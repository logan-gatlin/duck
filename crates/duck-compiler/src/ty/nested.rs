//! Functions declared in functions. One is a function as any other is, of
//! a type of its own, which the rest of its block names: the statement
//! that declares it binds its name to it, as a `let` would.
//!
//! Its body names the variables of the functions around it that are in
//! scope where it is declared, and captures each that it names: the
//! function holds a copy of it, as it is when the statement runs. So a
//! value of its type is as large as what it captures, laid out as a struct
//! of them in the order they are declared, and a call passes those before
//! what the function takes. One that captures nothing holds nothing, as a
//! function of the module does.
//!
//! Its body is lowered where it is declared, once for each instance of the
//! function around it, whose type parameters it names.

use crate::ir::{FuncId, LocalId};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, ExprKind, Pattern, PatternKind, StmtKind};

use super::inspect::visit::{self, Node};
use super::opaque::{OpaqueSite, Owner};
use super::{Body, Checker, Expr, FuncSig, OPEN_FUNCS, Stmt, Synth, Ty, TypeErrorKind, Value, Var};

/// What a function declared in a function is beyond its signature. It is
/// a closure if what it captures holds anything.
#[derive(Clone)]
pub(super) struct NestedFn {
    /// The name it is declared by, which its body names it by.
    name: String,
    /// The variables of the functions around it that its body names, in
    /// the order they are declared.
    captures: Vec<Capture>,
    /// The tuple of what it captures, which a value of its type is laid
    /// out as.
    held: Ty,
    /// The functions declared in those around it that are in scope where
    /// it is, each by its name and its type: its body names the type of
    /// each, whether or not it captures the function.
    fns: Vec<(String, Ty)>,
    /// The names of types that those around it bind and that are in scope
    /// where it is, each with its type: its body names them, and captures
    /// nothing by them.
    aliases: Vec<(String, Ty)>,
}

/// A variable that a function declared in a function captures.
#[derive(Clone)]
pub(super) struct Capture {
    /// The name it has in the function around, and in the body.
    pub(super) name: String,
    /// The type of the variable, and so of the copy.
    pub(super) ty: Ty,
    /// Whether it is a `var`, which the function has a copy of that it
    /// doesn't assign.
    var: bool,
    /// Whether a `fn` in a function declares it.
    func: bool,
}

/// The names that the body of a function declared in a function mentions
/// and doesn't bind, which are those of the functions around it.
#[derive(Default)]
struct Free<'p> {
    /// The names in scope that the function binds, innermost last.
    bound: Vec<&'p str>,
    /// Those found so far, in the order they are first mentioned.
    names: Vec<&'p str>,
}

impl<'p> Free<'p> {
    /// The names free in the function `decl`.
    fn of(decl: &'p parse::FnDecl) -> Vec<&'p str> {
        let mut free = Self::default();
        free.function(decl);
        free.names
    }

    /// Finds those of the function `decl`, whose body names it and what it
    /// takes. One declared here is free of what this one binds.
    fn function(&mut self, decl: &'p parse::FnDecl) {
        let outer = self.bound.len();
        self.bound.push(&decl.sig.name.name);
        let params = decl.sig.params.iter();
        self.bound
            .extend(params.map(|param| param.name.name.as_str()));
        self.block(&decl.body);
        self.bound.truncate(outer);
    }

    /// Finds those of `block`, whose names are bound until it ends.
    fn block(&mut self, block: &'p [parse::Stmt]) {
        let outer = self.bound.len();
        for stmt in block {
            self.stmt(stmt);
        }
        self.bound.truncate(outer);
    }

    /// Finds those of `block`, which names what `pattern` binds.
    fn binding(&mut self, pattern: &'p Pattern, block: &'p [parse::Stmt]) {
        let outer = self.bound.len();
        self.bind(pattern);
        self.block(block);
        self.bound.truncate(outer);
    }

    /// Finds those of `stmt`, and binds what it declares for the rest of
    /// its block.
    fn stmt(&mut self, stmt: &'p parse::Stmt) {
        match &stmt.kind {
            // A name is bound once its value is evaluated.
            StmtKind::Binding(binding) => {
                self.expr(&binding.value);
                self.bind(&binding.pattern);
            }
            StmtKind::Expr(expr) => self.expr(expr),
            StmtKind::If {
                cond,
                then_body,
                else_body,
            } => {
                self.expr(cond);
                self.block(then_body);
                self.block(else_body.as_deref().unwrap_or_default());
            }
            StmtKind::While { cond, body } => {
                self.expr(cond);
                self.block(body);
            }
            StmtKind::For { var, iter, body } => {
                self.expr(iter);
                self.bound.push(&var.name);
                self.block(body);
                self.bound.pop();
            }
            StmtKind::Match { value, arms } => {
                self.expr(value);
                for arm in arms {
                    self.binding(&arm.pattern, &arm.body);
                }
            }
            StmtKind::Defer(body) => self.block(body),
            StmtKind::Fn(decl) => {
                self.function(decl);
                self.bound.push(&decl.sig.name.name);
            }
            StmtKind::Pass => {}
        }
    }

    /// Brings the names that `pattern` binds into scope.
    fn bind(&mut self, pattern: &'p Pattern) {
        match &pattern.kind {
            PatternKind::Name(name) => self.bound.push(name),
            PatternKind::Tuple(elems) | PatternKind::Array(elems) => {
                for elem in elems {
                    self.bind(elem);
                }
            }
            PatternKind::Variant(_, holds) => {
                if let Some(holds) = holds {
                    self.bind(holds);
                }
            }
            PatternKind::Discard | PatternKind::Literal(_) => {}
        }
    }

    /// Finds those that `expr` names, wherever in it: nothing in an
    /// expression binds a name.
    fn expr(&mut self, expr: &'p parse::Expr) {
        visit::expr(expr, &mut |node| {
            if let Node::Expr(parse::Expr {
                kind: ExprKind::Name(name),
                ..
            }) = node
                && !self.bound.contains(&name.as_str())
                && !self.names.contains(&name.as_str())
            {
                self.names.push(name);
            }
        });
    }
}

impl Checker {
    /// The signature of function `id`.
    pub(super) fn sig(&self, id: FuncId) -> &FuncSig {
        match id.0.checked_sub(OPEN_FUNCS) {
            Some(open) => &self.open_funcs[open as usize],
            None => &self.funcs[id.0 as usize],
        }
    }

    /// What function `id` captures, if it is declared in a function, in the
    /// order a value of its type holds them.
    pub(super) fn captures(&self, id: FuncId) -> &[Capture] {
        match self.nested_fns.get(&id) {
            Some(nested) => &nested.captures,
            None => &[],
        }
    }

    /// The tuple that a value of the type of function `id` is laid out as,
    /// if the function is declared in a function: one of what it captures.
    pub(super) fn held(&self, id: FuncId) -> Option<Ty> {
        self.nested_fns.get(&id).map(|nested| nested.held)
    }

    /// Whether a value of type `ty` may hold anything: a type parameter
    /// stands for one that may, whatever it is given.
    fn holds_value(&self, ty: Ty) -> bool {
        match ty {
            Ty::Func(id) => self.is_closure(id),
            Ty::Enum(id) => self.holds_value(self.enum_ty(id)),
            Ty::Struct(_) if self.union_id(ty).is_some() => true,
            Ty::Struct(_) | Ty::Tuple(_) => {
                let mut members = self.members(ty).into_iter();
                members.any(|member| self.holds_value(member))
            }
            Ty::Type | Ty::Unit | Ty::Never | Ty::Error => false,
            Ty::Prim(_) | Ty::Ptr(_) | Ty::Array(_) | Ty::Fn(_) => true,
            // What stands for a type may stand for one that does.
            Ty::Param(_) | Ty::Opaque(_) => true,
        }
    }

    /// Whether function `id` is a closure: one that captures what a value
    /// of its type then holds, so that no pointer to the function alone
    /// calls it. One that captures only what holds nothing is none.
    pub(super) fn is_closure(&self, id: FuncId) -> bool {
        self.held_captures(id).next().is_some()
    }

    /// The captures of function `id` that a value of its type holds
    /// something of.
    fn held_captures(&self, id: FuncId) -> impl Iterator<Item = &Capture> {
        let captures = self.captures(id).iter();
        captures.filter(|capture| self.holds_value(capture.ty))
    }

    /// The type of a closure that a value of type `ty` holds, if it holds
    /// one: `ty` itself, or what a struct, a tuple or an enum of it holds.
    pub(super) fn closure_part(&self, ty: Ty) -> Option<Ty> {
        match ty {
            Ty::Func(id) => self.is_closure(id).then_some(ty),
            // What a result hides may be one, and is its own to know.
            Ty::Opaque(_) => Some(ty),
            Ty::Enum(id) => self.closure_part(self.enum_ty(id)),
            Ty::Struct(_) | Ty::Tuple(_) => {
                let mut members = self.members(ty).into_iter();
                members.find_map(|member| self.closure_part(member))
            }
            _ => None,
        }
    }

    /// The error for a `ty` that is no pointer because it is the type of a
    /// closure, if it is one.
    pub(super) fn no_pointer(&self, ty: Ty) -> Option<TypeErrorKind> {
        let Ty::Func(id) = ty else {
            return None;
        };
        let held = self.held_captures(id).map(|capture| capture.name.clone());
        let held: Vec<_> = held.collect();
        (!held.is_empty()).then(|| TypeErrorKind::ClosurePointer {
            name: self.ty_name(ty),
            captures: held,
        })
    }

    /// What a closure `id` captures, as an editor says it: each variable
    /// that a value of its type holds, and how many bytes they take, unless
    /// that is for a type argument to say. `None` if it is no closure.
    pub(super) fn captures_text(&self, id: FuncId) -> Option<String> {
        let held = self.held_captures(id);
        let held = held.map(|capture| format!("{}: {}", capture.name, self.ty_name(capture.ty)));
        let held: Vec<_> = held.collect();
        if held.is_empty() {
            return None;
        }
        let size = match self.held(id) {
            Some(held) if !self.has_param(held) => match self.layout(held).0 {
                1 => " (1 byte)".to_string(),
                size => format!(" ({size} bytes)"),
            },
            _ => String::new(),
        };
        Some(format!("captures {}{size}", held.join(", ")))
    }

    /// The function that the body of `parent` declares at `span`, and
    /// whether it is yet to be declared: it is then the next that
    /// [`Self::declare_nested`] declares. One in a generic function checked
    /// as declared is of no instance, so it is no function of the module.
    fn nested_at(&self, parent: Option<FuncId>, span: Span) -> (FuncId, bool) {
        match (self.nested.get(&(parent, span)), self.open) {
            (Some(id), _) => (*id, false),
            (None, true) => (FuncId(OPEN_FUNCS + self.open_funcs.len() as u32), true),
            (None, false) => (FuncId(self.funcs.len() as u32), true),
        }
    }

    /// Declares the function with signature `sig` that the body of `parent`
    /// declares at `span`, which is `nested` beyond that.
    fn declare_nested(
        &mut self,
        parent: Option<FuncId>,
        span: Span,
        sig: FuncSig,
        nested: NestedFn,
    ) {
        let (id, _) = self.nested_at(parent, span);
        match self.open {
            true => self.open_funcs.push(sig),
            false => {
                self.funcs.push(sig);
                self.synths.push(Synth::Nested);
            }
        }
        self.nested.insert((parent, span), id);
        self.nested_fns.insert(id, nested);
    }

    /// Lowers function `id`, which `decl` declares at `span` in the body of
    /// the function being lowered.
    fn lower_nested(&mut self, program: &Program, id: FuncId, decl: &parse::FnDecl, span: Span) {
        let sig = self.sig(id).clone();
        self.record_params(&decl.sig, &sig);
        self.lowering.insert(id);
        self.deps.push(Vec::new());
        let func = self.lower_body(program, Some(id), sig, &decl.body, span, Vec::new());
        let deps = self.deps.pop().unwrap_or_default();
        // What it names, the function that declares it does.
        if let Some(outer) = self.deps.last_mut() {
            outer.extend(&deps);
        }
        self.lowering.remove(&id);
        if id.0 < OPEN_FUNCS {
            self.func_deps.insert(id, deps);
            self.lowered.insert(id, func);
        }
    }
}

impl Body<'_> {
    /// Brings into scope what the body of function `id` names of those
    /// around it, if it is declared in one: each variable it captures,
    /// which it has a copy of, and itself, which holds them all.
    pub(super) fn bind_captures(&mut self, id: FuncId) {
        let Some(nested) = self.ck.nested_fns.get(&id).cloned() else {
            return;
        };
        self.fns = nested.fns;
        self.bind_aliases(nested.aliases);
        let mut held = Vec::new();
        for capture in nested.captures {
            let slots = self.alloc(&capture.name, capture.ty);
            held.extend(&slots);
            let var = Var {
                ty: capture.ty,
                mutable: false,
                captured: capture.var,
                func: capture.func,
                alias: false,
                order: 0,
                slots,
            };
            self.bind_var(&capture.name, var);
        }
        self.bind_fn(&nested.name, Ty::Func(id), held);
    }

    /// Binds `name` to a function declared in a function, a value of type
    /// `ty` that `slots` hold. Its name is its type where one is written.
    fn bind_fn(&mut self, name: &str, ty: Ty, slots: Vec<LocalId>) {
        let var = Var {
            ty,
            mutable: false,
            captured: false,
            func: ty != Ty::Error,
            alias: false,
            order: 0,
            slots,
        };
        self.bind_var(name, var);
    }

    /// What each name that the body binds and that is in scope is bound to:
    /// the innermost so named.
    pub(super) fn bound_in_scope(&self) -> Vec<(&String, &Var)> {
        let mut bound: Vec<(&String, &Var)> = Vec::new();
        for (name, var) in self.scopes.iter().rev().flatten() {
            if !bound.iter().any(|(seen, _)| *seen == name) {
                bound.push((name, var));
            }
        }
        bound
    }

    /// The functions that are declared in this one and in those around it,
    /// and that are in scope, each by its name and its type: those around
    /// it first, unless this one binds the name.
    fn fns_in_scope(&self) -> Vec<(String, Ty)> {
        let bound = self.bound_in_scope();
        let hidden = |name: &String| bound.iter().any(|(seen, _)| *seen == name);
        let around = self.fns.iter().filter(|(name, _)| !hidden(name));
        let fns = bound.iter().filter(|(_, var)| var.func);
        let fns = fns.map(|(name, var)| ((*name).clone(), var.ty));
        around.cloned().chain(fns).collect()
    }

    /// Resolves, with `resolve`, types written where each function in scope
    /// that is declared in a function names its type, as a function of the
    /// module does, and each name of a type that the body binds names its
    /// own.
    pub(super) fn naming_locals<T>(&mut self, resolve: impl FnOnce(&mut Checker) -> T) -> T {
        let outer = self.ck.type_params.len();
        let fns = self.fns_in_scope();
        self.ck.type_params.extend(fns);
        let aliases = self.aliases_in_scope();
        self.ck.type_params.extend(aliases);
        let resolved = resolve(self.ck);
        self.ck.type_params.truncate(outer);
        resolved
    }

    /// Whether `expr` is the name of a function declared in a function,
    /// which is its type where a type is written.
    pub(super) fn names_nested(&self, expr: &parse::Expr) -> bool {
        match &expr.kind {
            ExprKind::Name(name) => self.lookup(name).is_some_and(|var| var.func),
            _ => false,
        }
    }

    /// Resolves `ty`, written in the body.
    pub(super) fn resolve_ty(&mut self, ty: &parse::Type) -> Ty {
        self.naming_locals(|ck| ck.resolve_ty(ty))
    }

    /// What the function `decl` captures, declared here: each variable in
    /// scope that its body names, in the order they are declared.
    fn captured(&self, decl: &parse::FnDecl) -> Vec<Capture> {
        let named = Free::of(decl).into_iter();
        let mut captures: Vec<_> = named
            .filter_map(|name| self.lookup(name).map(|var| (name, var)))
            .collect();
        captures.sort_by_key(|(_, var)| var.order);
        let capture = |(name, var): (&str, &Var)| Capture {
            name: name.to_string(),
            ty: var.ty,
            var: var.mutable || var.captured,
            func: var.func,
        };
        captures.into_iter().map(capture).collect()
    }

    /// Declares the function `decl`, in the statement spanning `span`: lowers
    /// it, unless that is done, and binds its name to it, with a copy of
    /// each variable it captures.
    pub(super) fn nested_fn(&mut self, decl: &parse::FnDecl, span: Span, out: &mut Vec<Stmt>) {
        let name = &decl.sig.name;
        let own = || name.name.clone();
        if let Some(host) = &decl.export_name {
            self.error(TypeErrorKind::NestedHostName(own()), host.span);
        }
        let defaults = decl.sig.params.iter().filter_map(|p| p.default.as_ref());
        for default in defaults {
            self.error(TypeErrorKind::NestedDefault(own()), default.span);
        }
        let inferred = decl.sig.type_params.first().map(|param| param.name.span);
        let given = decl.sig.params.iter().find(|param| param.ty.is_type());
        if let Some(param) = inferred.or(given.map(|param| param.span)) {
            self.error(TypeErrorKind::NestedTypeParams(own()), param);
            self.bind_fn(&name.name, Ty::Error, Vec::new());
            return;
        }
        let (id, new) = self.ck.nested_at(self.func, span);
        if new {
            let func = format!("{}.{}", self.name, name.name);
            let site = OpaqueSite {
                owner: Owner::Func(id),
                func: func.clone(),
                is_pub: false,
                count: 0,
            };
            let (params, ret) = self.naming_locals(|ck| ck.resolve_sig(&decl.sig, Some(site)));
            let sig = FuncSig {
                name: func,
                params,
                defaults: Vec::new(),
                ret,
            };
            let captures = self.captured(decl);
            let nested = NestedFn {
                name: own(),
                held: (self.ck).tuple_of(captures.iter().map(|capture| capture.ty).collect()),
                captures,
                fns: self.fns_in_scope(),
                aliases: self.aliases_in_scope(),
            };
            self.ck.declare_nested(self.func, span, sig, nested);
            let program = self.program.expect("only a function has statements");
            self.ck.lower_nested(program, id, decl, span);
        }
        // A signature that failed to resolve is already reported.
        let (params, ret) = self.ck.func_shape(id);
        let failed = ret == Ty::Error || params.contains(&Ty::Error);
        let ty = match failed {
            true => Ty::Error,
            false => Ty::Func(id),
        };
        self.ck.record(name.span, ty);
        // A copy of each variable it captures, as it is now.
        let mut held = Vec::new();
        for capture in self.ck.captures(id).to_vec() {
            let var = self
                .lookup(&capture.name)
                .expect("in scope where it is declared");
            let reads = var.slots.iter().map(|slot| Expr::Local(*slot));
            held.push(self.scalars(capture.ty, reads.collect()));
        }
        let Value { pre, scalars } = self.seq(held);
        out.extend(pre);
        let slots = match failed {
            true => Vec::new(),
            false => self.alloc(&name.name, ty),
        };
        for (slot, (_, scalar)) in slots.iter().zip(scalars) {
            out.push(Stmt::SetLocal(*slot, scalar));
        }
        self.bind_fn(&name.name, ty, slots);
    }
}

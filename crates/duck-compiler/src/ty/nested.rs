//! Functions declared in functions. One is a function as any other is, of
//! a type of its own, which the rest of its block names: the statement
//! that declares it binds its name to it, as a `let` would.
//!
//! Its body is lowered where it is declared, once for each instance of the
//! function around it, whose type parameters it names. It names the
//! functions that are declared before it in those around it, and itself.

use crate::ir::FuncId;
use crate::lex::Span;
use crate::load::Program;
use crate::parse;

use super::{Body, Checker, FuncSig, OPEN_FUNCS, Synth, Ty, TypeErrorKind, Var};

/// What the body of a function declared in another names of those around
/// it: a function declared before it, or itself.
pub(super) struct Around {
    name: String,
    ty: Ty,
}

impl Checker {
    /// The signature of function `id`.
    pub(super) fn sig(&self, id: FuncId) -> &FuncSig {
        match id.0.checked_sub(OPEN_FUNCS) {
            Some(open) => &self.open_funcs[open as usize],
            None => &self.funcs[id.0 as usize],
        }
    }

    /// The function with signature `sig` that the body of `parent` declares
    /// at `span`, and whether this is the first it is asked for. One in a
    /// generic function checked as declared is of no instance, so it is no
    /// function of the module.
    fn nested_id(&mut self, parent: Option<FuncId>, span: Span, sig: FuncSig) -> (FuncId, bool) {
        if let Some(id) = self.nested.get(&(parent, span)) {
            return (*id, false);
        }
        let id = match self.open {
            true => {
                self.open_funcs.push(sig);
                FuncId(OPEN_FUNCS + self.open_funcs.len() as u32 - 1)
            }
            false => {
                self.funcs.push(sig);
                self.synths.push(Synth::Nested);
                FuncId(self.funcs.len() as u32 - 1)
            }
        };
        self.nested.insert((parent, span), id);
        (id, true)
    }

    /// Lowers function `id`, which `decl` declares at `span` in the body of
    /// the function being lowered, and whose body names each of `around`.
    fn lower_nested(
        &mut self,
        program: &Program,
        id: FuncId,
        decl: &parse::FnDecl,
        span: Span,
        around: &[Around],
    ) {
        let sig = self.sig(id).clone();
        self.record_params(&decl.sig, &sig);
        self.lowering.insert(id);
        self.deps.push(Vec::new());
        let func = self.lower_body(program, Some(id), around, sig, &decl.body, span, Vec::new());
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
    /// Brings `outer` into scope, which the body names.
    pub(super) fn bind_around(&mut self, outer: &Around) {
        let var = Var {
            ty: outer.ty,
            mutable: false,
            func: true,
            slots: Vec::new(),
        };
        self.bind_var(&outer.name, var);
    }

    /// The functions that are declared in this one and in those around it,
    /// and that are in scope.
    fn fns_in_scope(&self) -> Vec<Around> {
        let mut seen = Vec::new();
        let mut fns = Vec::new();
        for (name, var) in self.scopes.iter().rev().flatten() {
            if seen.contains(&name) {
                continue;
            }
            seen.push(name);
            if var.func {
                let (name, ty) = (name.clone(), var.ty);
                fns.push(Around { name, ty });
            }
        }
        fns
    }

    /// Resolves, with `resolve`, types written where each function in scope
    /// that is declared in a function names its type, as a function of the
    /// module does.
    pub(super) fn naming_fns<T>(&mut self, resolve: impl FnOnce(&mut Checker) -> T) -> T {
        let outer = self.ck.type_params.len();
        let fns = self.fns_in_scope().into_iter();
        self.ck.type_params.extend(fns.map(|f| (f.name, f.ty)));
        let resolved = resolve(self.ck);
        self.ck.type_params.truncate(outer);
        resolved
    }

    /// Whether `expr` is the name of a function declared in a function,
    /// which is its type where a type is written.
    pub(super) fn names_nested(&self, expr: &parse::Expr) -> bool {
        match &expr.kind {
            parse::ExprKind::Name(name) => self.lookup(name).is_some_and(|var| var.func),
            _ => false,
        }
    }

    /// Resolves `ty`, written in the body.
    pub(super) fn resolve_ty(&mut self, ty: &parse::Type) -> Ty {
        self.naming_fns(|ck| ck.resolve_ty(ty))
    }

    /// Declares the function `decl`, in the statement spanning `span`: lowers
    /// it, unless that is done, and binds its name to it.
    pub(super) fn nested_fn(&mut self, decl: &parse::FnDecl, span: Span) {
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
            self.bind(&name.name, Ty::Error, false, Vec::new());
            return;
        }
        let (params, ret) = self.naming_fns(|ck| ck.resolve_sig(&decl.sig));
        // A signature that failed to resolve is already reported.
        let failed = ret == Ty::Error || params.iter().any(|(_, ty)| *ty == Ty::Error);
        let sig = FuncSig {
            name: format!("{}.{}", self.name, name.name),
            params,
            defaults: Vec::new(),
            ret,
        };
        let (id, new) = self.ck.nested_id(self.func, span, sig);
        if new {
            let mut around = self.fns_in_scope();
            let (name, ty) = (own(), Ty::Func(id));
            around.push(Around { name, ty });
            let program = self.program.expect("only a function has statements");
            self.ck.lower_nested(program, id, decl, span, &around);
        }
        let ty = match failed {
            true => Ty::Error,
            false => Ty::Func(id),
        };
        self.ck.record(name.span, ty);
        let var = Var {
            ty,
            mutable: false,
            func: !failed,
            slots: Vec::new(),
        };
        self.bind_var(&name.name, var);
    }
}

//! Generic functions: resolving their signatures with type parameters,
//! inferring type arguments at calls, and lowering an instance per list of
//! type arguments.
//!
//! A generic function's body is checked once as declared, with its type
//! parameters standing for themselves. An error that no type argument avoids
//! is reported there. A statement that only some avoid, like `a + b` of a
//! type parameter, is a need of the function, and each instance is checked
//! against the needs alone before it is lowered. An error in a need is
//! reported at the call that led to the instance.

use std::collections::HashMap;
use std::mem;
use std::rc::Rc;

use crate::ir::{self, FuncId};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, Arg};

use super::generic::Arity;
use super::{
    Body, Checker, DefaultValue, FuncSig, GenericFnId, Item, Synth, Ty, TypeErrorKind, Value,
    generic_fn_decls, is_typed_by_other, path_text, pending_defaults,
};

/// The most instances of generic functions that can be nested, each
/// instantiated while lowering the last.
pub(super) const MAX_INSTANCE_DEPTH: usize = 64;

/// The most parts the type arguments of an instance can have, counting each
/// type and those within it, as written out.
pub(super) const MAX_INSTANCE_SIZE: u64 = 4096;

/// A generic function's declaration.
pub(super) struct GenericFn {
    /// The [`Ty::Param`] of each type parameter.
    params: Vec<Ty>,
    /// The signature, in terms of the type parameters.
    sig: FuncSig,
    /// What its body needs of its type arguments. Empty until the body is
    /// checked as declared.
    needs: Rc<Needs>,
    /// Whether its declaration has an error, which its instances share.
    failed: bool,
}

/// An instance of a generic function, waiting to be lowered.
#[derive(Clone)]
pub(super) struct FnInstance {
    generic: GenericFnId,
    args: Vec<Ty>,
    /// The instance and those whose calls led to it, innermost first.
    chain: Vec<InstanceCall>,
}

/// An instance of a generic function, and the call that first used it.
#[derive(Clone)]
pub(super) struct InstanceCall {
    /// The instance as written, such as `id(i32)`.
    pub(super) name: String,
    pub(super) call: Span,
}

/// What the statements of a generic function's body need of its type
/// arguments, by where each starts.
#[derive(Default)]
pub(super) struct Needs {
    stmts: HashMap<usize, Need>,
}

/// What a statement in the body of a generic function needs of its type
/// arguments. That of an `if` or `while` is its condition's, that of a `for`
/// is its array's, and that of a `match` is its value's and its patterns':
/// the statements within have their own.
#[derive(Clone, Copy)]
pub(super) enum Need {
    /// Something that not every type has, so it's checked for each instance.
    Check,
    /// Nothing, but it's a `let`, `var`, `for` or `match` that binds names
    /// in a value of this type, which may hold type parameters.
    Bind(Ty),
    /// Nothing.
    Skip,
}

impl Needs {
    pub(super) fn of(&self, stmt: &parse::Stmt) -> Need {
        let need = self.stmts.get(&stmt.span.start);
        need.copied().unwrap_or(Need::Skip)
    }

    pub(super) fn set(&mut self, stmt: &parse::Stmt, need: Need) {
        self.stmts.insert(stmt.span.start, need);
    }
}

impl Checker {
    /// Declares generic function `decl`.
    pub(super) fn declare_generic_fn(&mut self, decl: &parse::FnDecl) -> GenericFnId {
        let params = self.new_params(&decl.sig.type_params);
        self.generic_fns.push(GenericFn {
            params,
            sig: FuncSig {
                name: decl.sig.name.name.clone(),
                params: Vec::new(),
                defaults: Vec::new(),
                ret: Ty::Unit,
            },
            needs: Rc::default(),
            failed: false,
        });
        GenericFnId(self.generic_fns.len() as u32 - 1)
    }

    /// Resolves the signature of every generic function.
    pub(super) fn define_generic_fns(&mut self, program: &Program) {
        for (i, (item, decl)) in generic_fn_decls(program).enumerate() {
            self.module = item.span.file;
            let errors = self.errors.len();
            let params = self.generic_fns[i].params.clone();
            self.declare_type_params(&decl.sig.type_params, &params);
            let (params, ret) = self.resolve_sig(&decl.sig);
            if item.is_pub {
                self.check_public_sig(&decl.sig, &params, ret);
            }
            self.type_params.clear();
            let def = &mut self.generic_fns[i];
            def.sig.params = params;
            def.sig.defaults = pending_defaults(&decl.sig);
            def.sig.ret = ret;
            def.failed = self.errors.len() > errors;
        }
    }

    /// Checks and folds the defaults of every generic function's parameters,
    /// which each instance shares.
    pub(super) fn define_generic_fn_defaults(&mut self, program: &Program) {
        for (i, (item, decl)) in generic_fn_decls(program).enumerate() {
            self.module = item.span.file;
            let params = self.generic_fns[i].sig.params.clone();
            let defaults = self.fold_param_defaults(program, &decl.sig, &params);
            self.generic_fns[i].sig.defaults = defaults;
        }
    }

    /// Checks the body of every generic function as declared, with its type
    /// parameters standing for themselves, and records what each needs of
    /// its type arguments. What is lowered is of no instance, and is dropped.
    pub(super) fn check_generic_fns(&mut self, program: &Program) {
        for (i, (item, decl)) in generic_fn_decls(program).enumerate() {
            self.module = item.span.file;
            let def = &self.generic_fns[i];
            let (params, sig) = (def.params.clone(), def.sig.clone());
            let names = decl.sig.type_params.iter().map(|p| p.name.clone());
            self.type_params = names.zip(params).collect();
            let errors = self.errors.len();
            self.open = true;
            self.deferred = false;
            let (_, needs) = self.walk_body(sig, &decl.body, item.span, None, None);
            self.open = false;
            self.type_params.clear();
            let def = &mut self.generic_fns[i];
            def.needs = Rc::new(needs);
            def.failed |= self.errors.len() > errors;
        }
    }

    /// The instance of generic function `generic` with type arguments
    /// `args`, first called at `call`. `None` if an argument is the error
    /// type, or after reporting an instance too deep or large to create, or
    /// whose signature points to something memory can't hold.
    fn instantiate_fn(
        &mut self,
        generic: GenericFnId,
        args: Vec<Ty>,
        call: Span,
    ) -> Option<FuncId> {
        if args.contains(&Ty::Error) {
            return None;
        }
        if let Some(id) = self.fn_instances.get(&(generic, args.clone())) {
            return Some(*id);
        }
        if self.instance_chain.len() >= MAX_INSTANCE_DEPTH {
            let name = self.generic_fns[generic.0 as usize].sig.name.clone();
            self.error(TypeErrorKind::InstanceTooDeep(name), call);
            return None;
        }
        let sig = self.instance_sig(generic, &args, call)?;
        let mut chain = vec![InstanceCall {
            name: sig.name.clone(),
            call,
        }];
        chain.extend(self.instance_chain.iter().cloned());
        let id = FuncId(self.funcs.len() as u32);
        self.funcs.push(sig);
        self.synths.push(Synth::Instance(FnInstance {
            generic,
            args: args.clone(),
            chain,
        }));
        self.fn_instances.insert((generic, args), id);
        Some(id)
    }

    /// The signature of the instance of generic function `generic` with type
    /// arguments `args`, named as the instance is written. `None` after
    /// reporting, at `call`, type arguments too large for an instance, or a
    /// signature that points to something memory can't hold.
    fn instance_sig(&mut self, generic: GenericFnId, args: &[Ty], call: Span) -> Option<FuncSig> {
        let sig = self.generic_fns[generic.0 as usize].sig.clone();
        let mut sizes = HashMap::new();
        let size = args.iter().map(|arg| self.written_size(*arg, &mut sizes));
        if size.fold(0, u64::saturating_add) > MAX_INSTANCE_SIZE {
            self.error(TypeErrorKind::InstanceTooLarge(sig.name), call);
            return None;
        }
        let names: Vec<_> = args.iter().map(|arg| self.ty_name(*arg)).collect();
        let name = format!("{}({})", sig.name, names.join(", "));
        let params: Vec<_> = sig
            .params
            .into_iter()
            .map(|(param, ty)| (param, self.substitute(ty, args, call)))
            .collect();
        let ret = self.substitute(sig.ret, args, call);
        let tys = params.iter().map(|(_, ty)| *ty).chain([ret]);
        if let Some(pointee) = tys.into_iter().find_map(|ty| self.unstorable_pointee(ty)) {
            self.error(TypeErrorKind::NotStorable(self.ty_name(pointee)), call);
            return None;
        }
        // A call takes the defaults of the declaration it names.
        Some(FuncSig {
            name,
            params,
            defaults: Vec::new(),
            ret,
        })
    }

    /// The signature of generic function `generic` with type arguments
    /// `args`, as a call at `call` in a generic function checked as declared
    /// uses it. Each instance of that function has its own instance of this
    /// one, whose needs its type arguments may not meet, so the call is a
    /// need. `None` as [`Self::instantiate_fn`] is.
    fn open_instance(&mut self, generic: GenericFnId, args: &[Ty], call: Span) -> Option<FuncSig> {
        if args.contains(&Ty::Error) {
            return None;
        }
        self.deferred = true;
        self.instance_sig(generic, args, call)
    }

    /// Lowers function `id`, an instance of a generic function, once its
    /// type arguments are found to meet the needs of its declaration. They
    /// are all that can be wrong with it, so an error in lowering it is one
    /// that checking the declaration missed.
    pub(super) fn lower_instance(
        &mut self,
        program: &Program,
        id: FuncId,
        instance: FnInstance,
    ) -> ir::Func {
        let (item, decl) = generic_fn_decls(program)
            .nth(instance.generic.0 as usize)
            .unwrap();
        self.module = item.span.file;
        let names = decl.sig.type_params.iter().map(|p| p.name.clone());
        self.type_params = names.zip(instance.args).collect();
        self.instance_chain = instance.chain;
        let sig = self.funcs[id.0 as usize].clone();
        let def = &self.generic_fns[instance.generic.0 as usize];
        // A declaration with an error has it in every instance, where it
        // isn't a need.
        let needs = (!def.failed).then(|| def.needs.clone());
        let errors = self.errors.len();
        if let Some(needs) = needs {
            self.walk_body(sig.clone(), &decl.body, item.span, None, Some(needs));
        }
        let func = if self.errors.len() > errors {
            ir::Func {
                export: None,
                name: sig.name,
                params: Vec::new(),
                results: Vec::new(),
                locals: Vec::new(),
                body: Vec::new(),
            }
        } else {
            let func = self.lower_body(sig, &decl.body, item.span, None);
            for error in &mut self.errors[errors..] {
                // Where in the body it is, which the last instance holds.
                let Some(site) = error.instances.pop() else {
                    continue;
                };
                let kind = mem::replace(&mut error.kind, TypeErrorKind::NotAType);
                error.kind = TypeErrorKind::Unchecked {
                    instance: site.name,
                    error: Box::new(kind),
                };
                error.span = Some(site.span);
                error.instances.clear();
            }
            func
        };
        self.type_params.clear();
        self.instance_chain.clear();
        func
    }

    /// Binds each type parameter in `pattern`, a parameter type of a generic
    /// function, to the part of `actual`, its argument's type, in the same
    /// place. Parameters already in `bound` keep their type. An argument of
    /// the error type binds every parameter in `pattern` to it, since it
    /// already failed to check.
    fn unify(&self, pattern: Ty, actual: Ty, bound: &mut [Option<Ty>]) {
        match (pattern, actual) {
            (Ty::Param(id), _) => {
                let slot = &mut bound[self.params[id.0 as usize].index];
                slot.get_or_insert(actual);
            }
            (_, Ty::Error) => {
                for part in self.written_parts(pattern) {
                    self.unify(part, Ty::Error, bound);
                }
            }
            (Ty::Struct(p), Ty::Struct(a)) => {
                let p = &self.structs[p.0 as usize].instance;
                let a = &self.structs[a.0 as usize].instance;
                if let (Some(p), Some(a)) = (p, a)
                    && p.generic == a.generic
                {
                    for (p, a) in p.args.iter().zip(&a.args) {
                        self.unify(*p, *a, bound);
                    }
                }
            }
            (Ty::Ptr(_), Ty::Ptr(_))
            | (Ty::Tuple(_), Ty::Tuple(_))
            | (Ty::Array(_), Ty::Array(_))
            | (Ty::Fn(_), Ty::Fn(_)) => {
                let (p, a) = (self.components(pattern), self.components(actual));
                if p.len() == a.len() {
                    for (p, a) in p.into_iter().zip(a) {
                        self.unify(p, a, bound);
                    }
                }
            }
            _ => {}
        }
    }

    /// How many types `ty` is written with, counting itself and each type
    /// within it wherever it's written. Memoized in `sizes`, since types that
    /// hold the same type many times over are written exponentially long.
    fn written_size(&self, ty: Ty, sizes: &mut HashMap<Ty, u64>) -> u64 {
        if let Some(size) = sizes.get(&ty) {
            return *size;
        }
        let size = self
            .written_parts(ty)
            .into_iter()
            .map(|part| self.written_size(part, sizes))
            .fold(1, u64::saturating_add);
        sizes.insert(ty, size);
        size
    }

    /// Whether `ty` holds a type parameter not yet in `bound`.
    fn has_unbound(&self, ty: Ty, bound: &[Option<Ty>]) -> bool {
        match ty {
            Ty::Param(id) => bound[self.params[id.0 as usize].index].is_none(),
            _ => self
                .written_parts(ty)
                .into_iter()
                .any(|part| self.has_unbound(part, bound)),
        }
    }

    /// Whether `ty` is the type parameter `param`, or holds it anywhere
    /// within it.
    pub(super) fn holds(&self, ty: Ty, param: Ty) -> bool {
        let mut parts = self.written_parts(ty).into_iter();
        ty == param || parts.any(|part| self.holds(part, param))
    }

    /// The types `ty` is written with: the type arguments of an instance of
    /// a generic struct, or else its components.
    fn written_parts(&self, ty: Ty) -> Vec<Ty> {
        match ty {
            Ty::Struct(id) => match &self.structs[id.0 as usize].instance {
                Some(instance) => instance.args.clone(),
                None => Vec::new(),
            },
            _ => self.components(ty),
        }
    }
}

impl Body<'_> {
    /// A call of generic function `generic` spanning `span`, given type
    /// arguments `explicit`, or else inferring them from `args`.
    pub(super) fn generic_fn_call(
        &mut self,
        generic: GenericFnId,
        explicit: Option<Vec<Ty>>,
        args: &[Arg],
        span: Span,
    ) -> (Ty, Value) {
        let sig = self.ck.generic_fns[generic.0 as usize].sig.clone();
        let binding = self.bind_args(&sig.params, &sig.defaults, args, false, span);
        let mut checked: Vec<_> = args.iter().map(|_| None).collect();
        let type_args = match explicit {
            Some(type_args) => type_args,
            None => self.infer_type_args(generic, args, &binding, &mut checked, span),
        };
        // A generic function checked as declared calls no instance.
        let id = match self.ck.open {
            true => None,
            false => self.ck.instantiate_fn(generic, type_args.clone(), span),
        };
        let instance = match id {
            Some(id) => Some(self.ck.funcs[id.0 as usize].clone()),
            None if self.ck.open => self.ck.open_instance(generic, &type_args, span),
            None => None,
        };
        let Some(instance) = instance else {
            let params: Vec<_> = sig
                .params
                .iter()
                .map(|(p, _)| (p.clone(), Ty::Error))
                .collect();
            self.bound_args(&params, &sig.defaults, args, binding, checked);
            return (Ty::Error, Value::default());
        };
        let value = self.bound_args(&instance.params, &sig.defaults, args, binding, checked);
        match id {
            Some(id) => self.call_func(id, value),
            None => (instance.ret, self.blank(instance.ret)),
        }
    }

    /// A pointer to the instance of generic function `generic`, named at
    /// `span`, that has the function type `expected`. Nothing else gives
    /// its type parameters their types.
    pub(super) fn generic_fn_value(
        &mut self,
        generic: GenericFnId,
        expected: Option<Ty>,
        span: Span,
    ) -> (Ty, Value) {
        let def = &self.ck.generic_fns[generic.0 as usize];
        let (func, type_params) = (def.sig.name.clone(), def.params.clone());
        let (params, ret) = (def.sig.params.iter().map(|(_, ty)| *ty), def.sig.ret);
        let params: Vec<_> = params.collect();
        // A signature or expected type that failed to resolve is already
        // reported.
        if params.contains(&Ty::Error) || ret == Ty::Error || expected == Some(Ty::Error) {
            return (Ty::Error, Value::default());
        }
        // A function type, for some type arguments.
        if let Some(param @ Ty::Param(_)) = expected {
            self.ck.deferred = true;
            return (param, Value::default());
        }
        let mut bound = vec![None; type_params.len()];
        if let Some(expected @ Ty::Fn(_)) = expected {
            let pattern = self.ck.fn_of(params, ret);
            self.ck.unify(pattern, expected, &mut bound);
        }
        for (param, ty) in type_params.iter().zip(&bound) {
            if ty.is_none() {
                let (func, param) = (func.clone(), self.ck.param_name(*param));
                self.error(TypeErrorKind::CannotInfer { func, param }, span);
            }
        }
        let Some(type_args): Option<Vec<Ty>> = bound.into_iter().collect() else {
            return (Ty::Error, Value::default());
        };
        if self.ck.open {
            let Some(instance) = self.ck.open_instance(generic, &type_args, span) else {
                return (Ty::Error, Value::default());
            };
            let params = instance.params.into_iter().map(|(_, ty)| ty).collect();
            let ty = self.ck.fn_of(params, instance.ret);
            return (ty, self.blank(ty));
        }
        // Otherwise only the default of a generic struct's field is expected
        // to have a type that holds a type parameter.
        let mut held = type_args.iter();
        if let Some(param) = held.find_map(|arg| self.ck.held_param(*arg, false)) {
            let kind = TypeErrorKind::DefaultUsesParam(self.ck.param_name(param));
            self.error(kind, span);
            return (Ty::Error, Value::default());
        }
        match self.ck.instantiate_fn(generic, type_args, span) {
            Some(id) => self.func_value(id),
            None => (Ty::Error, Value::default()),
        }
    }

    /// Whether `expr(args)` gives a function its type arguments, rather
    /// than calling one whose result is then called. A generic function
    /// always takes type arguments; any other is taken to unless it returns
    /// a function pointer, so that giving it some is reported.
    pub(super) fn names_fn(&self, expr: &parse::Expr) -> bool {
        match self.named(expr) {
            Some(Item::GenericFn(_)) => true,
            Some(Item::Func(id)) => !matches!(self.ck.funcs[id.0 as usize].ret, Ty::Fn(_)),
            _ => false,
        }
    }

    /// `callee(args)`, where `callee` is the function `func` names given
    /// type arguments, as in `id(u8)`.
    pub(super) fn explicit_call(
        &mut self,
        callee: &parse::Expr,
        func: &parse::Expr,
        type_args: &[Arg],
        args: &[Arg],
        span: Span,
    ) -> (Ty, Value) {
        let name = path_text(func);
        let type_args = self.ck.type_args(type_args);
        let generic = match self.named(func) {
            Some(Item::GenericFn(generic)) => Some(generic),
            _ => {
                self.error(TypeErrorKind::NotGeneric(name.clone()), callee.span);
                None
            }
        };
        if let (Some(generic), Some(type_args)) = (generic, type_args) {
            let arity = Arity::Exactly(self.ck.generic_fns[generic.0 as usize].params.len());
            match arity.check(&name, Some(type_args.len())) {
                Some(kind) => self.error(kind, callee.span),
                None => return self.generic_fn_call(generic, Some(type_args), args, span),
            }
        }
        for arg in args {
            self.expr(&arg.value, None);
        }
        (Ty::Error, Value::default())
    }

    /// Infers the type arguments of a call of generic function `generic`
    /// from the `args` that `binding` matches with its parameters. Arguments
    /// that aren't literals or `.name`s go first, so that those take the
    /// types they settle, and those naming generic functions are left for
    /// last. Those it checks are kept in `checked`. Type parameters that no
    /// argument settles are reported at `span`, and given the error type.
    fn infer_type_args(
        &mut self,
        generic: GenericFnId,
        args: &[Arg],
        binding: &[Option<usize>],
        checked: &mut [Option<(Ty, Value)>],
        span: Span,
    ) -> Vec<Ty> {
        let def = &self.ck.generic_fns[generic.0 as usize];
        let patterns: Vec<_> = def.sig.params.iter().map(|(_, ty)| *ty).collect();
        let mut bound = vec![None; def.params.len()];
        for literals in [false, true] {
            for (k, (arg, param)) in args.iter().zip(binding).enumerate() {
                let Some(i) = *param else {
                    continue;
                };
                // A generic function's instance is picked by its parameter's
                // type, so it settles nothing.
                let generic = matches!(self.named(&arg.value), Some(Item::GenericFn(_)));
                if generic
                    || is_typed_by_other(&arg.value) != literals
                    || !self.ck.has_unbound(patterns[i], &bound)
                {
                    continue;
                }
                let (ty, value) = self.expr(&arg.value, None);
                self.ck.unify(patterns[i], ty, &mut bound);
                checked[k] = Some((ty, value));
            }
        }
        // Missing arguments, and signatures and defaults that failed to
        // resolve, are already reported. A default that didn't fail settles
        // nothing.
        let sig = &self.ck.generic_fns[generic.0 as usize].sig;
        if sig.params.iter().any(|(_, ty)| *ty == Ty::Error) || sig.ret == Ty::Error {
            bound.fill(Some(Ty::Error));
        }
        let defaults = sig.defaults.clone();
        for (i, pattern) in patterns.into_iter().enumerate() {
            let defaulted = matches!(
                defaults.get(i),
                Some(Some(DefaultValue::Pending | DefaultValue::Folded(_)))
            );
            if !defaulted && !binding.contains(&Some(i)) {
                self.ck.unify(pattern, Ty::Error, &mut bound);
            }
        }
        let def = &self.ck.generic_fns[generic.0 as usize];
        let func = def.sig.name.clone();
        let unbound: Vec<_> = (def.params.iter().zip(&bound))
            .filter(|(_, ty)| ty.is_none())
            .map(|(param, _)| self.ck.param_name(*param))
            .collect();
        // A type parameter in an argument's type may be given a type that
        // settles them.
        let mut tys = checked.iter().flatten().map(|(ty, _)| *ty);
        if self.ck.open && !unbound.is_empty() && tys.any(|ty| self.ck.has_param(ty)) {
            self.ck.deferred = true;
            return vec![Ty::Error; bound.len()];
        }
        for param in unbound {
            let func = func.clone();
            self.error(TypeErrorKind::CannotInfer { func, param }, span);
        }
        bound
            .into_iter()
            .map(|ty| ty.unwrap_or(Ty::Error))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::{DummyManager, FileManager, Settings};
    use crate::lex::tokenize;

    #[test]
    fn errors_that_a_declarations_needs_miss_are_internal() {
        let src = "\
fn(T) add(a: T, b: T) -> T:
    return a + b
fn f():
    add(true, false)
";
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let mut ck = Checker::define(&program, &Settings::default(), None);
        ck.check_generic_fns(&program);
        assert!(ck.errors.is_empty());
        // As if checking `add` as declared had found nothing it needs.
        ck.generic_fns[0].needs = Rc::default();
        ck.lower_funcs(&program);
        ck.lower_synths(&program);
        let [error] = &ck.errors[..] else {
            panic!("expected one error: {:#?}", ck.errors);
        };
        let operand = TypeErrorKind::InvalidOperand {
            op: "+",
            ty: "bool".to_string(),
        };
        let unchecked = TypeErrorKind::Unchecked {
            instance: "add(bool)".to_string(),
            error: Box::new(operand),
        };
        assert_eq!(error.kind, unchecked);
        let span = error.span.unwrap();
        assert_eq!(&src[span.start..span.end], "a + b");
        assert!(error.instances.is_empty());
    }
}

//! Generic functions: resolving their signatures with type parameters,
//! inferring type arguments at calls, and lowering an instance per list of
//! type arguments. Each instance's body is checked on its own, with its type
//! parameters naming its type arguments.

use std::collections::HashMap;

use crate::ir::{self, FuncId};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, Arg};

use super::generic::Arity;
use super::{
    Body, Checker, FuncSig, GenericFnId, InstanceSite, Item, Synth, Ty, TypeErrorKind, Value,
    generic_fn_decls, is_literal, path_text,
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
}

/// An instance of a generic function, waiting to be lowered.
#[derive(Clone)]
pub(super) struct FnInstance {
    generic: GenericFnId,
    args: Vec<Ty>,
    /// The instance and those whose calls led to it, innermost first.
    chain: Vec<InstanceSite>,
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
                ret: Ty::Unit,
            },
        });
        GenericFnId(self.generic_fns.len() as u32 - 1)
    }

    /// Resolves the signature of every generic function.
    pub(super) fn define_generic_fns(&mut self, program: &Program) {
        for (i, (item, decl)) in generic_fn_decls(program).enumerate() {
            self.module = item.span.file;
            let params = self.generic_fns[i].params.clone();
            self.declare_type_params(&decl.sig.type_params, &params);
            let (params, ret) = self.resolve_sig(&decl.sig);
            if item.is_pub {
                self.check_public_sig(&decl.sig, &params, ret);
            }
            self.type_params.clear();
            let sig = &mut self.generic_fns[i].sig;
            sig.params = params;
            sig.ret = ret;
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
        let sig = self.generic_fns[generic.0 as usize].sig.clone();
        let mut sizes = HashMap::new();
        let size = args.iter().map(|arg| self.written_size(*arg, &mut sizes));
        if size.fold(0, u64::saturating_add) > MAX_INSTANCE_SIZE {
            self.error(TypeErrorKind::InstanceTooLarge(sig.name), call);
            return None;
        }
        if self.instance_chain.len() >= MAX_INSTANCE_DEPTH {
            self.error(TypeErrorKind::InstanceTooDeep(sig.name), call);
            return None;
        }
        let names: Vec<_> = args.iter().map(|arg| self.ty_name(*arg)).collect();
        let name = format!("{}({})", sig.name, names.join(", "));
        let mut chain = vec![InstanceSite {
            name: name.clone(),
            call,
        }];
        chain.extend(self.instance_chain.iter().cloned());
        let params: Vec<_> = sig
            .params
            .into_iter()
            .map(|(param, ty)| (param, self.substitute(ty, &args, call)))
            .collect();
        let ret = self.substitute(sig.ret, &args, call);
        let tys = params.iter().map(|(_, ty)| *ty).chain([ret]);
        if let Some(pointee) = tys.into_iter().find_map(|ty| self.unstorable_pointee(ty)) {
            self.error(TypeErrorKind::NotStorable(self.ty_name(pointee)), call);
            return None;
        }
        let id = FuncId(self.funcs.len() as u32);
        self.funcs.push(FuncSig { name, params, ret });
        self.synths.push(Synth::Instance(FnInstance {
            generic,
            args: args.clone(),
            chain,
        }));
        self.fn_instances.insert((generic, args), id);
        Some(id)
    }

    /// Lowers function `id`, an instance of a generic function.
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
        let func = self.lower_body(sig, &decl.body, item.span, None);
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
        let binding = self.bind_args(&sig.params, args, false, span);
        let mut checked: Vec<_> = args.iter().map(|_| None).collect();
        let type_args = match explicit {
            Some(type_args) => type_args,
            None => self.infer_type_args(generic, args, &binding, &mut checked, span),
        };
        let Some(id) = self.ck.instantiate_fn(generic, type_args, span) else {
            let params: Vec<_> = sig
                .params
                .iter()
                .map(|(p, _)| (p.clone(), Ty::Error))
                .collect();
            self.bound_args(&params, args, binding, checked);
            return (Ty::Error, Value::default());
        };
        let params = self.ck.funcs[id.0 as usize].params.clone();
        let value = self.bound_args(&params, args, binding, checked);
        self.call_func(id, value)
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
        // Only the default of a generic struct's field is expected to have
        // a type that holds a type parameter.
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
    /// that aren't literals go first, so that literals take the types they
    /// settle, and those naming generic functions are left for last. Those it checks are kept in `checked`. Type parameters that
    /// no argument settles are reported at `span`, and given the error type.
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
                    || is_literal(&arg.value) != literals
                    || !self.ck.has_unbound(patterns[i], &bound)
                {
                    continue;
                }
                let (ty, value) = self.expr(&arg.value, None);
                self.ck.unify(patterns[i], ty, &mut bound);
                checked[k] = Some((ty, value));
            }
        }
        // Missing arguments, and signatures that failed to resolve, are
        // already reported.
        let sig = &self.ck.generic_fns[generic.0 as usize].sig;
        if sig.params.iter().any(|(_, ty)| *ty == Ty::Error) || sig.ret == Ty::Error {
            bound.fill(Some(Ty::Error));
        }
        for (i, pattern) in patterns.into_iter().enumerate() {
            if !binding.contains(&Some(i)) {
                self.ck.unify(pattern, Ty::Error, &mut bound);
            }
        }
        let def = &self.ck.generic_fns[generic.0 as usize];
        let func = def.sig.name.clone();
        let unbound: Vec<_> = (def.params.iter().zip(&bound))
            .filter(|(_, ty)| ty.is_none())
            .map(|(param, _)| self.ck.param_name(*param))
            .collect();
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

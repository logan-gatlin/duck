//! Generic functions: resolving their signatures with type parameters,
//! finding type arguments at calls, and lowering an instance per list of
//! type arguments.
//!
//! A type parameter in the `(T)` after `fn` is inferred from the arguments
//! of each call. A parameter of type `type` is a type parameter too, which
//! each call gives a type as its argument: `fn zero(T: type) -> &T` is
//! called as `zero(u8)`.
//!
//! A generic function's body is checked once as declared, with its type
//! parameters standing for themselves: types of which only the size and
//! alignment are known. So what is right there is right for every list of
//! type arguments, and an instance is lowered without being checked again.

use std::collections::HashMap;
use std::mem;

use crate::ir::{self, FuncId};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, Arg, FnSig};

use super::{
    Body, Checker, DefaultValue, FuncSig, GenericFnId, Item, Synth, Ty, TypeErrorKind, Value,
    generic_fn_decls, is_typed_by_other, never, pending_defaults,
};

/// The most instances of generic functions that can be nested, each
/// instantiated while lowering the last.
pub(super) const MAX_INSTANCE_DEPTH: usize = 64;

/// The most parts the type arguments of an instance can have, counting each
/// type and those within it, as written out.
pub(super) const MAX_INSTANCE_SIZE: u64 = 4096;

/// A generic function's declaration.
pub(super) struct GenericFn {
    /// The [`Ty::Param`] of each type parameter: those a call infers, then
    /// those it gives a type.
    params: Vec<Ty>,
    /// The signature, in terms of the type parameters. A parameter that is
    /// one of them is a [`Ty::Type`].
    sig: FuncSig,
    /// Which of `params` each parameter of `sig` is, if it's a type
    /// parameter.
    given: Vec<Option<usize>>,
    /// The type of each parameter's default that has one of its own, which
    /// settles the type parameters in the parameter's type for a call that
    /// leaves the argument out. Empty until the defaults are folded.
    default_tys: Vec<Option<Ty>>,
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

impl Checker {
    /// Declares generic function `decl`.
    pub(super) fn declare_generic_fn(&mut self, decl: &parse::FnDecl) -> GenericFnId {
        let params = self.new_params(&decl.sig.type_param_names());
        self.generic_fns.push(GenericFn {
            params,
            given: Vec::new(),
            default_tys: Vec::new(),
            sig: FuncSig {
                name: decl.sig.name.name.clone(),
                params: Vec::new(),
                defaults: Vec::new(),
                ret: Ty::Unit,
            },
            failed: false,
        });
        GenericFnId(self.generic_fns.len() as u32 - 1)
    }

    /// Resolves the signature of every generic function.
    pub(super) fn define_generic_fns(&mut self, program: &Program) {
        for (i, (item, decl)) in generic_fn_decls(program).enumerate() {
            self.module = item.span.file;
            let errors = self.errors.len();
            let tys = self.generic_fns[i].params.clone();
            self.declare_type_params(&decl.sig.type_param_names(), &tys);
            self.resolve_bounds(&decl.sig.type_params, &tys);
            let (params, ret) = self.resolve_sig(&decl.sig);
            if item.is_pub {
                self.check_public_sig(&decl.sig, &params, ret);
            }
            // One that isn't in scope is already reported.
            let inferred = decl.sig.type_params.iter().zip(&tys);
            let inferred: Vec<_> = inferred
                .filter(|(param, ty)| self.type_param(&param.name.name) == Some(**ty))
                .collect();
            self.type_params.clear();
            let mut next = decl.sig.type_params.len();
            let mut given = Vec::new();
            for param in &decl.sig.params {
                given.push(param.ty.is_type().then_some(next));
                if !param.ty.is_type() {
                    continue;
                }
                next += 1;
                if param.default.is_some() {
                    let kind = TypeErrorKind::TypeParamDefault(param.name.name.clone());
                    self.error(kind, param.span);
                }
            }
            // A call infers the type parameters in the types of its
            // arguments, and from those the ones their bounds name.
            let mut settled: Vec<_> = tys
                .iter()
                .map(|ty| params.iter().any(|(_, held)| self.holds(*held, *ty)))
                .collect();
            for i in (0..tys.len()).rev() {
                let bound = match tys[i] {
                    Ty::Param(id) if settled[i] => self.params[id.0 as usize].bound,
                    _ => None,
                };
                for (j, ty) in tys.iter().enumerate() {
                    settled[j] |= bound.is_some_and(|bound| self.holds(bound, *ty));
                }
            }
            // A signature that failed to resolve is already reported.
            let resolved = params.iter().all(|(_, ty)| *ty != Ty::Error);
            for (param, ty) in inferred {
                let index = tys.iter().position(|other| other == ty);
                if resolved && !index.is_some_and(|index| settled[index]) {
                    let kind = TypeErrorKind::NeverInferred {
                        func: decl.sig.name.name.clone(),
                        param: param.name.name.clone(),
                    };
                    self.error(kind, param.name.span);
                }
            }
            let def = &mut self.generic_fns[i];
            def.given = given;
            def.sig.params = params;
            def.sig.defaults = pending_defaults(&decl.sig);
            def.sig.ret = ret;
            def.failed = self.errors.len() > errors;
        }
    }

    /// Checks and folds the defaults of the parameters of generic function
    /// `id`, which has the signature `sig`. Each instance shares them.
    pub(super) fn define_generic_fn_defaults(
        &mut self,
        program: &Program,
        id: GenericFnId,
        sig: &FnSig,
    ) {
        let def = &self.generic_fns[id.0 as usize];
        let (params, tys) = (def.sig.params.clone(), def.params.clone());
        let (defaults, own) = self.fold_param_defaults(program, sig, &params, &tys);
        let def = &mut self.generic_fns[id.0 as usize];
        def.sig.defaults = defaults;
        def.default_tys = own;
    }

    /// Checks the body of every generic function as declared, with its type
    /// parameters standing for themselves. What is lowered is of no
    /// instance, and is dropped.
    pub(super) fn check_generic_fns(&mut self, program: &Program) {
        for (i, (item, decl)) in generic_fn_decls(program).enumerate() {
            self.module = item.span.file;
            let def = &self.generic_fns[i];
            let (params, sig) = (def.params.clone(), def.sig.clone());
            let names = decl.sig.type_param_names().into_iter().map(|p| p.name);
            self.type_params = names.zip(params).collect();
            self.record_params(&decl.sig, &sig);
            let errors = self.errors.len();
            self.open = true;
            self.lower_body(program, sig, &decl.body, item.span, Vec::new());
            self.open = false;
            self.type_params.clear();
            self.generic_fns[i].failed |= self.errors.len() > errors;
        }
    }

    /// The instance of generic function `generic` with type arguments
    /// `args`, first called at `call`. `None` if an argument is the error
    /// type, or after reporting an instance too deep or large to create, or
    /// a type argument that memory can't hold.
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
    /// reporting, at `call`, type arguments too large for an instance, or one
    /// that memory can't hold.
    fn instance_sig(&mut self, generic: GenericFnId, args: &[Ty], call: Span) -> Option<FuncSig> {
        let sig = self.generic_fns[generic.0 as usize].sig.clone();
        let mut sizes = HashMap::new();
        let size = args.iter().map(|arg| self.written_size(*arg, &mut sizes));
        if size.fold(0, u64::saturating_add) > MAX_INSTANCE_SIZE {
            self.error(TypeErrorKind::InstanceTooLarge(sig.name), call);
            return None;
        }
        // The body may point to a type parameter, whatever its signature
        // does.
        if let Some(arg) = args.iter().find(|arg| !self.storable(**arg)) {
            self.error(TypeErrorKind::NotStorable(self.ty_name(*arg)), call);
            return None;
        }
        let params = self.generic_fns[generic.0 as usize].params.clone();
        if !self.check_bounds(&params, args, call) {
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
    /// one. `None` as [`Self::instantiate_fn`] is.
    fn open_instance(&mut self, generic: GenericFnId, args: &[Ty], call: Span) -> Option<FuncSig> {
        if args.contains(&Ty::Error) {
            return None;
        }
        self.instance_sig(generic, args, call)
    }

    /// Lowers function `id`, an instance of a generic function. Its
    /// declaration is right for every list of type arguments, so an error in
    /// lowering it is one that checking the declaration missed.
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
        let names = decl.sig.type_param_names().into_iter().map(|p| p.name);
        self.type_params = names.zip(instance.args).collect();
        self.instance_chain = instance.chain;
        let sig = self.funcs[id.0 as usize].clone();
        let errors = self.errors.len();
        // A declaration with an error has it in every instance.
        let func = if self.generic_fns[instance.generic.0 as usize].failed {
            ir::Func {
                exports: Vec::new(),
                name: sig.name,
                params: Vec::new(),
                results: Vec::new(),
                locals: Vec::new(),
                body: Vec::new(),
            }
        } else {
            let func = self.lower_body(program, sig, &decl.body, item.span, Vec::new());
            for error in &mut self.errors[errors..] {
                // Only what an instance is too deep or too large for is its
                // type arguments' doing, and is reported at the call that led
                // to it.
                if let TypeErrorKind::InstanceTooDeep(_)
                | TypeErrorKind::InstanceTooLarge(_)
                | TypeErrorKind::NestedTooDeep(_) = error.kind
                {
                    continue;
                }
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
    pub(super) fn unify(&self, pattern: Ty, actual: Ty, bound: &mut [Option<Ty>]) {
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
            // A function is a pointer to itself where one is expected.
            (Ty::Fn(_), Ty::Func(id)) => {
                let (mut a, ret) = self.func_shape(id);
                a.push(ret);
                let p = self.components(pattern);
                if p.len() == a.len() {
                    for (p, a) in p.into_iter().zip(a) {
                        self.unify(p, a, bound);
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

    /// Settles the type parameters of generic function `generic` that
    /// `bound` leaves out, where the bound of one that it has names them:
    /// they are what makes the bound a type that the type argument starts
    /// as, or for a union or an enum, one that starts as the type argument.
    /// A bound names only type parameters before its own, so the last is
    /// taken first.
    pub(super) fn settle_by_bounds(&self, generic: GenericFnId, bound: &mut [Option<Ty>]) {
        let params = &self.generic_fns[generic.0 as usize].params;
        for (i, param) in params.iter().enumerate().rev() {
            let Ty::Param(id) = *param else {
                continue;
            };
            let (Some(want), Some(arg)) = (self.params[id.0 as usize].bound, bound[i]) else {
                continue;
            };
            if !self.has_unbound(want, bound) {
                continue;
            }
            let have = self.known(arg);
            if self.is_sum(want) {
                for first in self.starts(want) {
                    self.unify(first, have, bound);
                }
                continue;
            }
            let Some(listed) = self.listed(want) else {
                for first in self.starts(have) {
                    self.unify(want, first, bound);
                }
                continue;
            };
            // The first that uses what the bound lists, whatever the type
            // arguments of each.
            let alike = |(want, used): (&Ty, &Ty)| self.alike(*want, *used);
            let mut levels = self.starts(have).map(|first| self.used_by(first));
            let used = levels
                .find(|used| listed.len() <= used.len() && listed.iter().zip(*used).all(alike));
            for (want, used) in listed.iter().zip(used.unwrap_or_default()) {
                self.unify(*want, *used, bound);
            }
        }
    }

    /// Whether `pattern` and `actual` are the same type, type arguments
    /// aside: both arrays, or instances of one generic struct.
    fn alike(&self, pattern: Ty, actual: Ty) -> bool {
        let generic = |ty: Ty| match ty {
            Ty::Struct(id) => {
                let instance = self.structs[id.0 as usize].instance.as_ref();
                instance.map(|instance| instance.generic)
            }
            _ => None,
        };
        let arrays = matches!((pattern, actual), (Ty::Array(_), Ty::Array(_)));
        pattern == actual || arrays || generic(pattern).is_some_and(|g| Some(g) == generic(actual))
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
    /// A call of generic function `generic` spanning `span`, whose type
    /// arguments are those among `args` and those inferred from the others.
    pub(super) fn generic_fn_call(
        &mut self,
        generic: GenericFnId,
        args: &[Arg],
        span: Span,
    ) -> (Ty, Value) {
        let mut sig = self.ck.generic_fns[generic.0 as usize].sig.clone();
        let binding = self.bind_args(&sig.params, &sig.defaults, args, false, span);
        let item = self.ck.generic_fn_items[generic.0 as usize];
        if self.takes_defaults(item, &sig, &binding, span) {
            sig = self.ck.generic_fns[generic.0 as usize].sig.clone();
        }
        let mut checked: Vec<_> = args.iter().map(|_| None).collect();
        let type_args = self.type_args_of(generic, args, &binding, &mut checked, span);
        // An argument that would settle one is a `never`, and so is the
        // call: nothing says which instance it would be of.
        if checked.iter().flatten().any(|(ty, _)| *ty == Ty::Never) {
            let params = sig.params.iter().map(|(p, _)| (p.clone(), Ty::Error));
            let params: Vec<_> = params.collect();
            let value = self.bound_args(&params, &sig.defaults, args, binding, checked);
            return never(value.pre);
        }
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
        // A default with a type of its own is taken only as that type.
        let def = &self.ck.generic_fns[generic.0 as usize];
        let default_tys = def.default_tys.clone();
        for (i, own) in default_tys.into_iter().enumerate() {
            let Some(own) = own.filter(|_| !binding.contains(&Some(i))) else {
                continue;
            };
            let (param, expected) = &instance.params[i];
            if !self.ck.fits(own, *expected) && *expected != Ty::Error {
                let kind = TypeErrorKind::DefaultMismatch {
                    param: param.clone(),
                    expected: self.ck.ty_name(*expected),
                    found: self.ck.ty_name(own),
                };
                self.error(kind, span);
            }
        }
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
        // A type parameter is no parameter of an instance's pointer.
        let params: Vec<_> = params.filter(|ty| *ty != Ty::Type).collect();
        // A signature or expected type that failed to resolve is already
        // reported.
        if params.contains(&Ty::Error) || ret == Ty::Error || expected == Some(Ty::Error) {
            return (Ty::Error, Value::default());
        }
        let mut bound = vec![None; type_params.len()];
        if let Some(expected @ Ty::Fn(_)) = expected {
            let pattern = self.ck.fn_of(params, ret);
            self.ck.unify(pattern, expected, &mut bound);
            self.ck.settle_by_bounds(generic, &mut bound);
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
            let params = instance.params.into_iter().map(|(_, ty)| ty);
            let params = params.filter(|ty| *ty != Ty::Type).collect();
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

    /// The type `expr` writes, as the argument of a type parameter. The
    /// error type after reporting that it's a value.
    fn type_arg(&mut self, expr: &parse::Expr) -> Ty {
        if self.is_type_expr(expr) {
            return self.expr_type(expr);
        }
        if self.expr(expr, None).0 != Ty::Error {
            self.error(TypeErrorKind::NotAType, expr.span);
        }
        Ty::Error
    }

    /// The type arguments of a call of generic function `generic`, from the
    /// `args` that `binding` matches with its parameters: the types given
    /// to its parameters of type `type`, and those inferred from the other
    /// arguments. Of those, the ones that aren't literals, `.name`s or the
    /// names of functions go first, so that those take the types they
    /// settle: a function is a pointer where they settle on one, and is
    /// otherwise of its own type. Those naming generic functions are left
    /// for last. The arguments it checks are
    /// kept in `checked`. Type parameters that no argument settles are
    /// reported at `span`, and given the error type.
    fn type_args_of(
        &mut self,
        generic: GenericFnId,
        args: &[Arg],
        binding: &[Option<usize>],
        checked: &mut [Option<(Ty, Value)>],
        span: Span,
    ) -> Vec<Ty> {
        let def = &self.ck.generic_fns[generic.0 as usize];
        let patterns: Vec<_> = def.sig.params.iter().map(|(_, ty)| *ty).collect();
        let given = def.given.clone();
        let mut bound = vec![None; def.params.len()];
        for (k, (arg, param)) in args.iter().zip(binding).enumerate() {
            let Some(index) = param.and_then(|i| given[i]) else {
                continue;
            };
            let ty = self.type_arg(&arg.value);
            bound[index] = Some(ty);
            let found = match ty {
                Ty::Error => Ty::Error,
                _ => Ty::Type,
            };
            checked[k] = Some((found, Value::default()));
        }
        // One left without an argument is already reported.
        for index in given.iter().flatten() {
            bound[*index].get_or_insert(Ty::Error);
        }
        for literals in [false, true] {
            for (k, (arg, param)) in args.iter().zip(binding).enumerate() {
                let Some(i) = *param else {
                    continue;
                };
                // A generic function's instance is picked by its parameter's
                // type, so it settles nothing.
                let named = self.named(&arg.value);
                let late = is_typed_by_other(&arg.value) || matches!(named, Some(Item::Func(_)));
                if matches!(named, Some(Item::GenericFn(_)))
                    || late != literals
                    || !self.ck.has_unbound(patterns[i], &bound)
                {
                    continue;
                }
                let (ty, value) = self.expr(&arg.value, None);
                self.ck.unify(patterns[i], ty, &mut bound);
                // A bound settles a type parameter before a later argument
                // would, which is then checked against it.
                self.ck.settle_by_bounds(generic, &mut bound);
                checked[k] = Some((ty, value));
            }
        }
        if checked.iter().flatten().any(|(ty, _)| *ty == Ty::Never) {
            bound.fill(Some(Ty::Never));
        }
        // A default with a type of its own settles what no argument did.
        let default_tys = self.ck.generic_fns[generic.0 as usize].default_tys.clone();
        for (i, own) in default_tys.into_iter().enumerate() {
            if let Some(own) = own.filter(|_| !binding.contains(&Some(i))) {
                self.ck.unify(patterns[i], own, &mut bound);
            }
        }
        self.ck.settle_by_bounds(generic, &mut bound);
        // Missing arguments, and signatures and defaults that failed to
        // resolve, are already reported. Any other default settles nothing.
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
    fn errors_that_checking_a_declaration_misses_are_internal() {
        let src = "\
fn(T) add(a: T, b: T) -> T:
    return a + b
fn f():
    add(true, false)
";
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let mut ck = Checker::define(&program, &Settings::default(), false);
        // As if checking `add` as declared had found nothing wrong with it.
        assert!(ck.errors.is_empty());
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

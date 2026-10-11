//! Functions as values. A function is a value of a type of its own, which
//! only it is of: nothing is stored of it, and a call of one is a call of
//! the function.
//!
//! Where a pointer is expected, the function is one: a value of a type
//! `fn(A) -> R`, which is an index into the module's table, as wide as an
//! address. A function is given an index the first time its pointer is
//! taken, so pointers are constants. Calls through them are
//! `call_indirect`s, which trap on a function of another wasm type.

use crate::ir::{self, Expr, FuncId, Stmt};
use crate::lex::Span;
use crate::parse::{self, Arg};

use super::{
    Body, Checker, Dep, FnId, FuncSig, Synth, Ty, TypeErrorKind, Value, exprs, is_pure, is_stable,
    path_text, split1,
};

impl Checker {
    /// The interned type `fn(params) -> ret`.
    pub(super) fn fn_of(&mut self, params: Vec<Ty>, ret: Ty) -> Ty {
        let next = FnId(self.fn_tys.len() as u32);
        let id = *self.fn_ty_ids.entry((params.clone(), ret)).or_insert(next);
        if id == next {
            self.fn_tys.push((params, ret));
        }
        Ty::Fn(id)
    }

    /// The parameter types and result type of the pointers to function
    /// `id`.
    pub(super) fn func_shape(&self, id: FuncId) -> (Vec<Ty>, Ty) {
        let sig = &self.funcs[id.0 as usize];
        // A type parameter of an instance is no parameter of its pointer.
        let params = sig.params.iter().map(|(_, ty)| *ty);
        (params.filter(|ty| *ty != Ty::Type).collect(), sig.ret)
    }

    /// The type of the pointers to function `id`.
    pub(super) fn pointer_ty(&mut self, id: FuncId) -> Ty {
        let (params, ret) = self.func_shape(id);
        self.fn_of(params, ret)
    }

    /// The type that a `ty` is where a pointer to a function is needed: that
    /// of the pointers to the function, if it's the type of one, and
    /// otherwise itself.
    pub(super) fn pointer_ty_of(&mut self, ty: Ty) -> Ty {
        match ty {
            Ty::Func(id) => self.pointer_ty(id),
            _ => ty,
        }
    }

    /// The type of a function that a value of type `ty` holds, if it holds
    /// one: `ty` itself, or what a struct, a tuple or an enum of it holds.
    fn func_part(&self, ty: Ty) -> Option<Ty> {
        match ty {
            Ty::Func(_) => Some(ty),
            Ty::Enum(id) => self.func_part(self.enum_ty(id)),
            Ty::Struct(_) | Ty::Tuple(_) => {
                let mut members = self.members(ty).into_iter();
                members.find_map(|member| self.func_part(member))
            }
            _ => None,
        }
    }

    /// Reports each type in the signature of the `extern` function `sig`,
    /// resolved as `params` and `ret`, that holds the type of a function:
    /// nothing is passed for one, so the host neither takes nor gives it.
    pub(super) fn check_host_sig(&mut self, sig: &parse::FnSig, params: &[(String, Ty)], ret: Ty) {
        let written = sig.params.iter().map(|param| param.ty.span);
        let params = params.iter().map(|(_, ty)| *ty).zip(written);
        let ret = sig.ret.as_ref().map(|written| (ret, written.span));
        for (ty, span) in params.chain(ret).collect::<Vec<_>>() {
            if let Some(held) = self.func_part(ty) {
                let (ty, func) = (self.ty_name(held), sig.name.name.clone());
                self.error(TypeErrorKind::HostFnType { ty, func }, span);
            }
        }
    }

    /// The table index of function `id`, which is the next one free the
    /// first time it's asked for.
    fn table_index(&mut self, id: FuncId) -> u32 {
        // A generic function checked as declared takes no pointers.
        if self.open {
            return 0;
        }
        let target = self.pointer_target(id);
        self.note(Dep::Func(target));
        // Nothing is at index 0, so that calling zeroed memory traps.
        let next = self.table.len() as u32 + 1;
        let index = *self.table_indices.entry(target).or_insert(next);
        if index == next {
            self.table.push(target);
        }
        index
    }

    /// The function that pointers to function `id` call: `id` itself,
    /// unless the host supplies it and a call of it doesn't pass wasm
    /// values as they are: the host may give a narrow integer or `bool` out
    /// of range, or takes or gives what it does in memory. Then it's a
    /// function that calls `id` as any call does, created the first time
    /// it's asked for and lowered by [`Self::lower_wrapper`].
    fn pointer_target(&mut self, id: FuncId) -> FuncId {
        let sig = &self.funcs[id.0 as usize];
        let passes = |ck: &Self| {
            let passing = ck.import_passing(id);
            passing.params.is_none() && passing.result.is_none()
        };
        if id.0 >= self.import_count || (self.ranged(sig.ret).is_empty() && passes(self)) {
            return id;
        }
        if let Some(wrapper) = self.wrappers.get(&id) {
            return *wrapper;
        }
        let wrapper = FuncId(self.funcs.len() as u32);
        let name = format!("extern {}", sig.name);
        let sig = FuncSig {
            name,
            defaults: Vec::new(),
            ..sig.clone()
        };
        self.funcs.push(sig);
        self.synths.push(Synth::Wrapper(id));
        self.wrappers.insert(id, wrapper);
        wrapper
    }

    /// Lowers function `id`, which [`Self::pointer_target`] created to call
    /// the imported function `import`.
    pub(super) fn lower_wrapper(&mut self, id: FuncId, import: FuncId) -> ir::Func {
        let sig = self.funcs[id.0 as usize].clone();
        let mut body = Body::new(self, sig.ret);
        for (name, ty) in &sig.params {
            body.alloc(name, *ty);
        }
        let params: Vec<_> = body.locals.iter().map(|local| local.ty).collect();
        let args = (0..).map(ir::LocalId).map(Expr::Local);
        let args = Value {
            pre: Vec::new(),
            scalars: params.iter().copied().zip(args).collect(),
        };
        let (_, value) = body.call_func(import, args);
        let mut stmts = value.pre;
        stmts.push(Stmt::Return(exprs(value.scalars)));
        let locals = body.locals;
        ir::Func {
            exports: Vec::new(),
            name: sig.name,
            params,
            results: self.val_types(sig.ret),
            locals,
            body: stmts,
        }
    }
}

impl Body<'_> {
    /// Function `id` itself, a value of its own type.
    pub(super) fn func_value(&mut self, id: FuncId) -> (Ty, Value) {
        let (params, ret) = self.ck.func_shape(id);
        // A signature that failed to resolve is already reported.
        if params.contains(&Ty::Error) || ret == Ty::Error {
            return (Ty::Error, Value::default());
        }
        (Ty::Func(id), Value::default())
    }

    /// A `ty` as it is where a `want` is expected, if anything is: a
    /// function is a pointer to itself where a pointer of its type is.
    /// Any other is what it was. `value` is evaluated first.
    pub(super) fn as_expected(&mut self, ty: Ty, value: Value, want: Option<Ty>) -> (Ty, Value) {
        match (ty, want) {
            (Ty::Func(id), Some(want @ Ty::Fn(_))) if self.ck.pointer_ty(id) == want => {
                (want, self.pointer_to(id, value))
            }
            _ => (ty, value),
        }
    }

    /// A function as the pointer to it, where only its address serves: it
    /// is compared, or cast. Any other is what it was.
    pub(super) fn as_pointer(&mut self, ty: Ty, value: Value) -> (Ty, Value) {
        let want = self.ck.pointer_ty_of(ty);
        self.as_expected(ty, value, Some(want))
    }

    /// A pointer to function `id`, once `value` is evaluated, which is the
    /// function itself.
    pub(super) fn pointer_to(&mut self, id: FuncId, value: Value) -> Value {
        let index = self.ck.table_index(id);
        let index = Expr::Const(self.ck.addr_const(index.into()));
        Value {
            pre: value.pre,
            scalars: vec![(self.ck.addr_type(), index)],
        }
    }

    /// A call of `callee`, a value rather than the name of a function, with
    /// `args`, which are matched to its parameters in order.
    pub(super) fn call_value(
        &mut self,
        callee: &parse::Expr,
        args: &[Arg],
        span: Span,
    ) -> (Ty, Value) {
        let (ty, callee_value) = self.expr(callee, None);
        if ty == Ty::Never {
            return (ty, callee_value);
        }
        let Some((params, ret)) = self.ck.called_as(ty) else {
            if ty != Ty::Error {
                self.error(TypeErrorKind::NotCallable(path_text(callee)), callee.span);
            }
            for arg in args {
                self.expr(&arg.value, None);
            }
            return (Ty::Error, Value::default());
        };
        let (expected, found) = (params.len(), args.len());
        if found > expected {
            self.error(TypeErrorKind::TooManyArgs { expected, found }, span);
        } else if found < expected {
            self.error(TypeErrorKind::TooFewArgs { expected, found }, span);
        }
        let mut values = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if let Some(label) = &arg.label {
                self.error(TypeErrorKind::LabelledPointerArg, label.span);
            }
            match params.get(i) {
                Some(param) => values.push(self.check(&arg.value, *param)),
                None => {
                    self.expr(&arg.value, None);
                }
            }
        }
        // A function itself is called as it is by name, and nothing is
        // evaluated of it but what led to it.
        if let Ty::Func(id) = ty {
            values.insert(0, callee_value);
            let args = self.seq(values);
            return self.call_func(id, args);
        }
        // A type parameter is called only where a generic function is
        // checked as declared, which calls nothing.
        if let Ty::Param(_) = ty {
            values.insert(0, callee_value);
            let pre = self.seq(values).pre;
            let scalars = self.blank(ret).scalars;
            return (ret, Value { pre, scalars });
        }
        let args = self.seq(values);
        let (mut pre, mut index) = split1(callee_value);
        // Wasm takes the index last, but the callee is written first, so it
        // goes in a temporary unless nothing can tell which ran first: one
        // side can't be changed by the other, or neither changes anything.
        let all = |keep: fn(&Expr) -> bool| args.scalars.iter().all(|(_, arg)| keep(arg));
        let either_order =
            args.pre.is_empty() && (all(is_stable) || is_pure(&index) && all(is_pure));
        if !is_stable(&index) && !either_order {
            let tmp = self.temp(self.ck.addr_type());
            pre.push(Stmt::SetLocal(tmp, index));
            index = Expr::Local(tmp);
        }
        pre.extend(args.pre);
        let params = params.iter().flat_map(|param| self.ck.val_types(*param));
        let ty = ir::FuncType {
            params: params.collect(),
            results: self.ck.val_types(ret),
        };
        let args = exprs(args.scalars);
        let scalars = if let [result] = ty.results[..] {
            let index = Box::new(index);
            vec![(result, Expr::CallIndirect { ty, args, index })]
        } else {
            let dests: Vec<_> = ty.results.iter().map(|vt| self.temp(*vt)).collect();
            let scalars = ty
                .results
                .iter()
                .zip(&dests)
                .map(|(vt, dest)| (*vt, Expr::Local(*dest)))
                .collect();
            pre.push(Stmt::CallIndirect {
                ty,
                args,
                index,
                dests,
            });
            scalars
        };
        // One that returns a `never` never returns.
        if ret == Ty::Never {
            pre.push(Stmt::Unreachable);
        }
        (ret, Value { pre, scalars })
    }
}

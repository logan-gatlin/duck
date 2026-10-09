//! Function pointers: values of the types `fn(A) -> R`, which are indices
//! into the module's table, as wide as an address. A function is given an
//! index the first time its pointer is taken, so pointers are constants.
//! Calls through them are `call_indirect`s, which trap on a function of
//! another wasm type.

use crate::ir::{self, Expr, FuncId, Stmt};
use crate::lex::Span;
use crate::parse::{self, Arg};

use super::{
    Body, Checker, Dep, FnId, FuncSig, Synth, Ty, TypeErrorKind, Value, exprs, is_pure, is_stable,
    path_text, scalar, split1,
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
    /// unless the host supplies it and may give it a narrow integer or
    /// `bool` out of range. Then it's a function that calls `id` and brings
    /// its results into range, created the first time it's asked for and
    /// lowered by [`Self::lower_wrapper`].
    fn pointer_target(&mut self, id: FuncId) -> FuncId {
        let sig = &self.funcs[id.0 as usize];
        if id.0 >= self.import_count || self.ranged(sig.ret).is_empty() {
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
    /// A pointer to function `id`.
    pub(super) fn func_value(&mut self, id: FuncId) -> (Ty, Value) {
        let sig = &self.ck.funcs[id.0 as usize];
        // A type parameter of an instance is no parameter of its pointer.
        let params = sig.params.iter().map(|(_, ty)| *ty);
        let params: Vec<_> = params.filter(|ty| *ty != Ty::Type).collect();
        let ret = sig.ret;
        // A signature that failed to resolve is already reported.
        if params.contains(&Ty::Error) || ret == Ty::Error {
            return (Ty::Error, Value::default());
        }
        let index = self.ck.table_index(id);
        let index = Expr::Const(self.ck.addr_const(index.into()));
        (
            self.ck.fn_of(params, ret),
            scalar(self.ck.addr_type(), index),
        )
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
        let Ty::Fn(id) = ty else {
            if ty != Ty::Error {
                self.error(TypeErrorKind::NotCallable(path_text(callee)), callee.span);
            }
            for arg in args {
                self.expr(&arg.value, None);
            }
            return (Ty::Error, Value::default());
        };
        let (params, ret) = self.ck.fn_tys[id.0 as usize].clone();
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
        (ret, Value { pre, scalars })
    }
}

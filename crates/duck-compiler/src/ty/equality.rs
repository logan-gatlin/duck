//! `==` and `!=` on values of any type that can be stored in memory. Values
//! are equal when every field is: scalars compare as `==` does on their own,
//! except within enums, which compare bit for bit, and arrays compare their
//! elements through a generated function per array type.

use crate::ir::{self, BinOp as IrBinOp, Const, Expr, FuncId, Stmt, UnOp as IrUnOp, ValType};
use crate::lex::Span;
use crate::parse::BinOp;

use super::{
    Body, Checker, FuncSig, Prim, Synth, Ty, TypeErrorKind, Value, binary, binop_symbol,
    element_addr, exprs, is_pure, is_stable, scalar, split1,
};

/// How one piece of a value is compared, in leaf order.
enum Part {
    /// A scalar, compared as `==` compares its primitive type.
    Scalar(ValType),
    /// A scalar of an enum, compared by its bits.
    Bits(ValType),
    /// An array's `len` and `ptr`, compared element by element.
    Array(Ty),
}

impl Part {
    /// How many scalar leaves the part covers.
    fn width(&self) -> usize {
        match self {
            Part::Scalar(_) | Part::Bits(_) => 1,
            Part::Array(_) => 2,
        }
    }
}

impl Checker {
    /// The pieces `==` compares values of the storable type `ty` by.
    fn parts(&self, ty: Ty) -> Vec<Part> {
        let mut out = Vec::new();
        self.push_parts(ty, &mut out);
        out
    }

    fn push_parts(&self, ty: Ty, out: &mut Vec<Part>) {
        match ty {
            Ty::Prim(prim) => out.push(Part::Scalar(prim.val_type())),
            Ty::Ptr(_) | Ty::Fn(_) => out.push(Part::Scalar(ValType::I32)),
            Ty::Enum(id) => {
                out.extend(self.val_types(self.enum_ty(id)).into_iter().map(Part::Bits))
            }
            Ty::Array(_) => out.push(Part::Array(ty)),
            Ty::Struct(_) | Ty::Tuple(_) | Ty::Type => {
                for member in self.members(ty) {
                    self.push_parts(member, out);
                }
            }
            Ty::ExternRef => unreachable!("`externref` can't be compared"),
            Ty::Param(_) | Ty::Unit | Ty::Error => {}
        }
    }

    /// Whether comparing values of type `ty` compares arrays.
    fn compares_arrays(&self, ty: Ty) -> bool {
        self.parts(ty)
            .iter()
            .any(|part| matches!(part, Part::Array(_)))
    }

    /// The function comparing two arrays of type `ty`, created the first time
    /// it's asked for and lowered by [`Self::lower_eq_func`]. A `varray`
    /// compares through the function of its `array`.
    fn eq_func(&mut self, ty: Ty) -> FuncId {
        let ty = self.with_writes(ty, false);
        // A generic function checked as declared compares arrays of no type.
        if self.open {
            return FuncId(0);
        }
        if let Some(id) = self.eq_funcs.get(&ty) {
            return *id;
        }
        let id = FuncId(self.funcs.len() as u32);
        self.funcs.push(FuncSig {
            name: format!("==({})", self.ty_name(ty)),
            params: vec![("a".to_string(), ty), ("b".to_string(), ty)],
            defaults: Vec::new(),
            ret: Ty::Prim(Prim::Bool),
        });
        self.synths.push(Synth::Eq(ty));
        self.eq_funcs.insert(ty, id);
        id
    }

    /// Lowers function `id`, which [`Self::eq_func`] created to compare
    /// arrays of type `ty`.
    pub(super) fn lower_eq_func(&mut self, id: FuncId, ty: Ty) -> ir::Func {
        let sig = self.funcs[id.0 as usize].clone();
        let mut body = Body::new(self, sig.ret);
        let a = body.alloc("a", ty);
        let b = body.alloc("b", ty);
        let params = body.locals.iter().map(|local| local.ty).collect();
        let stmts = body.array_eq_body(ty, [a[0], a[1]], [b[0], b[1]]);
        ir::Func {
            export: None,
            name: sig.name,
            params,
            results: vec![ValType::I32],
            locals: body.locals,
            body: stmts,
        }
    }
}

impl Body<'_> {
    /// `lhs == rhs` or `lhs != rhs` for values of the type `ty`. Values that
    /// hold an `externref` have nothing to compare, and arrays can't be
    /// compared in constants, as that takes a call.
    pub(super) fn eq_values(
        &mut self,
        op: BinOp,
        ty: Ty,
        lhs: Value,
        rhs: Value,
        span: Span,
    ) -> (Ty, Value) {
        let bool = Ty::Prim(Prim::Bool);
        if ty == Ty::Error || !self.ck.stores(ty) {
            return self.invalid_operand(binop_symbol(op), ty, span);
        }
        // Checked up front, as folding skips calls in branches it doesn't
        // take.
        if self.global && self.ck.compares_arrays(ty) {
            self.error(TypeErrorKind::NotConstant, span);
            return (bool, scalar(ValType::I32, Expr::Const(Const::I32(0))));
        }
        (bool, self.compare(op, ty, lhs, rhs))
    }

    /// Compares every scalar at once, then any arrays one at a time, only
    /// while the result is still undecided.
    fn compare(&mut self, op: BinOp, ty: Ty, lhs: Value, rhs: Value) -> Value {
        let parts = self.ck.parts(ty);
        let width = parts.iter().map(Part::width).sum::<usize>();
        let has_array = parts.iter().any(|part| matches!(part, Part::Array(_)));
        let mut value = self.seq(vec![lhs, rhs]);
        // Scalars are compared in pairs, out of source order, and those of
        // arrays may not be read at all.
        if has_array {
            self.spill(&mut value, is_stable);
        } else if width > 1 {
            self.spill(&mut value, is_pure);
        }
        let mut lhs = exprs(value.scalars);
        // Only after a type error.
        if lhs.len() != 2 * width {
            return scalar(ValType::I32, Expr::Const(Const::I32(0)));
        }
        let mut rhs = lhs.split_off(width).into_iter();
        let mut lhs = lhs.into_iter();
        let (cmp, join, empty) = match op {
            BinOp::Eq => (IrBinOp::Eq, IrBinOp::And, 1),
            _ => (IrBinOp::Ne, IrBinOp::Or, 0),
        };
        let mut scalars = Vec::new();
        let mut arrays = Vec::new();
        for part in parts {
            let (a, b) = (lhs.next().unwrap(), rhs.next().unwrap());
            match part {
                Part::Scalar(vt) => scalars.push(binary(vt, cmp, a, b)),
                Part::Bits(vt) => {
                    let bits = |e| Expr::Unary(vt, IrUnOp::Reinterpret, Box::new(e));
                    scalars.push(match vt {
                        ValType::F32 => binary(ValType::I32, cmp, bits(a), bits(b)),
                        ValType::F64 => binary(ValType::I64, cmp, bits(a), bits(b)),
                        _ => binary(vt, cmp, a, b),
                    });
                }
                Part::Array(ty) => {
                    let (a_ptr, b_ptr) = (lhs.next().unwrap(), rhs.next().unwrap());
                    let call = Expr::Call(self.ck.eq_func(ty), vec![a, a_ptr, b, b_ptr]);
                    arrays.push(match op {
                        BinOp::Eq => call,
                        _ => Expr::Unary(ValType::I32, IrUnOp::Eqz, Box::new(call)),
                    });
                }
            }
        }
        let scalars = scalars
            .into_iter()
            .reduce(|acc, e| binary(ValType::I32, join, acc, e));
        // Each array is only compared if everything before it didn't decide.
        let expr = scalars
            .into_iter()
            .chain(arrays)
            .reduce(|acc, e| {
                let (then_expr, else_expr) = match op {
                    BinOp::Eq => (e, Expr::Const(Const::I32(0))),
                    _ => (Expr::Const(Const::I32(1)), e),
                };
                Expr::If {
                    ty: ValType::I32,
                    cond: Box::new(acc),
                    then_expr: Box::new(then_expr),
                    else_expr: Box::new(else_expr),
                }
            })
            .unwrap_or(Expr::Const(Const::I32(empty)));
        Value {
            pre: value.pre,
            scalars: vec![(ValType::I32, expr)],
        }
    }

    /// The body of the function comparing the arrays `a` and `b` of type
    /// `ty`, given the locals of their `len` and `ptr`. Returns at the first
    /// element that differs.
    fn array_eq_body(&mut self, ty: Ty, a: [ir::LocalId; 2], b: [ir::LocalId; 2]) -> Vec<Stmt> {
        let [a_len, a_ptr] = a.map(Expr::Local);
        let [b_len, b_ptr] = b.map(Expr::Local);
        let differ = || vec![Stmt::Return(vec![Expr::Const(Const::I32(0))])];
        let mut out = vec![Stmt::If {
            cond: binary(ValType::I32, IrBinOp::Ne, a_len.clone(), b_len),
            then_body: differ(),
            else_body: Vec::new(),
        }];
        let Ty::Array(id) = ty else {
            unreachable!("only arrays are compared by functions")
        };
        let elem = self.ck.element(id);
        if !self.ck.parts(elem).is_empty() {
            let index = self.temp(ValType::I32);
            let i = Expr::Local(index);
            out.push(Stmt::SetLocal(index, Expr::Const(Const::I32(0))));
            let done = binary(ValType::I32, IrBinOp::GeU, i.clone(), a_len);
            let mut inner = vec![Stmt::BrIf(1, done)];
            let stride = self.ck.layout(elem).0;
            let [x, y] = [a_ptr, b_ptr].map(|ptr| {
                let addr = element_addr(ptr, i.clone(), stride);
                self.load(scalar(ValType::I32, addr), 0, elem)
            });
            let ne = self.compare(BinOp::NotEq, elem, x, y);
            let (pre, ne) = split1(ne);
            inner.extend(pre);
            inner.push(Stmt::If {
                cond: ne,
                then_body: differ(),
                else_body: Vec::new(),
            });
            let next = binary(ValType::I32, IrBinOp::Add, i, Expr::Const(Const::I32(1)));
            inner.push(Stmt::SetLocal(index, next));
            inner.push(Stmt::Br(0));
            out.push(Stmt::Block(vec![Stmt::Loop(inner)]));
        }
        out.push(Stmt::Return(vec![Expr::Const(Const::I32(1))]));
        out
    }
}

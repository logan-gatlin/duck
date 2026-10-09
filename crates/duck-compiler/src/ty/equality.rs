//! `==` and `!=` on values of any type that can be stored in memory. Values
//! are equal when every field is: scalars compare as `==` does on their own,
//! except within enums, which compare bit for bit, and arrays compare their
//! elements through a generated function per array type. Unions are equal
//! when they hold the same variant and its values are equal.

use crate::ir::{self, BinOp as IrBinOp, Const, Expr, FuncId, Stmt, UnOp as IrUnOp, ValType};
use crate::lex::Span;
use crate::parse::BinOp;

use super::{
    Body, Checker, FuncSig, Leaf, Prim, Synth, Ty, Value, binary, binop_symbol, exprs, is_pure,
    is_stable, scalar, split1,
    unions::{self, Holds, narrow, tags_are, widen},
};

/// One piece of a value that is compared, a union's tag before each of its
/// variants in turn.
struct Part {
    how: Compare,
    /// The leaves of the value that hold the piece, each of which may be
    /// wider than what it holds where the variants of a union share it.
    leaves: Vec<Leaf>,
    /// For a piece of a union's variant, each union it's in and the variant
    /// of it, outermost first: the piece is compared only where they all
    /// hold.
    when: Vec<Holds>,
}

/// How a piece of a value is compared.
enum Compare {
    /// A scalar, compared as `==` compares its primitive type.
    Scalar(ValType),
    /// A scalar of an enum, compared by its bits.
    Bits(ValType),
    /// An array's `ptr` and `len`, compared element by element.
    Array(Ty),
}

impl Checker {
    /// The pieces `==` compares values of the storable type `ty` by.
    fn parts(&self, ty: Ty) -> Vec<Part> {
        let mut out = Vec::new();
        self.push_parts(ty, false, &self.leaf_list(ty), &[], &mut out);
        out
    }

    /// Pushes the pieces of a `ty` held in `leaves`, which are compared
    /// where every union of `when` holds its variant, and by their `bits`
    /// within an enum.
    fn push_parts(&self, ty: Ty, bits: bool, leaves: &[Leaf], when: &[Holds], out: &mut Vec<Part>) {
        let scalar = |vt| match bits {
            true => Compare::Bits(vt),
            false => Compare::Scalar(vt),
        };
        let part = |how, leaves: &[Leaf]| Part {
            how,
            leaves: leaves.to_vec(),
            when: when.to_vec(),
        };
        match ty {
            Ty::Prim(prim) => out.push(part(scalar(self.fixed(prim).val_type()), leaves)),
            Ty::Ptr(_) | Ty::Fn(_) => out.push(part(scalar(self.addr_type()), leaves)),
            Ty::Enum(id) => self.push_parts(self.enum_ty(id), true, leaves, when, out),
            Ty::Array(_) if !bits => out.push(part(Compare::Array(ty), leaves)),
            Ty::Struct(_) if self.union_id(ty).is_some() => {
                out.push(part(scalar(unions::TAG.val_type()), &leaves[..1]));
                let variants = self.member_leaves(ty, leaves).into_iter();
                for (index, (variant, held)) in variants.enumerate() {
                    let mut when = when.to_vec();
                    when.push(Holds::new(leaves[0], index));
                    self.push_parts(variant, bits, &held, &when, out);
                }
            }
            Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_) => {
                for (member, held) in self.member_leaves(ty, leaves) {
                    self.push_parts(member, bits, &held, when, out);
                }
            }
            Ty::ExternRef => unreachable!("`externref` can't be compared"),
            Ty::Param(_) | Ty::Type | Ty::Unit | Ty::Never | Ty::Error => {}
        }
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
            exports: Vec::new(),
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
        if ty == Ty::Error || !self.ck.storable(ty) {
            return self.invalid_operand(binop_symbol(op), ty, span);
        }
        (bool, self.compare(op, ty, lhs, rhs))
    }

    /// Compares every scalar at once, then any arrays one at a time, only
    /// while the result is still undecided. What a union's variant holds is
    /// compared only where both values hold it.
    pub(super) fn compare(&mut self, op: BinOp, ty: Ty, lhs: Value, rhs: Value) -> Value {
        let parts = self.ck.parts(ty);
        let width = self.ck.val_types(ty).len();
        let has_array = parts.iter().any(|p| matches!(p.how, Compare::Array(_)));
        let has_union = parts.iter().any(|part| !part.when.is_empty());
        let mut value = self.seq(vec![lhs, rhs]);
        // Scalars are compared in pairs, out of source order, and those of
        // arrays may not be read at all. A union's tags are read again for
        // each piece of its variants.
        if has_union {
            self.spill_simple(&mut value);
        } else if has_array {
            self.spill(&mut value, is_stable);
        } else if width > 1 {
            self.spill(&mut value, is_pure);
        }
        let mut lhs = exprs(value.scalars);
        // Only after a type error.
        if lhs.len() != 2 * width {
            return scalar(ValType::I32, Expr::Const(Const::I32(0)));
        }
        let rhs = lhs.split_off(width);
        let (cmp, join, empty) = match op {
            BinOp::Eq => (IrBinOp::Eq, IrBinOp::And, 1),
            _ => (IrBinOp::Ne, IrBinOp::Or, 0),
        };
        let mut scalars = Vec::new();
        let mut arrays = Vec::new();
        for part in parts {
            // The scalar of type `vt` that a leaf of one side holds.
            let read =
                |side: &[Expr], leaf: Leaf, vt| narrow(leaf.ty, vt, side[leaf.index].clone());
            let compared = match part.how {
                Compare::Scalar(vt) => {
                    let leaf = part.leaves[0];
                    binary(vt, cmp, read(&lhs, leaf, vt), read(&rhs, leaf, vt))
                }
                Compare::Bits(vt) => {
                    let leaf = part.leaves[0];
                    let int = match vt {
                        ValType::F32 => ValType::I32,
                        ValType::F64 => ValType::I64,
                        vt => vt,
                    };
                    // A leaf wider than a float holds its bits already.
                    let bits = |side: &[Expr]| match leaf.ty == vt {
                        true => widen(vt, int, side[leaf.index].clone()),
                        false => read(side, leaf, int),
                    };
                    binary(int, cmp, bits(&lhs), bits(&rhs))
                }
                Compare::Array(ty) => {
                    let sides = [&lhs, &rhs].into_iter();
                    let args = sides.flat_map(|side| {
                        let ends = part.leaves.iter();
                        ends.map(|end| read(side, *end, self.ck.addr_type()))
                    });
                    let args = args.collect();
                    let call = Expr::Call(self.ck.eq_func(ty), args);
                    match op {
                        BinOp::Eq => call,
                        _ => Expr::Unary(ValType::I32, IrUnOp::Eqz, Box::new(call)),
                    }
                }
            };
            // The tags are compared too, so one value's say whether both
            // hold the variant: those that are known, if either's are.
            let held = match (tags_are(&part.when, &lhs), tags_are(&part.when, &rhs)) {
                (Expr::Const(Const::I32(0)), _) | (_, Expr::Const(Const::I32(0))) => continue,
                (Expr::Const(_), held) | (held, _) => held,
            };
            let compared = match held {
                Expr::Const(_) => compared,
                held => Expr::If {
                    ty: ValType::I32,
                    cond: Box::new(held),
                    then_expr: Box::new(compared),
                    else_expr: Box::new(Expr::Const(Const::I32(empty))),
                },
            };
            match part.how {
                Compare::Array(_) => arrays.push(compared),
                Compare::Scalar(_) | Compare::Bits(_) => scalars.push(compared),
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
    /// `ty`, given the locals of their `ptr` and `len`. Returns at the first
    /// element that differs.
    fn array_eq_body(&mut self, ty: Ty, a: [ir::LocalId; 2], b: [ir::LocalId; 2]) -> Vec<Stmt> {
        let [a_ptr, a_len] = a.map(Expr::Local);
        let [b_ptr, b_len] = b.map(Expr::Local);
        let differ = || vec![Stmt::Return(vec![Expr::Const(Const::I32(0))])];
        let vt = self.ck.addr_type();
        let mut out = vec![Stmt::If {
            cond: binary(vt, IrBinOp::Ne, a_len.clone(), b_len),
            then_body: differ(),
            else_body: Vec::new(),
        }];
        let Ty::Array(id) = ty else {
            unreachable!("only arrays are compared by functions")
        };
        let elem = self.ck.element(id);
        if !self.ck.parts(elem).is_empty() {
            let index = self.temp(vt);
            let i = Expr::Local(index);
            out.push(Stmt::SetLocal(index, Expr::Const(self.ck.addr_const(0))));
            let done = binary(vt, IrBinOp::GeU, i.clone(), a_len);
            let mut inner = vec![Stmt::BrIf(1, done)];
            let stride = self.ck.layout(elem).0;
            let [x, y] = [a_ptr, b_ptr].map(|ptr| {
                let addr = self.ck.element_addr(ptr, i.clone(), stride);
                self.load(scalar(vt, addr), 0, elem)
            });
            let ne = self.compare(BinOp::NotEq, elem, x, y);
            let (pre, ne) = split1(ne);
            inner.extend(pre);
            inner.push(Stmt::If {
                cond: ne,
                then_body: differ(),
                else_body: Vec::new(),
            });
            let next = binary(vt, IrBinOp::Add, i, Expr::Const(self.ck.addr_const(1)));
            inner.push(Stmt::SetLocal(index, next));
            inner.push(Stmt::Br(0));
            out.push(Stmt::Block(vec![Stmt::Loop(inner)]));
        }
        out.push(Stmt::Return(vec![Expr::Const(Const::I32(1))]));
        out
    }
}

//! How what a function takes and gives crosses to the host, as the
//! Canonical ABI of the component model has it.
//!
//! A value is the wasm values of its scalars, as it is between functions of
//! the source, while there are few enough: parameters of up to
//! [`MAX_FLAT_PARAMS`] values, and a result of up to [`MAX_FLAT_RESULTS`].
//! More than that are passed in memory, where they are laid out as a tuple
//! of them is, by a pointer.
//!
//! A call of an import has nowhere of its own to put them, as nothing is a
//! stack in memory. So the module has one return area, which every call
//! uses: the parameters are stored there, the host writes the result there,
//! and the call reads it into locals before anything else runs. An export
//! stores its result there as it returns, which the host reads before it
//! calls anything else of the module. Nothing else is ever there, so it is
//! only as large as the most that one function passes through it.

use crate::ir::{self, Expr, FuncId, Stmt, ValType};

use super::{Body, Checker, FuncSig, Place, Slots, Ty, Value, exprs, is_simple, scalar};

/// The most wasm values that the parameters of a function are, before they
/// are passed in memory.
const MAX_FLAT_PARAMS: usize = 16;

/// The most wasm values that the result of a function is, before it is
/// passed in memory.
const MAX_FLAT_RESULTS: usize = 1;

/// The bytes of the return area where the [`Settings`] give no size.
///
/// [`Settings`]: crate::file::Settings
pub const DEFAULT_RETURN_AREA: u32 = 128;

/// What the return area is aligned to: the most that any type is.
const RETURN_AREA_ALIGN: u32 = 8;

/// How what a function takes and gives is passed.
pub(super) struct Passing {
    /// Where each parameter is in the memory they are passed in, if they
    /// are: for an import, in the return area.
    pub(super) params: Option<Vec<u32>>,
    /// Where the result is in the return area, if it is passed in memory.
    pub(super) result: Option<u32>,
    /// How much of the return area that takes.
    pub(super) size: u32,
}

impl Checker {
    /// How `sig` is passed: as one that is `imported` passes it, or as one
    /// that is exported does, whose parameters the host puts in memory that
    /// it has the module allocate.
    pub(super) fn passing(&self, sig: &FuncSig, imported: bool) -> Passing {
        let params = sig.params.iter().map(|(_, ty)| *ty);
        let params: Vec<_> = params.filter(|ty| *ty != Ty::Type).collect();
        let flat: usize = params.iter().map(|ty| self.val_types(*ty).len()).sum();
        // Where a `ty` goes after `size` bytes, and how many there are
        // with it.
        let place = |size: u32, ty: Ty| {
            let (bytes, align) = self.layout(ty);
            let at = size.next_multiple_of(align);
            (at, at + bytes)
        };
        let mut size = 0;
        let params = (flat > MAX_FLAT_PARAMS).then(|| {
            let mut offsets = Vec::new();
            for ty in params {
                let (at, end) = place(size, ty);
                offsets.push(at);
                size = end;
            }
            offsets
        });
        // The host has the module allocate for the parameters of an export.
        if !imported {
            size = 0;
        }
        let results = self.val_types(sig.ret).len();
        let result = (results > MAX_FLAT_RESULTS).then(|| {
            let (at, end) = place(size, sig.ret);
            size = end;
            at
        });
        Passing {
            params,
            result,
            size,
        }
    }

    /// The wasm type of the import that `sig` is: what it takes, and what
    /// it gives.
    pub(super) fn import_type(&self, sig: &FuncSig) -> (Vec<ValType>, Vec<ValType>) {
        let passing = self.passing(sig, true);
        let mut params = match passing.params {
            Some(_) => vec![self.addr_type()],
            None => (sig.params.iter())
                .flat_map(|(_, ty)| self.val_types(*ty))
                .collect(),
        };
        let results = match passing.result {
            Some(_) => {
                params.push(self.addr_type());
                Vec::new()
            }
            None => self.val_types(sig.ret),
        };
        (params, results)
    }

    /// The address of the return area, which is given memory the first time
    /// anything is passed through it.
    fn return_area(&mut self) -> u64 {
        if let Some(area) = self.return_area {
            return area;
        }
        let area = self.reserve_data(self.return_area_size.into(), RETURN_AREA_ALIGN);
        self.return_area = Some(area);
        area
    }

    /// Lowers function `id`, which the world exports as `export`: one that
    /// calls `target`, taking what the host passes and giving what it
    /// returns as the host takes it.
    pub(super) fn lower_export(&mut self, id: FuncId, target: FuncId, export: &str) -> ir::Func {
        let sig = self.funcs[id.0 as usize].clone();
        let passing = self.passing(&sig, false);
        let addr_type = self.addr_type();
        let mut body = Body::new(self, sig.ret);
        let params = sig.params.iter().filter(|(_, ty)| *ty != Ty::Type);
        let mut args = Value::default();
        // How many locals are what the host passes: those before any that
        // reading them takes.
        let taken = match &passing.params {
            // The host put them in memory, and passes where.
            Some(offsets) => {
                let at = body.push_local("args".to_string(), addr_type);
                for ((_, ty), offset) in params.zip(offsets) {
                    let read = body.load(scalar(addr_type, Expr::Local(at)), *offset, *ty);
                    args.pre.extend(read.pre);
                    args.scalars.extend(read.scalars);
                }
                1
            }
            None => {
                for (name, ty) in params {
                    let leaves = body.ck.val_types(*ty);
                    let locals = body.alloc(name, *ty);
                    let locals = locals.into_iter().map(Expr::Local);
                    args.scalars.extend(leaves.into_iter().zip(locals));
                }
                body.locals.len()
            }
        };
        let (_, value) = body.call_func(target, args);
        let mut stmts = value.pre;
        let results = match passing.result {
            Some(offset) => {
                let area = body.ck.return_area();
                let area = Expr::Const(body.ck.addr_const(area));
                body.store_at(area.clone(), offset, sig.ret, value.scalars, &mut stmts);
                stmts.push(Stmt::Return(vec![area]));
                vec![addr_type]
            }
            None => {
                stmts.push(Stmt::Return(exprs(value.scalars)));
                body.ck.val_types(sig.ret)
            }
        };
        let locals = body.locals;
        ir::Func {
            exports: vec![export.to_string()],
            name: sig.name,
            params: locals[..taken].iter().map(|local| local.ty).collect(),
            results,
            locals,
            body: stmts,
        }
    }
}

impl Body<'_> {
    /// What a call of the import `id` passes for the scalars of its
    /// arguments `scalars`, after `pre`, and where in the return area its
    /// result is written, if it is. Also gives whether the arguments are in
    /// the return area, so that the call is to follow at once: the next
    /// call of any import writes there too.
    pub(super) fn import_args(
        &mut self,
        id: FuncId,
        scalars: Vec<(ValType, Expr)>,
        pre: &mut Vec<Stmt>,
    ) -> (Vec<Expr>, Option<Expr>, bool) {
        let sig = self.ck.funcs[id.0 as usize].clone();
        let passing = self.ck.passing(&sig, true);
        if passing.params.is_none() && passing.result.is_none() {
            return (exprs(scalars), None, false);
        }
        let area = self.ck.return_area();
        let at = |ck: &Checker, offset: u32| Expr::Const(ck.addr_const(area + u64::from(offset)));
        let mut args = match &passing.params {
            Some(offsets) => {
                let params = sig.params.iter().filter(|(_, ty)| *ty != Ty::Type);
                let mut scalars = scalars.into_iter();
                for ((_, ty), offset) in params.zip(offsets) {
                    let leaves = self.ck.val_types(*ty).len();
                    let held = scalars.by_ref().take(leaves).collect();
                    self.store_at(at(self.ck, 0), *offset, *ty, held, pre);
                }
                vec![at(self.ck, 0)]
            }
            None => exprs(scalars),
        };
        let result = passing.result.map(|offset| at(self.ck, offset));
        args.extend(result.clone());
        (args, result, passing.params.is_some())
    }

    /// The result of a call of an import that wrote it at `addr`, a `ty`,
    /// read after `pre` into locals: the next call of any import writes
    /// there too.
    pub(super) fn import_result(
        &mut self,
        addr: Expr,
        ty: Ty,
        pre: &mut Vec<Stmt>,
    ) -> Vec<(ValType, Expr)> {
        let read = self.load(scalar(self.ck.addr_type(), addr), 0, ty);
        pre.extend(read.pre);
        let mut kept = Vec::new();
        for (leaf, expr) in read.scalars {
            let local = self.temp(leaf);
            pre.push(Stmt::SetLocal(local, expr));
            kept.push((leaf, Expr::Local(local)));
        }
        kept
    }

    /// Writes `scalars`, those of a `ty`, at `offset` bytes past `addr`,
    /// after `out`. Each is evaluated once, before any is written.
    fn store_at(
        &mut self,
        addr: Expr,
        offset: u32,
        ty: Ty,
        scalars: Vec<(ValType, Expr)>,
        out: &mut Vec<Stmt>,
    ) {
        let mut held = Vec::new();
        for (leaf, expr) in scalars {
            held.push(match is_simple(&expr) {
                true => expr,
                false => {
                    let local = self.temp(leaf);
                    out.push(Stmt::SetLocal(local, expr));
                    Expr::Local(local)
                }
            });
        }
        let place = Place {
            name: String::new(),
            ty,
            mutable: true,
            behind: None,
            pre: Vec::new(),
            slots: Slots::Memory { addr, offset },
        };
        let cells = self.ck.cells(ty);
        self.store(&place, &cells, held, out);
    }
}

//! Enums: types whose values are a fixed list of named constants of another
//! type. A value is stored as its member's constant, so each use of a member,
//! like `ReturnCode.ok`, builds a fresh copy of it.

use std::collections::HashMap;

use crate::ir::{Const, Expr, Stmt, ValType};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, EnumDecl, ExprKind, Ident, ItemKind};

use super::{
    Body, Checker, EnumId, Item, Label, Prim, TYPE_FIELDS, Ty, TypeErrorKind, Value, Visit, zero,
};

pub(super) struct EnumDef {
    pub(super) name: String,
    pub(super) is_pub: bool,
    /// The type of every member's value. [`Ty::Error`] until resolved.
    pub(super) ty: Ty,
    /// Where the type of the values is written.
    ty_span: Span,
    pub(super) members: Vec<MemberDef>,
    /// Whether the members' values are known. Global initializers and
    /// members of other enums can only use those of earlier enums.
    defined: bool,
}

pub(super) struct MemberDef {
    pub(super) name: String,
    /// One constant per scalar leaf of the enum's type.
    pub(super) value: Vec<Const>,
}

impl Checker {
    /// Registers `decl`'s name and the names of its members, whose values
    /// are defined later.
    pub(super) fn declare_enum(&mut self, decl: &EnumDecl, is_pub: bool) -> EnumId {
        let members = decl
            .members
            .iter()
            .map(|member| MemberDef {
                name: member.name.name.clone(),
                value: Vec::new(),
            })
            .collect();
        self.enums.push(EnumDef {
            name: decl.name.name.clone(),
            is_pub,
            ty: Ty::Error,
            ty_span: decl.ty.span,
            members,
            defined: false,
        });
        EnumId(self.enums.len() as u32 - 1)
    }

    /// Resolves the type of every enum's values, then reports enums that
    /// contain themselves and cuts each cycle by giving the offending enum
    /// the error type. Cycles through a struct are left to the struct.
    pub(super) fn resolve_enums(&mut self, program: &Program) {
        for (id, decl) in enum_decls(program).enumerate() {
            self.module = decl.name.span.file;
            self.enums[id].ty = self.resolve_ty(&decl.ty);
        }
        let mut visits = vec![Visit::New; self.enums.len()];
        for id in 0..self.enums.len() {
            self.break_enum_cycles(id, &mut visits);
        }
    }

    fn break_enum_cycles(&mut self, id: usize, visits: &mut [Visit]) {
        if visits[id] != Visit::New {
            return;
        }
        visits[id] = Visit::Active;
        let mut children = Vec::new();
        self.push_inline_enums(self.enums[id].ty, &mut children);
        for EnumId(child) in children {
            match visits[child as usize] {
                Visit::Active => {
                    let def = &mut self.enums[id];
                    def.ty = Ty::Error;
                    let (kind, span) =
                        (TypeErrorKind::RecursiveEnum(def.name.clone()), def.ty_span);
                    self.error(kind, span);
                    break;
                }
                Visit::New => self.break_enum_cycles(child as usize, visits),
                Visit::Done => {}
            }
        }
        visits[id] = Visit::Done;
    }

    /// The enums that a value of type `ty` holds directly, rather than in a
    /// struct or behind a pointer.
    fn push_inline_enums(&self, ty: Ty, out: &mut Vec<EnumId>) {
        match ty {
            Ty::Enum(id) => out.push(id),
            Ty::Tuple(id) => {
                for elem in &self.tuples[id.0 as usize] {
                    self.push_inline_enums(*elem, out);
                }
            }
            _ => {}
        }
    }

    /// Reports an enum whose values' type has a pointer to something that
    /// can't be stored in memory, which `resolve_ty` couldn't know before
    /// every struct was defined.
    pub(super) fn check_enum_pointers(&mut self) {
        for id in 0..self.enums.len() {
            if let Some(ty) = self.unstorable_pointee(self.enums[id].ty) {
                let kind = TypeErrorKind::NotStorable(self.ty_name(ty));
                self.error(kind, self.enums[id].ty_span);
                self.enums[id].ty = Ty::Error;
            }
        }
    }

    /// Checks and folds the values of enum `id`'s members. An integer
    /// member without one is the previous member's value plus one, or zero
    /// if it's first.
    pub(super) fn define_members(&mut self, id: EnumId, decl: &EnumDecl) {
        let ty = self.enum_ty(id);
        let int = match ty {
            Ty::Prim(prim) if prim.is_int() => Some(prim),
            _ => None,
        };
        // The value the next member counts up to, and each value so far by
        // its bits, `None` where it failed to check.
        let mut next = Some(0);
        let mut bits: Vec<Option<Vec<u64>>> = Vec::new();
        for (i, member) in decl.members.iter().enumerate() {
            let name = &member.name;
            let value = if decl.members[..i].iter().any(|m| m.name.name == name.name) {
                self.error(TypeErrorKind::DuplicateMember(name.name.clone()), name.span);
                None
            } else {
                self.member_value(ty, int, next, member)
            };
            next = match (int, &value) {
                (Some(prim), Some(value)) => Some(const_int(prim, value[0]) + 1),
                _ => None,
            };
            let value_bits = value
                .as_ref()
                .map(|v| v.iter().map(|c| const_bits(*c)).collect());
            if let Some(same) = value_bits
                .as_ref()
                .and_then(|b| bits.iter().position(|prev| prev.as_ref() == Some(b)))
            {
                let kind = TypeErrorKind::DuplicateValue {
                    member: name.name.clone(),
                    same_as: decl.members[same].name.name.clone(),
                };
                self.error(kind, member.span);
            }
            bits.push(value_bits);
            let zeros = || self.val_types(ty).into_iter().map(zero).collect();
            self.enums[id.0 as usize].members[i].value = value.unwrap_or_else(zeros);
        }
        self.enums[id.0 as usize].defined = true;
    }

    /// The folded value of `member` of an enum whose values have type `ty`,
    /// which counts up to `next` if it's an integer. `None` after reporting
    /// an error, or if `ty` is the error type.
    fn member_value(
        &mut self,
        ty: Ty,
        int: Option<Prim>,
        next: Option<i128>,
        member: &parse::Member,
    ) -> Option<Vec<Const>> {
        let name = &member.name;
        let Some(expr) = &member.value else {
            let prim = match int {
                Some(prim) => prim,
                None if ty == Ty::Error => return None,
                None => {
                    self.error(TypeErrorKind::MissingValue(name.name.clone()), name.span);
                    return None;
                }
            };
            // Counting from a member whose value is unknown.
            let n = next?;
            if n > prim.range().1 {
                let kind = TypeErrorKind::MemberOutOfRange {
                    member: name.name.clone(),
                    ty: prim.name().to_string(),
                };
                self.error(kind, name.span);
                return None;
            }
            return Some(vec![int_const(prim, n)]);
        };
        let errors = self.errors.len();
        let mut body = Body::new(self, Ty::Unit);
        body.global = true;
        let value = body.check(expr, ty);
        let consts = self.fold_value(&value, expr.span);
        (self.errors.len() == errors && ty != Ty::Error).then_some(consts)
    }

    /// The type of enum `id`'s values.
    pub(super) fn enum_ty(&self, id: EnumId) -> Ty {
        self.enums[id.0 as usize].ty
    }
}

impl Body<'_> {
    /// The enum `expr` names, if it's the name of one that no variable
    /// shadows, or of one in a module, as `module.Enum`.
    pub(super) fn enum_name(&self, expr: &parse::Expr) -> Option<EnumId> {
        match (self.named(expr), &expr.kind) {
            (Some(Item::Enum(id)), _) => Some(id),
            (None, ExprKind::Name(name)) if self.lookup(name).is_none() => {
                match self.ck.type_param(name) {
                    Some(Ty::Enum(id)) => Some(id),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// `E.field`, where `E` names enum `id`: the member `field`, or else
    /// `None` for a field of `type`, which `E` is as a value.
    pub(super) fn enum_member(&mut self, id: EnumId, field: &Ident) -> Option<(Ty, Value)> {
        let def = &self.ck.enums[id.0 as usize];
        let Some(member) = def.members.iter().find(|m| m.name == field.name) else {
            if TYPE_FIELDS.contains(&field.name.as_str()) {
                return None;
            }
            let kind = TypeErrorKind::NoMember {
                ty: def.name.clone(),
                member: field.name.clone(),
            };
            self.error(kind, field.span);
            return Some((Ty::Error, Value::default()));
        };
        // Only reachable from an earlier global's or member's initializer.
        if !def.defined {
            self.error(TypeErrorKind::NotConstant, field.span);
            return Some((Ty::Error, Value::default()));
        }
        let consts = member.value.iter().map(|c| Expr::Const(*c)).collect();
        Some((Ty::Enum(id), self.scalars(Ty::Enum(id), consts)))
    }

    /// `for var in E`, where `E` names enum `id`: a copy of `body` per
    /// member, in declaration order, after setting `var` to it. Each copy is
    /// in a block that `continue` leaves, and they're all in one that `break`
    /// leaves.
    pub(super) fn unrolled_loop(&mut self, id: EnumId, var: &Ident, body: &parse::Block) -> Stmt {
        let ty = Ty::Enum(id);
        let slots = self.alloc(&var.name, ty);
        self.scopes.push(HashMap::new());
        self.bind(&var.name, ty, false, slots.clone());
        self.labels.push(Label::Break);
        let body = self.labelled(Label::Continue, body);
        self.labels.pop();
        self.scopes.pop();
        let copies = self.ck.enums[id.0 as usize]
            .members
            .iter()
            .map(|member| {
                let sets = slots.iter().zip(&member.value);
                let mut copy: Vec<_> = sets
                    .map(|(slot, c)| Stmt::SetLocal(*slot, Expr::Const(*c)))
                    .collect();
                copy.extend(body.iter().cloned());
                Stmt::Block(copy)
            })
            .collect();
        Stmt::Block(copies)
    }
}

/// Every enum declaration, in [`EnumId`] order.
fn enum_decls(program: &Program) -> impl Iterator<Item = &EnumDecl> {
    program.items.iter().filter_map(|item| match &item.kind {
        ItemKind::Enum(decl) => Some(decl),
        _ => None,
    })
}

/// An integer constant of type `prim` as a number.
fn const_int(prim: Prim, c: Const) -> i128 {
    match c {
        Const::I32(x) if prim.is_signed() => x.into(),
        Const::I32(x) => (x as u32).into(),
        Const::I64(x) if prim.is_signed() => x.into(),
        Const::I64(x) => (x as u64).into(),
        Const::F32(_) | Const::F64(_) => unreachable!("integers are never floats"),
    }
}

/// `n` as a constant of the integer type `prim`, which it fits in.
fn int_const(prim: Prim, n: i128) -> Const {
    match prim.val_type() {
        ValType::I64 => Const::I64(n as i64),
        _ => Const::I32(n as i32),
    }
}

/// The bits of a constant, which tell apart floats that compare equal, like
/// `0.0` and `-0.0`.
fn const_bits(c: Const) -> u64 {
    match c {
        Const::I32(x) => x as u32 as u64,
        Const::I64(x) => x as u64,
        Const::F32(x) => x.to_bits().into(),
        Const::F64(x) => x.to_bits(),
    }
}

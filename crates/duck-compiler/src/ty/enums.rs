//! Enums: types whose values are a fixed list of named constants of another
//! type. A value is stored as its member's constant, so each use of a member,
//! like `ReturnCode.ok`, builds a fresh copy of it.

use std::collections::HashMap;
use std::mem;

use crate::file::FileId;
use crate::ir::{Const, Expr, Stmt, ValType};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, EnumDecl, ExprKind, Ident, ItemKind};

use super::{
    Body, Checker, EnumId, Item, Label, Prim, TYPE_FIELDS, Ty, TypeErrorKind, Value, Visit, zero,
};

pub(super) struct EnumDef {
    pub(super) name: String,
    /// The module that declares it.
    pub(super) module: FileId,
    /// The item of the program that declares it.
    pub(super) item: usize,
    pub(super) is_pub: bool,
    /// The type of every member's value. [`Ty::Error`] until resolved.
    pub(super) ty: Ty,
    /// Where the type of the values is written.
    ty_span: Span,
    /// The enum that each of its `use` lines names, in order, of which it
    /// [starts as](Checker::starts) the first. The error type for one that
    /// failed to resolve.
    pub(super) uses: Vec<Ty>,
    /// Those that it uses of other enums and then its own, in the order
    /// they are written. Empty until [`Checker::resolve_enums`] lists them.
    pub(super) members: Vec<MemberDef>,
}

pub(super) struct MemberDef {
    pub(super) name: String,
    /// One constant per scalar leaf of the enum's type.
    pub(super) value: Vec<Const>,
    /// Whether `value` is its value, rather than zeros in place of one that
    /// failed to check or isn't folded yet.
    known: bool,
    /// Whether it is given no value, so that an integer counts up to it.
    counts: bool,
    /// The member of another enum that a `use` makes it one of, if any.
    used: Option<(EnumId, usize)>,
    /// Where it is written: the `use`, for one that a `use` makes a member.
    span: Span,
}

impl Checker {
    /// Registers the name of `decl`, which is item `item` of the program.
    /// Its members are listed later, and their values defined after that.
    pub(super) fn declare_enum(&mut self, decl: &EnumDecl, item: usize, is_pub: bool) -> EnumId {
        self.enums.push(EnumDef {
            name: decl.name.name.clone(),
            module: self.module,
            item,
            is_pub,
            ty: Ty::Error,
            ty_span: decl.ty.span,
            uses: Vec::new(),
            members: Vec::new(),
        });
        EnumId(self.enums.len() as u32 - 1)
    }

    /// Resolves the type of every enum's values, then reports enums that
    /// contain themselves and cuts each cycle by giving the offending enum
    /// the error type. Cycles through a struct are left to the struct. Then
    /// lists every enum's members.
    pub(super) fn resolve_enums(&mut self, program: &Program) {
        for (id, decl) in enum_decls(program).enumerate() {
            self.module = decl.name.span.file;
            self.enums[id].ty = self.resolve_ty(&decl.ty);
        }
        let mut visits = vec![Visit::New; self.enums.len()];
        for id in 0..self.enums.len() {
            self.break_enum_cycles(id, &mut visits);
        }
        let mut visits = vec![Visit::New; self.enums.len()];
        for id in 0..self.enums.len() {
            self.list_members(program, id, &mut visits);
        }
    }

    /// Lists the members of enum `id`, unless it has them, or is being
    /// given them, as one that a `use` leads back to is. `visits` is how far
    /// each enum is. Those it uses are given theirs first.
    fn list_members(&mut self, program: &Program, id: usize, visits: &mut [Visit]) {
        if visits[id] != Visit::New {
            return;
        }
        visits[id] = Visit::Active;
        let ItemKind::Enum(decl) = &program.items[self.enums[id].item].kind else {
            unreachable!("an enum declares it")
        };
        // It may be an enum that another, being listed, uses.
        let module = mem::replace(&mut self.module, self.enums[id].module);
        let mut members: Vec<MemberDef> = Vec::new();
        for entry in &decl.entries {
            match entry {
                // One named as another is reported with its value.
                parse::Entry::Own(member) => members.push(MemberDef {
                    name: member.name.name.clone(),
                    value: Vec::new(),
                    known: false,
                    counts: member.value.is_none(),
                    used: None,
                    span: member.span,
                }),
                parse::Entry::Use(used) => {
                    let (ty, used_members) = self.used_members(program, id, used, visits);
                    self.enums[id].uses.push(ty);
                    for member in used_members {
                        if members.iter().any(|m| m.name == member.name) {
                            self.error(TypeErrorKind::DuplicateMember(member.name), used.span);
                            continue;
                        }
                        members.push(member);
                    }
                }
            }
        }
        self.module = module;
        self.enums[id].members = members;
        visits[id] = Visit::Done;
    }

    /// The enum that `use written` names in enum `id`, and the members it
    /// gives it: those of that enum, whose values have the type that its
    /// own do, each written where the `use` is. The error type and no
    /// members after reporting an error.
    fn used_members(
        &mut self,
        program: &Program,
        id: usize,
        written: &parse::Type,
        visits: &mut [Visit],
    ) -> (Ty, Vec<MemberDef>) {
        let failed = (Ty::Error, Vec::new());
        let ty = self.resolve_ty(written);
        let used = match ty {
            Ty::Enum(used) => used,
            Ty::Error => return failed,
            _ => {
                let (within, takes, ty) = ("an enum", "an enum", self.ty_name(ty));
                let kind = TypeErrorKind::UseOfOther { within, takes, ty };
                self.error(kind, written.span);
                return failed;
            }
        };
        let index = used.0 as usize;
        if visits[index] == Visit::Active {
            let kind = TypeErrorKind::RecursiveUse(self.ty_name(ty));
            self.error(kind, written.span);
            return failed;
        }
        self.list_members(program, index, visits);
        let (expected, found) = (self.enums[id].ty, self.enums[index].ty);
        if expected != found && expected != Ty::Error && found != Ty::Error {
            let kind = TypeErrorKind::UseOfValues {
                name: self.ty_name(ty),
                expected: self.ty_name(expected),
                found: self.ty_name(found),
            };
            self.error(kind, written.span);
            return failed;
        }
        let members = &self.enums[index].members;
        let firsts = (0..members.len())
            .filter(|i| !members[..*i].iter().any(|m| m.name == members[*i].name));
        let members = firsts
            .map(|i| MemberDef {
                name: members[i].name.clone(),
                value: Vec::new(),
                known: false,
                counts: members[i].counts,
                used: Some((used, i)),
                span: written.span,
            })
            .collect();
        (ty, members)
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
    /// if it's first, and so is one that a `use` makes a member, which
    /// otherwise has the value it was given where it is declared.
    pub(super) fn define_members(&mut self, program: &Program, id: EnumId, decl: &EnumDecl) {
        let ty = self.enum_ty(id);
        let int = match ty {
            Ty::Prim(prim) if prim.is_int() => Some(prim),
            _ => None,
        };
        // The value the next member counts up to, and each value so far by
        // its bits, `None` where it failed to check.
        let mut next = Some(0);
        let mut bits: Vec<Option<Vec<u64>>> = Vec::new();
        let mut written = decl.entries.iter().filter_map(parse::Entry::own);
        for i in 0..self.enums[id.0 as usize].members.len() {
            let members = &self.enums[id.0 as usize].members;
            let (used, counts, span) = (members[i].used, members[i].counts, members[i].span);
            let own = match used {
                Some(_) => None,
                None => written.next(),
            };
            let name = Ident {
                name: members[i].name.clone(),
                span: own.map_or(span, |member| member.name.span),
            };
            let value = if members[..i].iter().any(|m| m.name == name.name) {
                self.error(TypeErrorKind::DuplicateMember(name.name.clone()), name.span);
                None
            } else {
                match (own.and_then(|member| member.value.as_ref()), used) {
                    (Some(expr), _) => self.member_value(program, ty, expr),
                    (None, Some((from, index))) if !counts => {
                        self.used_value(program, from, index, span)
                    }
                    // Reported where it is declared.
                    (None, Some(_)) if int.is_none() => None,
                    (None, _) => self.counted_value(ty, int, next, &name),
                }
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
                    same_as: self.enums[id.0 as usize].members[same].name.clone(),
                };
                self.error(kind, span);
            }
            bits.push(value_bits);
            let known = value.is_some();
            let zeros = || self.val_types(ty).into_iter().map(zero).collect();
            let value = value.unwrap_or_else(zeros);
            let member = &mut self.enums[id.0 as usize].members[i];
            (member.known, member.value) = (known, value);
        }
    }

    /// The value of the member `name`, which is given none, of an enum
    /// whose values have type `ty`: `next`, which it counts up to if `ty` is
    /// the integer `int`. `None` after reporting an error, or if `ty` is the
    /// error type.
    fn counted_value(
        &mut self,
        ty: Ty,
        int: Option<Prim>,
        next: Option<i128>,
        name: &Ident,
    ) -> Option<Vec<Const>> {
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
        if n > self.fixed(prim).range().1 {
            let kind = TypeErrorKind::MemberOutOfRange {
                member: name.name.clone(),
                ty: prim.name().to_string(),
            };
            self.error(kind, name.span);
            return None;
        }
        Some(vec![int_const(self.fixed(prim), n)])
    }

    /// The value of member `index` of enum `from`, which the `use` at `span`
    /// makes a member of another, once the values of `from` are folded.
    /// `None` after reporting an error, or if the value failed to check.
    fn used_value(
        &mut self,
        program: &Program,
        from: EnumId,
        index: usize,
        span: Span,
    ) -> Option<Vec<Const>> {
        let def = &self.enums[from.0 as usize];
        let (item, name) = (def.item, def.name.clone());
        if !self.folded(Some(program), item, &name, span) {
            return None;
        }
        let member = &self.enums[from.0 as usize].members[index];
        member.known.then(|| member.value.clone())
    }

    /// The folded value of `expr`, which a member of an enum whose values
    /// have type `ty` is given. `None` after reporting an error, or if `ty`
    /// is the error type.
    fn member_value(
        &mut self,
        program: &Program,
        ty: Ty,
        expr: &parse::Expr,
    ) -> Option<Vec<Const>> {
        let errors = self.errors.len();
        let mut body = Body::new(self, Ty::Unit);
        body.global = Some(program);
        let value = body.check(expr, ty);
        let consts = body.evaluate(value, expr.span);
        consts.filter(|_| self.errors.len() == errors && ty != Ty::Error)
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
            (Some(Item::Alias(id)), _) => match self.ck.aliased(id) {
                Ty::Enum(id) => Some(id),
                _ => None,
            },
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
        let (name, item) = (def.name.clone(), def.item);
        let Some(index) = def.members.iter().position(|m| m.name == field.name) else {
            if TYPE_FIELDS.contains(&field.name.as_str()) {
                return None;
            }
            let kind = TypeErrorKind::NoMember {
                ty: name,
                member: field.name.clone(),
            };
            self.error(kind, field.span);
            return Some((Ty::Error, Value::default()));
        };
        if !self.folded(item, &name, field.span) {
            return Some((Ty::Error, Value::default()));
        }
        let member = &self.ck.enums[id.0 as usize].members[index];
        let consts = member.value.iter().map(|c| Expr::Const(*c)).collect();
        Some((Ty::Enum(id), self.scalars(Ty::Enum(id), consts)))
    }

    /// `for var in E`, where `E` names enum `id`: a copy of `body` per
    /// member, in declaration order, after setting `var` to it. Each copy is
    /// in a block that `continue` leaves, and they're all in one that `break`
    /// leaves.
    pub(super) fn unrolled_loop(&mut self, id: EnumId, var: &Ident, body: &parse::Block) -> Stmt {
        let ty = Ty::Enum(id);
        self.ck.record(var.span, ty);
        let slots = self.alloc(&var.name, ty);
        self.scopes.push(HashMap::new());
        self.bind(&var.name, ty, false, slots.clone());
        self.labels.push(Label::Break);
        let (body, _) = self.maybe(|lowered| lowered.labelled(Label::Continue, body));
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

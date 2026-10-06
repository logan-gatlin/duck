//! `match`: the patterns its arms test a value against and bind names in,
//! and whether the arms cover every value, each matching some that those
//! before it don't.

use std::collections::HashMap;

use crate::ir::{BinOp as IrBinOp, Const, Expr, LocalId, Stmt, ValType};
use crate::lex::Span;
use crate::parse::{self, Arm, BinOp, Ident, Pattern, PatternKind};

use super::{
    Body, Checker, Label, Need, StructId, TUPLE, Ty, TypeErrorKind, Value, binary, single,
};

/// A pattern as the values it matches: any, or those built one way from
/// parts that match patterns in turn.
#[derive(Clone)]
enum Pat {
    Any,
    Built(Ctor, Vec<Pat>),
}

/// One of the ways a value of a type is built, which a pattern tells apart.
#[derive(Clone, PartialEq)]
enum Ctor {
    /// A union's variant, by position, from the value it holds, if any.
    Variant(usize),
    /// An enum's member, by position.
    Member(usize),
    /// A tuple, from its elements: the one way it's built.
    Tuple,
}

/// The pattern of an arm, checked against the type of the value.
#[derive(Default)]
struct Case<'p> {
    /// What a value passes to match, each tested only if those before it
    /// passed.
    tests: Vec<Expr>,
    /// The names the pattern binds, with the type and the locals of the
    /// part of the value each is.
    names: Vec<(&'p str, Ty, Vec<LocalId>)>,
    /// Whether the pattern has an error, so that what it matches is unknown.
    failed: bool,
}

impl Checker {
    /// The types of the parts a `ty` is built from by `ctor`.
    fn part_tys(&self, ty: Ty, ctor: &Ctor) -> Vec<Ty> {
        match (ctor, self.union_id(ty)) {
            (Ctor::Variant(index), Some(id)) => {
                let variant = &self.structs[id.0 as usize].fields[*index];
                match variant.bare {
                    true => Vec::new(),
                    false => vec![variant.ty],
                }
            }
            (Ctor::Tuple, _) => self.members(ty),
            _ => Vec::new(),
        }
    }

    /// Every way a `ty` is built, with the types of the parts, if patterns
    /// tell them apart and there are finitely many.
    fn ctors(&self, ty: Ty) -> Option<Vec<(Ctor, Vec<Ty>)>> {
        let ctors: Vec<_> = match (ty, self.union_id(ty)) {
            (_, Some(id)) => {
                let variants = 0..self.structs[id.0 as usize].fields.len();
                variants.map(Ctor::Variant).collect()
            }
            (Ty::Enum(id), _) => {
                let members = 0..self.enums[id.0 as usize].members.len();
                members.map(Ctor::Member).collect()
            }
            (Ty::Tuple(_) | Ty::Unit, _) => vec![Ctor::Tuple],
            _ => return None,
        };
        let parts = |ctor: Ctor| {
            let part_tys = self.part_tys(ty, &ctor);
            (ctor, part_tys)
        };
        Some(ctors.into_iter().map(parts).collect())
    }

    /// Every way a `ty` is built, as [`Self::ctors`] has them, if each
    /// starts one of `rows`: the rows tell every value of the type apart.
    fn complete(&self, rows: &[Vec<Pat>], ty: Ty) -> Option<Vec<(Ctor, Vec<Ty>)>> {
        let ctors = self.ctors(ty)?;
        let starts = |ctor: &Ctor| {
            let mut heads = rows.iter().map(|row| &row[0]);
            heads.any(|head| matches!(head, Pat::Built(built, _) if built == ctor))
        };
        ctors.iter().all(|(ctor, _)| starts(ctor)).then_some(ctors)
    }

    /// Whether `row`, a pattern for each of `tys`, matches values that none
    /// of `rows` does.
    fn useful(&self, rows: &[Vec<Pat>], row: &[Pat], tys: &[Ty]) -> bool {
        let Some((head, rest)) = row.split_first() else {
            return rows.is_empty();
        };
        // Whether the row does once it's known to start with `ctor`.
        let built = |ctor: &Ctor, parts: &[Pat], part_tys: Vec<Ty>| {
            let rows = specialize(rows, ctor, parts.len());
            let row: Vec<_> = parts.iter().chain(rest).cloned().collect();
            let tys: Vec<_> = part_tys
                .into_iter()
                .chain(tys[1..].iter().copied())
                .collect();
            self.useful(&rows, &row, &tys)
        };
        match head {
            Pat::Built(ctor, parts) => built(ctor, parts, self.part_tys(tys[0], ctor)),
            Pat::Any => match self.complete(rows, tys[0]) {
                Some(ctors) => ctors.into_iter().any(|(ctor, part_tys)| {
                    let parts = vec![Pat::Any; part_tys.len()];
                    built(&ctor, &parts, part_tys)
                }),
                None => self.useful(&rest_of_any(rows), rest, &tys[1..]),
            },
        }
    }

    /// A pattern for each of `tys` that together match values none of
    /// `rows` does, if there are any.
    fn uncovered(&self, rows: &[Vec<Pat>], tys: &[Ty]) -> Option<Vec<Pat>> {
        let Some((ty, rest)) = tys.split_first() else {
            return rows.is_empty().then(Vec::new);
        };
        let Some(ctors) = self.complete(rows, *ty) else {
            let mut missing = self.uncovered(&rest_of_any(rows), rest)?;
            // One of the ways that start no row, if the type's are known.
            let starts = |ctor: &Ctor| {
                let mut heads = rows.iter().map(|row| &row[0]);
                heads.any(|head| matches!(head, Pat::Built(built, _) if built == ctor))
            };
            let mut ctors = self.ctors(*ty).into_iter().flatten();
            let head = match ctors.find(|(ctor, _)| !starts(ctor)) {
                Some((ctor, part_tys)) => Pat::Built(ctor, vec![Pat::Any; part_tys.len()]),
                None => Pat::Any,
            };
            missing.insert(0, head);
            return Some(missing);
        };
        ctors.into_iter().find_map(|(ctor, part_tys)| {
            let rows = specialize(rows, &ctor, part_tys.len());
            let tys: Vec<_> = part_tys.iter().chain(rest).copied().collect();
            let mut parts = self.uncovered(&rows, &tys)?;
            let mut missing = parts.split_off(part_tys.len());
            missing.insert(0, Pat::Built(ctor, parts));
            Some(missing)
        })
    }

    /// `pat`, which matches values of type `ty`, as it would be written.
    fn pat_text(&self, pat: &Pat, ty: Ty) -> String {
        let Pat::Built(ctor, parts) = pat else {
            return "_".to_string();
        };
        let part_tys = self.part_tys(ty, ctor);
        let parts = parts.iter().zip(part_tys);
        let parts: Vec<_> = parts.map(|(part, ty)| self.pat_text(part, ty)).collect();
        match (ctor, ty, self.union_id(ty)) {
            (Ctor::Variant(index), _, Some(id)) => {
                let name = &self.structs[id.0 as usize].fields[*index].name;
                match parts.is_empty() {
                    true => format!(".{name}"),
                    false => format!(".{name}({})", parts.join(", ")),
                }
            }
            (Ctor::Member(index), Ty::Enum(id), _) => {
                format!(".{}", self.enums[id.0 as usize].members[*index].name)
            }
            _ => format!("({})", parts.join(", ")),
        }
    }
}

impl Body<'_> {
    /// `match value:`, which runs the first of `arms` whose pattern the
    /// value matches, with the names the pattern binds. The value is
    /// evaluated once, and traps if no arm matches it, as only one that was
    /// never built here can.
    pub(super) fn match_stmt(
        &mut self,
        stmt: &parse::Stmt,
        value: &parse::Expr,
        arms: &[Arm],
        out: &mut Vec<Stmt>,
    ) {
        let (ty, mut subject) = match self.need(stmt) {
            Need::Check => self.expr(value, None),
            Need::Bind(ty) => self.unchecked(ty, stmt.span),
            Need::Skip => (Ty::Error, Value::default()),
        };
        // Held in temporaries that the arms test and their names read, so
        // nothing an arm does changes what its names are.
        self.spill(&mut subject, |_| false);
        out.extend(subject.pre);
        let locals = subject
            .scalars
            .iter()
            .filter_map(|(_, scalar)| match scalar {
                Expr::Local(local) => Some(*local),
                _ => None,
            });
        let locals: Vec<_> = locals.collect();
        // Only a mistyped value has other scalars than its type's.
        let matched = match locals.len() == self.ck.val_types(ty).len() {
            true => ty,
            false => Ty::Error,
        };
        let mut cases = Vec::new();
        let mut rows = Vec::new();
        for arm in arms {
            let mut case = Case::default();
            rows.push(vec![self.pattern(
                &arm.pattern,
                matched,
                &locals,
                &mut case,
            )]);
            cases.push(case);
        }
        self.record(stmt, Some(ty));
        if matched != Ty::Error && cases.iter().all(|case| !case.failed) {
            self.check_arms(arms, &rows, matched, value.span);
        }
        // The arms are in a block that each leaves once it has run.
        self.labels.push(Label::Other);
        let mut block = Vec::new();
        let mut ended = false;
        for (arm, case) in arms.iter().zip(cases) {
            self.scopes.push(HashMap::new());
            for (name, ty, slots) in case.names {
                self.bind(name, ty, false, slots);
            }
            let tests = case.tests.into_iter().rev();
            let test = tests.reduce(|rest, test| Expr::If {
                ty: ValType::I32,
                cond: Box::new(test),
                then_expr: Box::new(rest),
                else_expr: Box::new(Expr::Const(Const::I32(0))),
            });
            let mut body = match test {
                Some(_) => self.labelled(Label::Other, &arm.body),
                None => self.block(&arm.body),
            };
            self.scopes.pop();
            // An arm after one that matches every value is never reached.
            if ended {
                continue;
            }
            let Some(cond) = test else {
                block.extend(body);
                ended = true;
                continue;
            };
            let leaves = matches!(
                body.last(),
                Some(Stmt::Return(_) | Stmt::Unreachable | Stmt::Br(_))
            );
            if !leaves {
                body.push(Stmt::Br(1));
            }
            block.push(Stmt::If {
                cond,
                then_body: body,
                else_body: Vec::new(),
            });
        }
        if !ended {
            block.push(Stmt::Unreachable);
        }
        self.labels.pop();
        out.push(Stmt::Block(block));
    }

    /// Reports each of `arms` that matches no value those before it don't,
    /// and values of type `ty` that none matches, at `span`. `rows` holds
    /// the pattern of each arm.
    fn check_arms(&mut self, arms: &[Arm], rows: &[Vec<Pat>], ty: Ty, span: Span) {
        for (i, arm) in arms.iter().enumerate() {
            if !self.ck.useful(&rows[..i], &rows[i], &[ty]) {
                self.error(TypeErrorKind::UnreachableArm, arm.pattern.span);
            }
        }
        if let Some(missing) = self.ck.uncovered(rows, &[ty]) {
            let pattern = self.ck.pat_text(&missing[0], ty);
            self.error(TypeErrorKind::NonExhaustive(pattern), span);
        }
    }

    /// Checks `pattern` against a value of type `ty` held in the locals
    /// `subject`, adding the tests the value passes to match it and the
    /// names it binds to `case`. Returns what it matches.
    fn pattern<'p>(
        &mut self,
        pattern: &'p Pattern,
        ty: Ty,
        subject: &[LocalId],
        case: &mut Case<'p>,
    ) -> Pat {
        match &pattern.kind {
            PatternKind::Name(name) => {
                if case.names.iter().any(|(bound, ..)| bound == name) {
                    let kind = TypeErrorKind::DuplicateBinding(name.clone());
                    self.error(kind, pattern.span);
                    return Pat::Any;
                }
                // The temporaries are read under the name, so they take it.
                let leaves = self.ck.leaves(ty, name);
                for (local, (leaf, _)) in subject.iter().zip(leaves) {
                    self.name_temp(*local, leaf);
                }
                case.names.push((name, ty, subject.to_vec()));
                Pat::Any
            }
            PatternKind::Discard => Pat::Any,
            PatternKind::Tuple(elems) => {
                let members = match ty {
                    Ty::Tuple(id) if self.ck.tuples[id.0 as usize].len() == elems.len() => {
                        self.ck.members(ty)
                    }
                    Ty::Unit if elems.is_empty() => Vec::new(),
                    _ => {
                        if ty != Ty::Error {
                            let kind = TypeErrorKind::Mismatch {
                                expected: format!("{TUPLE}({})", vec!["_"; elems.len()].join(", ")),
                                found: self.ck.ty_name(ty),
                            };
                            self.error(kind, pattern.span);
                        }
                        return self.failed(pattern, case);
                    }
                };
                let mut start = 0;
                let mut parts = Vec::new();
                for (elem, member) in elems.iter().zip(members) {
                    let end = start + self.ck.val_types(member).len();
                    parts.push(self.pattern(elem, member, &subject[start..end], case));
                    start = end;
                }
                Pat::Built(Ctor::Tuple, parts)
            }
            PatternKind::Variant(name, holds) => {
                let holds = holds.as_deref();
                let built = match (ty, self.ck.union_id(ty)) {
                    (_, Some(id)) => self.variant_pattern(id, name, holds, subject, case),
                    (Ty::Enum(_), _) => self.member_pattern(ty, name, holds, subject, case),
                    (Ty::Error, _) => None,
                    _ => {
                        let kind = TypeErrorKind::NoVariant {
                            ty: self.ck.ty_name(ty),
                            variant: name.name.clone(),
                        };
                        self.error(kind, name.span);
                        None
                    }
                };
                built.unwrap_or_else(|| self.failed(pattern, case))
            }
        }
    }

    /// `.name` or `.name(holds)` against a value of union `id` held in the
    /// locals `subject`: the variant `name`, whose value matches `holds`.
    /// `None` after reporting an error.
    fn variant_pattern<'p>(
        &mut self,
        id: StructId,
        name: &Ident,
        holds: Option<&'p Pattern>,
        subject: &[LocalId],
        case: &mut Case<'p>,
    ) -> Option<Pat> {
        let def = &self.ck.structs[id.0 as usize];
        let Some(index) = def.fields.iter().position(|v| v.name == name.name) else {
            let kind = TypeErrorKind::NoVariant {
                ty: def.name.clone(),
                variant: name.name.clone(),
            };
            self.error(kind, name.span);
            return None;
        };
        let (held, bare) = (def.fields[index].ty, def.fields[index].bare);
        if bare != holds.is_none() {
            let variant = name.name.clone();
            let kind = match bare {
                true => TypeErrorKind::VariantTakesNothing(variant),
                false => TypeErrorKind::VariantNeedsValue {
                    variant,
                    ty: self.ck.ty_name(held),
                },
            };
            self.error(kind, name.span);
            return None;
        }
        let tag = Expr::Const(Const::I32(index as i32));
        let is_variant = binary(ValType::I32, IrBinOp::Eq, Expr::Local(subject[0]), tag);
        case.tests.push(is_variant);
        let leaves = &subject[self.ck.variant_leaves(id, index)];
        let parts = holds.map(|holds| self.pattern(holds, held, leaves, case));
        Some(Pat::Built(
            Ctor::Variant(index),
            parts.into_iter().collect(),
        ))
    }

    /// `.name` against a value of the enum `ty` held in the locals
    /// `subject`: the member `name`. `None` after reporting an error, as
    /// `.name(holds)` is one.
    fn member_pattern(
        &mut self,
        ty: Ty,
        name: &Ident,
        holds: Option<&Pattern>,
        subject: &[LocalId],
        case: &mut Case,
    ) -> Option<Pat> {
        let Ty::Enum(id) = ty else {
            unreachable!("only enums have members")
        };
        let members = &self.ck.enums[id.0 as usize].members;
        let index = members.iter().position(|m| m.name == name.name);
        if index.is_some() && holds.is_some() {
            let kind = TypeErrorKind::NotCallable(format!(".{}", name.name));
            self.error(kind, name.span);
            return None;
        }
        let member = match self.enum_member(id, name) {
            Some((Ty::Error, _)) => return None,
            Some((_, member)) => member,
            // A field of the enum as a `type`.
            None => {
                let kind = TypeErrorKind::NoMember {
                    ty: self.ck.ty_name(ty),
                    member: name.name.clone(),
                };
                self.error(kind, name.span);
                return None;
            }
        };
        let locals = subject.iter().map(|local| Expr::Local(*local));
        let value = self.scalars(ty, locals.collect());
        case.tests
            .push(single(self.compare(BinOp::Eq, ty, value, member)));
        Some(Pat::Built(Ctor::Member(index?), Vec::new()))
    }

    /// Marks `case` as having an error in `pattern`, which is reported, and
    /// gives the names in the patterns within it the error type, so that
    /// what uses them isn't reported too.
    fn failed<'p>(&mut self, pattern: &'p Pattern, case: &mut Case<'p>) -> Pat {
        case.failed = true;
        let within: Vec<&Pattern> = match &pattern.kind {
            PatternKind::Tuple(elems) => elems.iter().collect(),
            PatternKind::Variant(_, holds) => holds.as_deref().into_iter().collect(),
            PatternKind::Name(_) | PatternKind::Discard => Vec::new(),
        };
        for pattern in within {
            self.pattern(pattern, Ty::Error, &[], case);
        }
        Pat::Any
    }
}

/// The rows of `rows` that match values built by `ctor` from `arity` parts,
/// each with the patterns of the parts in place of its first.
fn specialize(rows: &[Vec<Pat>], ctor: &Ctor, arity: usize) -> Vec<Vec<Pat>> {
    let parts = |row: &Vec<Pat>| {
        let parts = match &row[0] {
            Pat::Any => vec![Pat::Any; arity],
            Pat::Built(built, parts) if built == ctor => parts.clone(),
            Pat::Built(..) => return None,
        };
        Some(parts.into_iter().chain(row[1..].iter().cloned()).collect())
    };
    rows.iter().filter_map(parts).collect()
}

/// The rows of `rows` that match a value however it's built, without their
/// first pattern.
fn rest_of_any(rows: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
    let rows = rows.iter().filter(|row| matches!(row[0], Pat::Any));
    rows.map(|row| row[1..].to_vec()).collect()
}

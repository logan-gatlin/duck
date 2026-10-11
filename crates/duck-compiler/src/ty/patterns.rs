//! `match`: the patterns its arms test a value against and bind names in,
//! and whether the arms cover every value, each matching some that those
//! before it don't.

use std::collections::HashMap;

use crate::ir::{BinOp as IrBinOp, Const, Expr, LocalId, Stmt, UnOp as IrUnOp, ValType};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, Arm, BinOp, ExprKind, Ident, ItemKind, Pattern, PatternKind, StmtKind};

use super::{
    ARRAY, Body, Checker, Label, Prim, StructId, TUPLE, Ty, TypeErrorKind, Value, binary, scalar,
    single, unions::narrow,
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
    Bool(bool),
    /// A number, by its bits. Zero has those of the positive one.
    Number(u64),
    /// An array, from as many elements. A string is one of its bytes.
    Array(usize),
}

/// One step of telling whether a value matches a pattern.
enum Step {
    /// What the value passes to match.
    Test(Expr),
    /// What reads the part of the value that the tests after it are of.
    Read(Vec<Stmt>),
}

/// The pattern of an arm, checked against the type of the value.
#[derive(Default)]
struct Case<'p> {
    /// What tells whether a value matches, each taken only if the tests
    /// before it passed.
    steps: Vec<Step>,
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
            (Ctor::Array(len), _) => match ty {
                Ty::Array(id) => vec![self.element(id); *len],
                _ => Vec::new(),
            },
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
            (Ty::Prim(Prim::Bool), _) => vec![Ctor::Bool(false), Ctor::Bool(true)],
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
        let all_start = ctors.iter().all(|(ctor, _)| starts(rows, ctor));
        all_start.then_some(ctors)
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
            let mut ctors = self.ctors(*ty).into_iter().flatten();
            let head = match ctors.find(|(ctor, _)| !starts(rows, ctor)) {
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
            (Ctor::Bool(value), ..) => value.to_string(),
            (Ctor::Array(_), ..) => format!("[{}]", parts.join(", ")),
            // One of endlessly many, so no arm is ever said to lack it.
            (Ctor::Number(_), ..) => "_".to_string(),
            _ => format!("({})", parts.join(", ")),
        }
    }

    /// Places each string that a pattern of `program` is in memory, after
    /// the literals of its globals: a `match` compares with it there. One
    /// in a function lowered for a constant to call is placed already.
    pub(super) fn place_pattern_strings(&mut self, program: &Program) {
        let mut strings = Vec::new();
        for item in &program.items {
            if let ItemKind::Fn(decl) = &item.kind {
                push_pattern_strings(&decl.body, &mut strings);
            }
        }
        for string in strings {
            self.pattern_string(string);
        }
    }

    /// The address of `string`, which a pattern is, placing it in memory
    /// unless it is there.
    fn pattern_string(&mut self, string: &str) -> u64 {
        self.share_data(string.as_bytes().to_vec(), 1, 1)
    }
}

impl Body<'_> {
    /// `value`, of type `ty`, which a `match` at `span` takes apart: as its
    /// bound, if `ty` is a type parameter bounded by a union or an enum,
    /// whose variants or members the patterns are then of. An instance of a
    /// generic function matches it as that bound too, which its type
    /// argument casts to.
    fn as_bound(&mut self, ty: Ty, value: Value, span: Span) -> (Ty, Value) {
        let key = (span.file, span.start);
        let bound = self.ck.known(ty);
        if bound != ty && self.ck.is_sum(bound) {
            self.ck.bound_uses.insert(key, bound);
            return (bound, value);
        }
        let bound = match self.ck.bound_uses.get(&key) {
            Some(bound) if !self.ck.instance_chain.is_empty() => *bound,
            _ => return (ty, value),
        };
        let args: Vec<_> = self.ck.type_params.iter().map(|(_, arg)| *arg).collect();
        let bound = self.ck.substitute(bound, &args, span);
        match self.ck.is_sum(ty) && self.ck.meets(ty, bound) {
            true => self.ck.cast_value(ty, bound, value).unwrap(),
            false => (ty, value),
        }
    }

    /// `match value:`, which runs the first of `arms` whose pattern the
    /// value matches, with the names the pattern binds. The value is
    /// evaluated once, and traps if no arm matches it, as only one that was
    /// never built here can.
    pub(super) fn match_stmt(&mut self, value: &parse::Expr, arms: &[Arm], out: &mut Vec<Stmt>) {
        let (ty, subject) = self.expr(value, None);
        let (ty, mut subject) = self.as_bound(ty, subject, value.span);
        // Held in temporaries that the arms test and their names read, so
        // nothing an arm does changes what its names are.
        self.spill(&mut subject, |_| false);
        out.extend(subject.pre);
        // No arm is run for a value that there never is: each is checked
        // as it is for one that failed to check, and left out.
        let mut unused = Vec::new();
        let (ty, out) = match ty {
            Ty::Never => (Ty::Error, &mut unused),
            _ => (ty, out),
        };
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
        if matched != Ty::Error && cases.iter().all(|case| !case.failed) {
            self.check_arms(arms, &rows, matched, value.span);
        }
        // The arms are in a block that each leaves once it has run.
        self.labels.push(Label::Other);
        let mut block = Vec::new();
        let mut ended = false;
        // One of them runs, or it traps: nothing follows it if each of them
        // never reaches its end.
        let mut left = true;
        for (arm, case) in arms.iter().zip(cases) {
            self.scopes.push(HashMap::new());
            for (name, ty, slots) in case.names {
                self.bind(name, ty, false, slots);
            }
            let test = case.steps.into_iter().rev().fold(None, |rest, step| {
                Some(match (step, rest) {
                    (Step::Test(test), None) => test,
                    (Step::Test(test), Some(rest)) => Expr::If {
                        ty: ValType::I32,
                        cond: Box::new(test),
                        then_expr: Box::new(rest),
                        else_expr: Box::new(Expr::Const(Const::I32(0))),
                    },
                    (Step::Read(read), rest) => {
                        let rest = rest.unwrap_or(Expr::Const(Const::I32(1)));
                        Expr::Seq(read, Box::new(rest))
                    }
                })
            });
            let (mut body, arm_left) = self.maybe(|lowered| match test {
                Some(_) => lowered.labelled(Label::Other, &arm.body),
                None => lowered.block(&arm.body),
            });
            left &= arm_left;
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
        self.ended |= left;
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
        self.ck.record(pattern.span, ty);
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
                        let expected = format!("{TUPLE}({})", vec!["_"; elems.len()].join(", "));
                        self.unmatched(expected, ty, pattern.span);
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
            PatternKind::Literal(literal) => {
                let built = self.literal_pattern(literal, ty, subject, case);
                built.unwrap_or_else(|| self.failed(pattern, case))
            }
            PatternKind::Array(elems) => {
                let Ty::Array(id) = ty else {
                    self.unmatched(format!("{ARRAY}(_)"), ty, pattern.span);
                    return self.failed(pattern, case);
                };
                let elem = self.ck.element(id);
                let (ptr, len) = (Expr::Local(subject[0]), Expr::Local(subject[1]));
                let count = Expr::Const(self.ck.addr_const(elems.len() as u64));
                let has_all = binary(self.ck.addr_type(), IrBinOp::Eq, len, count);
                case.steps.push(Step::Test(has_all));
                let stride = self.ck.layout(elem).0;
                let mut parts = Vec::new();
                for (i, pattern) in elems.iter().enumerate() {
                    // What matches every element reads none.
                    if pattern.kind == PatternKind::Discard {
                        parts.push(Pat::Any);
                        continue;
                    }
                    let ptr = scalar(self.ck.addr_type(), ptr.clone());
                    let value = self.load(ptr, i as u32 * stride, elem);
                    let mut read = value.pre;
                    let mut locals = Vec::new();
                    for (vt, scalar) in value.scalars {
                        let local = self.temp(vt);
                        read.push(Stmt::SetLocal(local, scalar));
                        locals.push(local);
                    }
                    case.steps.push(Step::Read(read));
                    parts.push(self.pattern(pattern, elem, &locals, case));
                }
                Pat::Built(Ctor::Array(elems.len()), parts)
            }
        }
    }

    /// Reports at `span` that a pattern matches values of the type
    /// `expected`, as written, and not a `found`, unless that is the error
    /// type.
    fn unmatched(&mut self, expected: String, found: Ty, span: Span) {
        if found != Ty::Error {
            let found = self.ck.ty_name(found);
            self.error(TypeErrorKind::Mismatch { expected, found }, span);
        }
    }

    /// `literal` against a value of type `ty` held in the locals `subject`:
    /// the value that `==` finds equal to it. `None` after reporting an
    /// error.
    fn literal_pattern(
        &mut self,
        literal: &parse::Expr,
        ty: Ty,
        subject: &[LocalId],
        case: &mut Case,
    ) -> Option<Pat> {
        let number = match &literal.kind {
            ExprKind::Unary(_, number) => &number.kind,
            kind => kind,
        };
        let value = |subject: &[LocalId]| Expr::Local(subject[0]);
        let ctor = match (number, ty) {
            (ExprKind::Bool(wanted), Ty::Prim(Prim::Bool)) => {
                case.steps.push(Step::Test(match wanted {
                    true => value(subject),
                    false => Expr::Unary(ValType::I32, IrUnOp::Eqz, Box::new(value(subject))),
                }));
                Ctor::Bool(*wanted)
            }
            (ExprKind::Int(_), Ty::Prim(prim)) | (ExprKind::Float(_), Ty::Prim(prim))
                if prim.is_float() || prim.is_int() && matches!(number, ExprKind::Int(_)) =>
            {
                let errors = self.ck.errors.len();
                let (_, number) = self.expr(literal, Some(ty));
                let [(vt, Expr::Const(number))] = number.scalars[..] else {
                    return None;
                };
                if self.ck.errors.len() > errors {
                    return None;
                }
                let equal = binary(vt, IrBinOp::Eq, value(subject), Expr::Const(number));
                case.steps.push(Step::Test(equal));
                Ctor::Number(number_bits(number))
            }
            (ExprKind::Str(string), Ty::Array(id)) if self.ck.element(id) == Ty::Prim(Prim::U8) => {
                let ty = self.ck.with_writes(ty, false);
                let value = self.read_locals(ty, subject);
                // Every function's are placed before any is lowered, but
                // one lowered for a constant to call.
                let placed = self.ck.pattern_string(string);
                let string_value = self.ck.array_value(placed, string.len() as u64);
                let equal = self.compare(BinOp::Eq, ty, value, string_value);
                case.steps.push(Step::Test(single(equal)));
                // What it matches is the array of its bytes, which an array
                // pattern may match too.
                let bytes = string.bytes().map(|byte| Ctor::Number(byte.into()));
                let bytes = bytes.map(|byte| Pat::Built(byte, Vec::new())).collect();
                return Some(Pat::Built(Ctor::Array(string.len()), bytes));
            }
            _ => {
                let expected = match number {
                    ExprKind::Bool(_) => Prim::Bool.name().to_string(),
                    ExprKind::Int(_) => Prim::I32.name().to_string(),
                    ExprKind::Float(_) => Prim::F64.name().to_string(),
                    _ => format!("{ARRAY}({})", Prim::U8.name()),
                };
                self.unmatched(expected, ty, literal.span);
                return None;
            }
        };
        Some(Pat::Built(ctor, Vec::new()))
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
            self.error(self.ck.misused_variant(id, index), name.span);
            return None;
        }
        let tag = Expr::Const(Const::I32(index as i32));
        let is_variant = binary(ValType::I32, IrBinOp::Eq, Expr::Local(subject[0]), tag);
        case.steps.push(Step::Test(is_variant));
        let parts = holds.map(|holds| {
            // What matches every value the variant holds reads none.
            let locals = match holds.kind {
                PatternKind::Discard => Vec::new(),
                _ => self.variant_locals(id, index, subject, case),
            };
            self.pattern(holds, held, &locals, case)
        });
        Some(Pat::Built(
            Ctor::Variant(index),
            parts.into_iter().collect(),
        ))
    }

    /// The locals of what variant `index` holds in a value of union `id`
    /// held in the locals `subject`: those of the leaves the variants share
    /// that hold it, but for each wider than the scalar it holds, which a
    /// step of `case` reads out of it.
    fn variant_locals(
        &mut self,
        id: StructId,
        index: usize,
        subject: &[LocalId],
        case: &mut Case,
    ) -> Vec<LocalId> {
        let held = self.ck.structs[id.0 as usize].fields[index].ty;
        let leaves = self.ck.union_leaves(id).1.swap_remove(index);
        let mut read = Vec::new();
        let mut locals = Vec::new();
        for (leaf, vt) in leaves.into_iter().zip(self.ck.val_types(held)) {
            let shared = subject[leaf];
            let leaf_ty = self.locals[shared.0 as usize].ty;
            locals.push(match leaf_ty == vt {
                true => shared,
                false => {
                    let local = self.temp(vt);
                    let scalar = narrow(leaf_ty, vt, Expr::Local(shared));
                    read.push(Stmt::SetLocal(local, scalar));
                    local
                }
            });
        }
        if !read.is_empty() {
            case.steps.push(Step::Read(read));
        }
        locals
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
        let value = self.read_locals(ty, subject);
        let equal = self.compare(BinOp::Eq, ty, value, member);
        case.steps.push(Step::Test(single(equal)));
        Some(Pat::Built(Ctor::Member(index?), Vec::new()))
    }

    /// The value of type `ty` that the locals `subject` hold.
    fn read_locals(&self, ty: Ty, subject: &[LocalId]) -> Value {
        let locals = subject.iter().map(|local| Expr::Local(*local));
        self.scalars(ty, locals.collect())
    }

    /// Marks `case` as having an error in `pattern`, which is reported, and
    /// gives the names in the patterns within it the error type, so that
    /// what uses them isn't reported too.
    fn failed<'p>(&mut self, pattern: &'p Pattern, case: &mut Case<'p>) -> Pat {
        case.failed = true;
        let within: Vec<&Pattern> = match &pattern.kind {
            PatternKind::Tuple(elems) | PatternKind::Array(elems) => elems.iter().collect(),
            PatternKind::Variant(_, holds) => holds.as_deref().into_iter().collect(),
            PatternKind::Name(_) | PatternKind::Discard | PatternKind::Literal(_) => Vec::new(),
        };
        for pattern in within {
            self.pattern(pattern, Ty::Error, &[], case);
        }
        Pat::Any
    }
}

/// Whether one of `rows` starts with a pattern for values built by `ctor`.
fn starts(rows: &[Vec<Pat>], ctor: &Ctor) -> bool {
    let mut heads = rows.iter().map(|row| &row[0]);
    heads.any(|head| matches!(head, Pat::Built(built, _) if built == ctor))
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

/// The bits of a number that a pattern is, which tell it apart from every
/// number that `==` finds different: those of `0.0` for `-0.0` too.
fn number_bits(number: Const) -> u64 {
    match number {
        Const::I32(x) => x as u32 as u64,
        Const::I64(x) => x as u64,
        Const::F32(x) => (x + 0.0).to_bits().into(),
        Const::F64(x) => (x + 0.0).to_bits(),
    }
}

/// Pushes each string that a pattern in `block` is, in source order.
fn push_pattern_strings<'p>(block: &'p [parse::Stmt], out: &mut Vec<&'p str>) {
    fn push<'p>(pattern: &'p Pattern, out: &mut Vec<&'p str>) {
        match &pattern.kind {
            PatternKind::Literal(literal) => {
                if let ExprKind::Str(string) = &literal.kind {
                    out.push(string);
                }
            }
            PatternKind::Tuple(elems) | PatternKind::Array(elems) => {
                for elem in elems {
                    push(elem, out);
                }
            }
            PatternKind::Variant(_, holds) => {
                if let Some(holds) = holds {
                    push(holds, out);
                }
            }
            PatternKind::Name(_) | PatternKind::Discard => {}
        }
    }
    for stmt in block {
        match &stmt.kind {
            StmtKind::If {
                then_body,
                else_body,
                ..
            } => {
                push_pattern_strings(then_body, out);
                push_pattern_strings(else_body.as_deref().unwrap_or_default(), out);
            }
            StmtKind::While { body, .. } | StmtKind::For { body, .. } | StmtKind::Defer(body) => {
                push_pattern_strings(body, out);
            }
            StmtKind::Fn(decl) => push_pattern_strings(&decl.body, out),
            StmtKind::Match { arms, .. } => {
                for arm in arms {
                    push(&arm.pattern, out);
                    push_pattern_strings(&arm.body, out);
                }
            }
            // Every statement that holds others is above.
            StmtKind::Binding(_) | StmtKind::Expr(_) | StmtKind::Pass => {}
        }
    }
}

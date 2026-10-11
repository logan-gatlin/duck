//! Unions: types whose values hold one of a fixed list of variants, and a
//! tag that says which. A union is declared and instantiated as a struct is,
//! with a field per variant. Outside memory a value is its tag and then the
//! leaves that its variants share, as the Canonical ABI of the component
//! model flattens a variant: each holds a scalar of the variant that the
//! value holds, and is wide enough for that of any. Those that the variant
//! has nothing in are zero in any value built here. In memory it is the tag
//! and then room for the largest variant.

use std::iter;

use crate::ir::{BinOp as IrBinOp, Const, Expr, Stmt, UnOp as IrUnOp, ValType};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, Arg, ExprKind, Ident, UnionDecl};

use super::{
    Body, Checker, FieldDef, Item, Leaf, OPTION, ParamDefaults, Prim, RESULT, StructDef, StructId,
    TYPE_FIELDS, Ty, TypeErrorKind, Value, Visit, binary, fold_unary, is_pure, never, zero,
};

/// The type of a union's tag in memory, which counts its variants from 0.
pub(super) const TAG: Prim = Prim::U8;

/// The most variants a union can have: as many as its tag tells apart.
pub(super) const MAX_VARIANTS: usize = 256;

/// The built-in unions. `none` is the first variant of `option`, so that
/// zeroed memory holds it.
const BUILTIN_UNIONS: [Builtin; 2] = [
    Builtin {
        name: OPTION,
        params: &["T"],
        variants: &[("none", None), ("some", Some(0))],
    },
    Builtin {
        name: RESULT,
        params: &["T", "E"],
        variants: &[("ok", Some(0)), ("err", Some(1))],
    },
];

/// A generic union that the language declares.
struct Builtin {
    name: &'static str,
    params: &'static [&'static str],
    /// The name of each variant, and which type parameter it holds, if any.
    variants: &'static [(&'static str, Option<usize>)],
}

/// That a union within a value holds one of its variants.
#[derive(Clone, Copy, PartialEq)]
pub(super) struct Holds {
    /// The leaf of the value that holds the union's tag.
    tag: Leaf,
    /// The tag of the variant.
    variant: i32,
}

impl Holds {
    /// That the union whose tag leaf `tag` holds has its variant `index`.
    pub(super) fn new(tag: Leaf, index: usize) -> Self {
        let variant = index as i32;
        Self { tag, variant }
    }

    /// Whether the union is the one whose tag is in leaf `leaf`.
    pub(super) fn is_of(self, leaf: usize) -> bool {
        self.tag.index == leaf
    }

    /// Whether it's so of the value with the scalars `consts`.
    pub(super) fn in_consts(self, consts: &[Const]) -> bool {
        let tag = consts
            .get(self.tag.index)
            .map(|tag| self.tag_in(Expr::Const(*tag)));
        tag == Some(Expr::Const(Const::I32(self.variant)))
    }

    /// The tag that `leaf` holds, which is the leaf of the union's tag: a
    /// union within another's variant may share a wider one.
    fn tag_in(self, leaf: Expr) -> Expr {
        narrow(self.tag.ty, TAG.val_type(), leaf)
    }
}

impl Checker {
    /// The union that `ty` is, if it's one.
    pub(super) fn union_id(&self, ty: Ty) -> Option<StructId> {
        match ty {
            Ty::Struct(id) if self.structs[id.0 as usize].union => Some(id),
            _ => None,
        }
    }

    /// Declares the built-in unions, which are generic unions that no module
    /// declares and every module sees.
    pub(super) fn declare_builtin_unions(&mut self) {
        // Nothing is reported in them, so they are written nowhere.
        let span = Span {
            file: self.entry,
            start: 0,
            end: 0,
        };
        for union in BUILTIN_UNIONS {
            let Builtin {
                name,
                params,
                variants,
            } = union;
            let ident = |name: &&str| Ident {
                name: name.to_string(),
                span,
            };
            let params: Vec<_> = params.iter().map(ident).collect();
            let params = self.new_params(&params);
            let variant = |(name, holds): &(&str, Option<usize>)| FieldDef {
                name: name.to_string(),
                ty: holds.map_or(Ty::Unit, |param| params[param]),
                is_pub: true,
                bare: holds.is_none(),
                default: None,
                default_ty: None,
                used: None,
                span,
            };
            self.builtin_unions
                .push(StructId(self.structs.len() as u32));
            self.structs.push(StructDef {
                name: name.to_string(),
                module: self.entry,
                item: 0,
                is_pub: true,
                union: true,
                uses: Vec::new(),
                fields: variants.iter().map(variant).collect(),
                params,
                defaults: ParamDefaults::default(),
                instance: None,
                depth: None,
            });
        }
    }

    /// The built-in union `name`, if it names one.
    pub(super) fn builtin_union(&self, name: &str) -> Option<StructId> {
        let index = BUILTIN_UNIONS.iter().position(|union| union.name == name)?;
        self.builtin_unions.get(index).copied()
    }

    /// Resolves the variants of union `id`, which `decl` declares, with its
    /// type parameters in scope.
    pub(super) fn union_variants(
        &mut self,
        program: &Program,
        id: usize,
        decl: &UnionDecl,
        visits: &mut [Visit],
    ) -> Vec<FieldDef> {
        let mut variants: Vec<FieldDef> = Vec::new();
        // Where the first variant past the most there can be is written.
        let mut extra = None;
        for entry in &decl.entries {
            let variant = match entry {
                parse::Entry::Own(variant) => variant,
                parse::Entry::Use(used) => {
                    let (ty, used_variants) = self.used_fields(program, id, used, visits);
                    self.structs[id].uses.push(ty);
                    for variant in used_variants {
                        if self.structs[id].is_pub {
                            self.check_public(variant.ty, used.span, &variant.name);
                        }
                        if variants.iter().any(|v| v.name == variant.name) {
                            let kind = TypeErrorKind::DuplicateVariant(variant.name);
                            self.error(kind, used.span);
                            continue;
                        }
                        variants.push(variant);
                        if variants.len() > MAX_VARIANTS {
                            extra.get_or_insert(used.span);
                        }
                    }
                    continue;
                }
            };
            let name = &variant.name;
            let ty = match &variant.ty {
                Some(ty) => {
                    let resolved = self.resolve_ty(ty);
                    if self.structs[id].is_pub {
                        self.check_public(resolved, ty.span, &name.name);
                    }
                    resolved
                }
                None => Ty::Unit,
            };
            if variants.iter().any(|v| v.name == name.name) {
                self.error(
                    TypeErrorKind::DuplicateVariant(name.name.clone()),
                    name.span,
                );
                continue;
            }
            variants.push(FieldDef {
                name: name.name.clone(),
                ty,
                is_pub: true,
                bare: variant.ty.is_none(),
                default: None,
                default_ty: None,
                used: None,
                span: variant.span,
            });
            if variants.len() > MAX_VARIANTS {
                extra.get_or_insert(variant.span);
            }
        }
        if let Some(extra) = extra {
            let kind = TypeErrorKind::TooManyVariants(decl.name.name.clone());
            self.error(kind, extra);
        }
        variants
    }

    /// Where the variants of union `id` start in memory, and its size and
    /// alignment, laid out as C would a struct of the tag and then a union:
    /// the variants at the first multiple of the largest alignment past the
    /// tag, and the whole padded to one.
    pub(super) fn union_layout(&self, id: StructId) -> (u32, u32, u32) {
        let (mut size, mut align) = (0u32, TAG.size());
        for variant in &self.structs[id.0 as usize].fields {
            let (variant_size, variant_align) = self.layout(variant.ty);
            size = size.max(variant_size);
            align = align.max(variant_align);
        }
        let start = TAG.size().next_multiple_of(align);
        (start, (start + size).next_multiple_of(align), align)
    }

    /// The error for giving variant `index` of union `id` a value it doesn't
    /// hold, or none where it holds one.
    pub(super) fn misused_variant(&self, id: StructId, index: usize) -> TypeErrorKind {
        let variant = &self.structs[id.0 as usize].fields[index];
        match variant.bare {
            true => TypeErrorKind::VariantTakesNothing(variant.name.clone()),
            false => TypeErrorKind::VariantNeedsValue {
                variant: variant.name.clone(),
                ty: self.ty_name(variant.ty),
            },
        }
    }

    /// The types of the leaves that follow the tag in a value of union `id`,
    /// and for each variant, the leaf that holds each scalar of its value,
    /// counting the tag as leaf 0. The variants share the leaves as the
    /// Canonical ABI has them: the scalars of each are held in order from
    /// the first leaf, each of which has the [`join`] of the types it holds.
    pub(super) fn union_leaves(&self, id: StructId) -> (Vec<ValType>, Vec<Vec<usize>>) {
        let variants = &self.structs[id.0 as usize].fields;
        let held: Vec<_> = variants.iter().map(|v| self.val_types(v.ty)).collect();
        let mut shared: Vec<ValType> = Vec::new();
        for scalars in &held {
            for (i, vt) in scalars.iter().enumerate() {
                match shared.get_mut(i) {
                    Some(leaf) => *leaf = join(*leaf, *vt),
                    None => shared.push(*vt),
                }
            }
        }
        // The first leaf is the tag.
        let leaves = held.iter().map(|scalars| (1..=scalars.len()).collect());
        (shared, leaves.collect())
    }
}

impl Checker {
    /// `value`, of union `from`, as a value of union `to`, which starts as
    /// `from` does: it holds the same variant. A scalar of a variant is in
    /// the same leaf in both, which in `to` may be wider for the variants
    /// that `from` hasn't, and the leaves that only those use are zero.
    pub(super) fn widen_union(&self, from: StructId, to: StructId, value: Value) -> Value {
        let (from_leaves, to_leaves) = (self.union_leaves(from).0, self.union_leaves(to).0);
        // Only a variant whose type failed to resolve leaves `to` without
        // a leaf that `from` has, as it then holds nothing.
        let lacks_leaf = from_leaves.len() > to_leaves.len();
        let types = iter::once(ValType::I32).chain(to_leaves);
        let mut scalars: Vec<_> = types.map(|vt| (vt, Expr::Const(zero(vt)))).collect();
        // Only a mistyped value has other scalars than the union's.
        if lacks_leaf || value.scalars.len() != 1 + from_leaves.len() {
            return Value {
                pre: Vec::new(),
                scalars,
            };
        }
        for (leaf, (vt, scalar)) in value.scalars.into_iter().enumerate() {
            let (shared, zeroed) = &mut scalars[leaf];
            *zeroed = widen(vt, *shared, scalar);
        }
        Value {
            pre: value.pre,
            scalars,
        }
    }
}

impl Body<'_> {
    /// Whether `expr` names a union: one that no variable shadows, one in a
    /// module, a type parameter that stands for one, a generic one given
    /// type arguments, or a built-in one, with them or without.
    pub(super) fn names_union(&self, expr: &parse::Expr) -> bool {
        let generic = match &expr.kind {
            ExprKind::Call(callee, args) if self.names_type(callee, args) => callee,
            _ => expr,
        };
        if let ExprKind::Name(name) = &generic.kind
            && self.lookup(name).is_none()
            && self.ck.builtin_union(name).is_some()
        {
            return true;
        }
        let item = match &expr.kind {
            ExprKind::Call(callee, args) if self.names_type(callee, args) => self.named(callee),
            ExprKind::Name(name) if self.lookup(name).is_none() && self.item(name).is_none() => {
                let param = self.stands_for(name);
                return param.is_some_and(|ty| self.ck.union_id(ty).is_some());
            }
            _ => self.named(expr),
        };
        match item {
            Some(Item::Struct(id)) => self.ck.structs[id.0 as usize].union,
            Some(Item::Alias(id)) => self.ck.union_id(self.ck.aliased(id)).is_some(),
            _ => false,
        }
    }

    /// `U.name` or `U.name(args)`, where `U` is a union if it
    /// [names one](Self::names_union): the variant `name`, holding the value
    /// that `args` gives. `None` if `U` isn't a union, or if `name` is no
    /// variant but a field of `type`, which `U` is as a value.
    pub(super) fn union_variant(
        &mut self,
        union: &parse::Expr,
        name: &Ident,
        args: Option<&[Arg]>,
    ) -> Option<(Ty, Value)> {
        if !self.names_union(union) {
            return None;
        }
        let ty = self.expr_type(union);
        let variants = self
            .ck
            .union_id(ty)
            .map(|id| &self.ck.structs[id.0 as usize].fields);
        let named = variants.is_some_and(|variants| variants.iter().any(|v| v.name == name.name));
        if ty != Ty::Error && !named && TYPE_FIELDS.contains(&name.name.as_str()) {
            return None;
        }
        Some(self.variant(ty, name, args))
    }

    /// `.name` or `.name(args)`: the variant `name` of the union expected of
    /// it, or the member `name` of the enum.
    pub(super) fn dot(
        &mut self,
        name: &Ident,
        args: Option<&[Arg]>,
        expected: Option<Ty>,
    ) -> (Ty, Value) {
        match expected {
            // A union that a result has yet to settle is expected of
            // nothing, which is to say what it is.
            Some(ty) if self.ck.union_id(ty).is_some() && !self.ck.has_hole(ty) => {
                return self.variant(ty, name, args);
            }
            Some(Ty::Enum(id)) if args.is_none() => match self.enum_member(id, name) {
                Some(member) => return member,
                // A field of the enum as a `type`.
                None => {
                    let kind = TypeErrorKind::NoMember {
                        ty: self.ck.ty_name(Ty::Enum(id)),
                        member: name.name.clone(),
                    };
                    self.error(kind, name.span);
                }
            },
            Some(Ty::Enum(_)) => {
                let kind = TypeErrorKind::NotCallable(format!(".{}", name.name));
                self.error(kind, name.span);
            }
            // What it is compared with or assigned to has no value, so it
            // has none either: only what it would hold is evaluated.
            Some(Ty::Never) => {
                let args = args.into_iter().flatten();
                let held = args.map(|arg| self.expr(&arg.value, None).1).collect();
                let mut held = self.seq(held);
                self.spill(&mut held, is_pure);
                return never(held.pre);
            }
            // A type that failed to resolve, already reported.
            Some(Ty::Error) => {}
            // A type parameter is no union or enum until it's given a type,
            // and its variants and members are written `T.name`.
            _ => self.error(TypeErrorKind::UntypedDot(name.name.clone()), name.span),
        }
        for arg in args.into_iter().flatten() {
            self.expr(&arg.value, None);
        }
        (Ty::Error, Value::default())
    }

    /// The variant `name` of the union `ty`, holding the value that `args`
    /// gives, if it holds one: the tag, then that value in the leaves the
    /// variants share, and zero in those it has nothing in.
    fn variant(&mut self, ty: Ty, name: &Ident, args: Option<&[Arg]>) -> (Ty, Value) {
        let found = self.ck.union_id(ty).and_then(|id| {
            let variants = &self.ck.structs[id.0 as usize].fields;
            let index = variants.iter().position(|v| v.name == name.name)?;
            Some((id, index, variants[index].ty, variants[index].bare))
        });
        let Some((id, index, holds, bare)) = found else {
            if ty != Ty::Error {
                let kind = TypeErrorKind::NoVariant {
                    ty: self.ck.ty_name(ty),
                    variant: name.name.clone(),
                };
                self.error(kind, name.span);
            }
            for arg in args.into_iter().flatten() {
                self.expr(&arg.value, None);
            }
            return (Ty::Error, Value::default());
        };
        let held = match (bare, args) {
            (true, None) => Value::default(),
            (false, Some([arg])) if arg.label.is_none() => self.check(&arg.value, holds),
            _ => {
                self.error(self.ck.misused_variant(id, index), name.span);
                for arg in args.into_iter().flatten() {
                    self.expr(&arg.value, None);
                }
                return (ty, self.blank(ty));
            }
        };
        let leaves = self.ck.union_leaves(id).1.swap_remove(index);
        // Only a mistyped value has other scalars than the variant's.
        if held.scalars.len() != leaves.len() {
            return (ty, self.blank(ty));
        }
        let mut value = self.blank(ty);
        value.scalars[0].1 = Expr::Const(Const::I32(index as i32));
        for (leaf, (vt, scalar)) in leaves.into_iter().zip(held.scalars) {
            let (shared, zeroed) = &mut value.scalars[leaf];
            *zeroed = widen(vt, *shared, scalar);
        }
        value.pre = held.pre;
        (ty, value)
    }
}

/// The type of a leaf that holds a scalar of type `a` in one variant of a
/// union and one of type `b` in another, as the Canonical ABI joins them:
/// one as wide as both, and an integer unless both are the same float.
fn join(a: ValType, b: ValType) -> ValType {
    match (a, b) {
        _ if a == b => a,
        (ValType::I32, ValType::F32) | (ValType::F32, ValType::I32) => ValType::I32,
        _ => ValType::I64,
    }
}

/// `expr`, a scalar of type `from`, as a leaf of type `to` holds it: by its
/// bits, with zeroes above them. `to` is `from` [joined](join) with others.
pub(super) fn widen(from: ValType, to: ValType, expr: Expr) -> Expr {
    match (from, to) {
        (ValType::F32, ValType::I32) | (ValType::F64, ValType::I64) => {
            unary(from, IrUnOp::Reinterpret, expr)
        }
        (ValType::I32, ValType::I64) => unary(from, IrUnOp::ExtendU, expr),
        (ValType::F32, ValType::I64) => {
            let bits = widen(from, ValType::I32, expr);
            widen(ValType::I32, to, bits)
        }
        _ => expr,
    }
}

/// The scalar of type `to` that `expr`, a leaf of type `from`, holds: what
/// [`widen`] made the leaf from.
pub(super) fn narrow(from: ValType, to: ValType, expr: Expr) -> Expr {
    match (from, to) {
        (ValType::I32, ValType::F32) | (ValType::I64, ValType::F64) => {
            unary(from, IrUnOp::Reinterpret, expr)
        }
        (ValType::I64, ValType::I32) => unary(from, IrUnOp::Wrap, expr),
        (ValType::I64, ValType::F32) => {
            let bits = narrow(from, ValType::I32, expr);
            narrow(ValType::I32, to, bits)
        }
        _ => expr,
    }
}

/// `<ty>.<op>` of `expr`, or its result if `expr` is a constant, so that a
/// constant is one in whatever leaf holds it.
fn unary(ty: ValType, op: IrUnOp, expr: Expr) -> Expr {
    let folded = match expr {
        Expr::Const(c) => fold_unary(op, c).ok(),
        _ => None,
    };
    match folded {
        Some(c) => Expr::Const(c),
        None => Expr::Unary(ty, op, Box::new(expr)),
    }
}

/// Whether the value with scalars `leaves` holds every variant of `when`.
pub(super) fn tags_are(when: &[Holds], leaves: &[Expr]) -> Expr {
    let mut tests = Vec::new();
    for holds in when {
        match holds.tag_in(leaves[holds.tag.index].clone()) {
            // The tag of a variant built in place is known.
            Expr::Const(Const::I32(tag)) if tag == holds.variant => {}
            Expr::Const(_) => return Expr::Const(Const::I32(0)),
            tag => {
                let variant = Expr::Const(Const::I32(holds.variant));
                tests.push(binary(ValType::I32, IrBinOp::Eq, tag, variant));
            }
        }
    }
    let tests = tests.into_iter();
    tests
        .reduce(|all, test| binary(ValType::I32, IrBinOp::And, all, test))
        .unwrap_or(Expr::Const(Const::I32(1)))
}

/// `stmts`, run only where the value with scalars `leaves` holds every
/// variant of `when`.
pub(super) fn where_held(when: &[Holds], leaves: &[Expr], stmts: Vec<Stmt>) -> Vec<Stmt> {
    match tags_are(when, leaves) {
        Expr::Const(Const::I32(0)) => Vec::new(),
        Expr::Const(_) => stmts,
        cond => vec![Stmt::If {
            cond,
            then_body: stmts,
            else_body: Vec::new(),
        }],
    }
}

//! Unions: types whose values hold one of a fixed list of variants, and a
//! tag that says which. A union is declared and instantiated as a struct is,
//! with a field per variant. Outside memory a value is its tag and then the
//! scalars of every variant, of which only those of the one it holds are
//! read: the rest are zero in any value built here. In memory it is the tag
//! and then room for the largest variant.

use std::ops::Range;

use crate::ir::{BinOp as IrBinOp, Const, Expr, Stmt, ValType};
use crate::parse::{self, Arg, ExprKind, Ident, UnionDecl};

use super::{
    Body, Checker, FieldDef, Item, Prim, StructId, TYPE_FIELDS, Ty, TypeErrorKind, Value, binary,
};

/// The type of a union's tag in memory, which counts its variants from 0.
pub(super) const TAG: Prim = Prim::U8;

/// The most variants a union can have: as many as its tag tells apart.
pub(super) const MAX_VARIANTS: usize = 256;

/// That a union within a value holds one of its variants.
#[derive(Clone, Copy, PartialEq)]
pub(super) struct Holds {
    /// The leaf of the value that is the union's tag.
    tag: usize,
    /// The tag of the variant.
    variant: i32,
}

impl Holds {
    /// That the union whose tag is leaf `tag` holds its variant `index`.
    pub(super) fn new(tag: usize, index: usize) -> Self {
        let variant = index as i32;
        Self { tag, variant }
    }

    /// Whether the union is the one whose tag is leaf `tag`.
    pub(super) fn is_of(self, tag: usize) -> bool {
        self.tag == tag
    }

    /// Whether it's so of the value with the scalars `consts`.
    pub(super) fn in_consts(self, consts: &[Const]) -> bool {
        consts.get(self.tag) == Some(&Const::I32(self.variant))
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

    /// Resolves the variants of union `id`, which `decl` declares, with its
    /// type parameters in scope.
    pub(super) fn union_variants(&mut self, id: usize, decl: &UnionDecl) -> Vec<FieldDef> {
        let mut variants: Vec<FieldDef> = Vec::new();
        for variant in &decl.variants {
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
                span: variant.span,
            });
        }
        if let Some(extra) = decl.variants.get(MAX_VARIANTS) {
            let kind = TypeErrorKind::TooManyVariants(decl.name.name.clone());
            self.error(kind, extra.span);
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

    /// The leaves of a value of union `id` that variant `index` is held in:
    /// those after the tag and the variants before it.
    pub(super) fn variant_leaves(&self, id: StructId, index: usize) -> Range<usize> {
        let variants = &self.structs[id.0 as usize].fields;
        let width = |variant: &FieldDef| self.val_types(variant.ty).len();
        let start = 1 + variants[..index].iter().map(width).sum::<usize>();
        start..start + width(&variants[index])
    }
}

impl Body<'_> {
    /// Whether `expr` names a union: one that no variable shadows, one in a
    /// module, a type parameter that stands for one, or a generic one given
    /// type arguments.
    pub(super) fn names_union(&self, expr: &parse::Expr) -> bool {
        let item = match &expr.kind {
            ExprKind::Call(callee, args) if self.names_type(callee, args) => self.named(callee),
            ExprKind::Name(name) if self.lookup(name).is_none() && self.ck.item(name).is_none() => {
                let param = self.ck.type_param(name);
                return param.is_some_and(|ty| self.ck.union_id(ty).is_some());
            }
            _ => self.named(expr),
        };
        matches!(item, Some(Item::Struct(id)) if self.ck.structs[id.0 as usize].union)
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
            Some(ty) if self.ck.union_id(ty).is_some() => return self.variant(ty, name, args),
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
    /// gives, if it holds one: the tag, then that value among the zeroed
    /// scalars of the other variants.
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
        let leaves = self.ck.variant_leaves(id, index);
        // Only a mistyped value has other scalars than the variant's.
        if held.scalars.len() != leaves.len() {
            return (ty, self.blank(ty));
        }
        let mut value = self.blank(ty);
        value.scalars[0].1 = Expr::Const(Const::I32(index as i32));
        value.scalars.splice(leaves, held.scalars);
        value.pre = held.pre;
        (ty, value)
    }
}

/// Whether the value with scalars `leaves` holds every variant of `when`.
pub(super) fn tags_are(when: &[Holds], leaves: &[Expr]) -> Expr {
    let mut tests = Vec::new();
    for holds in when {
        match &leaves[holds.tag] {
            // The tag of a variant built in place is known.
            Expr::Const(Const::I32(tag)) if *tag == holds.variant => {}
            Expr::Const(_) => return Expr::Const(Const::I32(0)),
            tag => {
                let variant = Expr::Const(Const::I32(holds.variant));
                tests.push(binary(ValType::I32, IrBinOp::Eq, tag.clone(), variant));
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

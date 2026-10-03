//! Field defaults: the constant a struct's field has where a constructor
//! gives it no value. Each is folded once, in declaration order with the
//! globals and enum members it may use, and every instance of a generic
//! struct shares its declaration's.

use crate::ir::{Const, Expr};
use crate::lex::Span;
use crate::parse::{self, Arg, ExprKind, Ident, StructDecl, TypeKind};

use super::{Body, Checker, StructId, Ty, TypeErrorKind, Value, zero};

/// The default of a struct field that has one.
#[derive(Clone)]
pub(super) enum FieldDefault {
    /// Not folded yet. Global initializers, enum members and other defaults
    /// can only use those of earlier structs.
    Pending,
    /// One constant per scalar leaf of the field's type.
    Folded(Vec<Const>),
    /// Reported as an error.
    Failed,
}

impl Checker {
    /// Checks and folds the defaults of struct `id`'s fields.
    pub(super) fn define_defaults(&mut self, id: StructId, decl: &StructDecl) {
        for field in &decl.fields {
            let Some(expr) = &field.default else {
                continue;
            };
            let fields = &self.structs[id.0 as usize].fields;
            // A repeated field isn't one of the struct's.
            let Some(index) = fields.iter().position(|def| def.span == field.span) else {
                continue;
            };
            let default = match self.fold_default(fields[index].ty, expr, &decl.params) {
                Some(consts) => FieldDefault::Folded(consts),
                None => FieldDefault::Failed,
            };
            self.structs[id.0 as usize].fields[index].default = Some(default);
        }
    }

    /// The folded value of `expr`, the default of a field of type `ty` in a
    /// struct with type parameters `params`. `None` after reporting an
    /// error, or if `ty` is the error type.
    fn fold_default(&mut self, ty: Ty, expr: &parse::Expr, params: &[Ident]) -> Option<Vec<Const>> {
        // The default is folded once for every instance, so it can neither
        // name a type parameter nor be a value laid out by one.
        let named = param_in_expr(expr, params).map(|(name, span)| (name.to_string(), span));
        let held = self.held_param(ty, true);
        let held = held.map(|param| (self.param_name(param), expr.span));
        if let Some((param, span)) = named.or(held) {
            self.error(TypeErrorKind::DefaultUsesParam(param), span);
            return None;
        }
        let errors = self.errors.len();
        let mut body = Body::new(self, Ty::Unit);
        body.global = true;
        body.default = true;
        let value = body.check(expr, ty);
        let consts = self.fold_value(&value, expr.span);
        (self.errors.len() == errors && ty != Ty::Error).then_some(consts)
    }

    /// The default of field `index` of struct `id`. An instance of a generic
    /// struct is given its fields before defaults are folded, so its own
    /// is read from its declaration.
    fn field_default(&self, id: StructId, index: usize) -> Option<&FieldDefault> {
        let def = &self.structs[id.0 as usize];
        let decl = def
            .instance
            .as_ref()
            .map_or(id, |instance| instance.generic);
        self.structs[decl.0 as usize].fields[index].default.as_ref()
    }

    /// A type parameter that `ty` holds, if any. With `by_value`, only one
    /// that `ty`'s layout may depend on: not one behind a pointer, an array
    /// or a function pointer.
    pub(super) fn held_param(&self, ty: Ty, by_value: bool) -> Option<Ty> {
        match ty {
            Ty::Param(_) => Some(ty),
            Ty::Struct(id) => {
                let instance = self.structs[id.0 as usize].instance.as_ref()?;
                let mut args = instance.args.iter();
                args.find_map(|arg| self.held_param(*arg, false))
            }
            Ty::Ptr(_) | Ty::Array(_) | Ty::Fn(_) if by_value => None,
            _ => self
                .components(ty)
                .into_iter()
                .find_map(|component| self.held_param(component, by_value)),
        }
    }
}

impl Body<'_> {
    /// A value of struct `id`, built from its labelled fields. A field given
    /// no value has its default.
    pub(super) fn construct_struct(&mut self, id: StructId, args: &[Arg], span: Span) -> Value {
        let def = &self.ck.structs[id.0 as usize];
        let (ty, foreign) = (def.name.clone(), def.module != self.ck.module);
        let fields = def.fields.clone();
        if foreign {
            let private = |field: &str| TypeErrorKind::PrivateField {
                ty: ty.clone(),
                field: field.to_string(),
            };
            let is_private = |name: &str| fields.iter().any(|f| f.name == name && !f.is_pub);
            // A private field without a default leaves nothing another
            // module could write here.
            match fields.iter().find(|f| !f.is_pub && f.default.is_none()) {
                Some(field) => self.error(private(&field.name), span),
                None => {
                    let labels = args.iter().filter_map(|arg| arg.label.as_ref());
                    for label in labels.filter(|label| is_private(&label.name)) {
                        self.error(private(&label.name), label.span);
                    }
                }
            }
        }
        let params: Vec<_> = fields.iter().map(|f| (f.name.clone(), f.ty)).collect();
        let binding = self.match_args(&params, args, true);
        let mut defaults = vec![Vec::new(); params.len()];
        let mut pending = false;
        for (i, (name, field_ty)) in params.iter().enumerate() {
            if binding.contains(&Some(i)) {
                continue;
            }
            let types = self.ck.val_types(*field_ty);
            let consts = match self.ck.field_default(id, i) {
                Some(FieldDefault::Folded(consts)) => consts.clone(),
                Some(default) => {
                    pending |= matches!(default, FieldDefault::Pending);
                    types.iter().map(|ty| zero(*ty)).collect()
                }
                None => {
                    self.error(TypeErrorKind::MissingArg(name.clone()), span);
                    continue;
                }
            };
            let consts = consts.into_iter().map(Expr::Const);
            defaults[i] = types.into_iter().zip(consts).collect();
        }
        // Only reachable from an earlier global's or member's initializer,
        // or an earlier default.
        if pending {
            self.error(TypeErrorKind::NotConstant, span);
        }
        let checked = args.iter().map(|_| None).collect();
        self.filled_args(&params, args, binding, checked, defaults)
    }
}

/// The first of the type parameters `params` that `expr` names, and where.
/// No item or local shares a type parameter's name.
fn param_in_expr<'a>(expr: &'a parse::Expr, params: &[Ident]) -> Option<(&'a str, Span)> {
    let any = |exprs: &'a [parse::Expr]| exprs.iter().find_map(|e| param_in_expr(e, params));
    match &expr.kind {
        ExprKind::Name(name) => {
            let named = params.iter().any(|param| param.name == *name);
            named.then_some((name.as_str(), expr.span))
        }
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Unit
        | ExprKind::Module(_)
        | ExprKind::Placeholder => None,
        ExprKind::Tuple(items) | ExprKind::List(items) => any(items),
        ExprKind::Unary(_, inner)
        | ExprKind::Field(inner, _)
        | ExprKind::Deref(inner)
        | ExprKind::AddrOf(_, inner) => param_in_expr(inner, params),
        ExprKind::Repeat(a, b)
        | ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::Pipe(a, b) => param_in_expr(a, params).or_else(|| param_in_expr(b, params)),
        ExprKind::Call(callee, args) => param_in_expr(callee, params).or_else(|| {
            args.iter()
                .find_map(|arg| param_in_expr(&arg.value, params))
        }),
        ExprKind::Cast(value, ty) => {
            param_in_expr(value, params).or_else(|| param_in_type(ty, params, false))
        }
        ExprKind::FnType(ty) => param_in_type(ty, params, false),
    }
}

/// The first of the type parameters `params` that `ty` names, and where.
/// The name of a `qualified` type is another module's, but its type
/// arguments are not.
fn param_in_type<'a>(
    ty: &'a parse::Type,
    params: &[Ident],
    qualified: bool,
) -> Option<(&'a str, Span)> {
    let any = |tys: &'a [parse::Type]| tys.iter().find_map(|ty| param_in_type(ty, params, false));
    match &ty.kind {
        TypeKind::Named(name, args) => {
            let named = !qualified && params.iter().any(|param| param.name == *name);
            let named = named.then_some((name.as_str(), ty.span));
            named.or_else(|| args.as_deref().and_then(any))
        }
        TypeKind::Pointer(_, pointee) => param_in_type(pointee, params, false),
        TypeKind::Qualified(_, inner) => param_in_type(inner, params, true),
        TypeKind::Fn(args, ret) => any(args).or_else(|| {
            ret.as_deref()
                .and_then(|ret| param_in_type(ret, params, false))
        }),
    }
}

//! Defaults: the constant a struct's field has where a constructor gives it
//! no value, and a function's parameter where a call gives it no argument.
//! Each is folded once, and every instance of a generic struct or function
//! shares its declaration's. A field's is folded with the globals and enum
//! members, which may use it as it may use them. A parameter's is folded
//! after them all, as nothing constant calls a function.

use crate::ir::Const;
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, Arg, ExprKind, FnSig, Ident, StructDecl, TypeKind};

use super::{Body, Checker, StructId, Ty, TypeErrorKind, Value, fn_sigs};

/// The default of a struct field or function parameter that has one.
#[derive(Clone)]
pub(super) enum DefaultValue {
    /// Not folded yet. A field's is when a global initializer, enum member
    /// or other default first uses one of its struct's.
    Pending,
    /// One constant per scalar leaf of the field's or parameter's type.
    Folded(Vec<Const>),
    /// Reported as an error.
    Failed,
}

impl Checker {
    /// Checks and folds the defaults of struct `id`'s fields.
    pub(super) fn define_defaults(&mut self, program: &Program, id: StructId, decl: &StructDecl) {
        for field in &decl.fields {
            let Some(expr) = &field.default else {
                continue;
            };
            let fields = &self.structs[id.0 as usize].fields;
            // A repeated field isn't one of the struct's.
            let Some(index) = fields.iter().position(|def| def.span == field.span) else {
                continue;
            };
            let ty = fields[index].ty;
            let default = match self.fold_default(program, ty, expr, &decl.params) {
                Some(consts) => DefaultValue::Folded(consts),
                None => DefaultValue::Failed,
            };
            self.structs[id.0 as usize].fields[index].default = Some(default);
        }
    }

    /// Checks and folds the defaults of every function's parameters.
    pub(super) fn define_param_defaults(&mut self, program: &Program) {
        for (id, (_, sig)) in fn_sigs(program).enumerate() {
            self.module = sig.name.span.file;
            let params = self.funcs[id].params.clone();
            self.funcs[id].defaults = self.fold_param_defaults(program, sig, &params);
        }
        self.define_generic_fn_defaults(program);
    }

    /// The default of each parameter of `sig` that has one, checked and
    /// folded. `params` are its parameters as resolved.
    pub(super) fn fold_param_defaults(
        &mut self,
        program: &Program,
        sig: &FnSig,
        params: &[(String, Ty)],
    ) -> Vec<Option<DefaultValue>> {
        let names: Vec<_> = sig.params.iter().map(|param| param.name.clone()).collect();
        let mut defaults = Vec::new();
        for (param, (_, ty)) in sig.params.iter().zip(params) {
            let Some(expr) = &param.default else {
                defaults.push(None);
                continue;
            };
            // The default is folded once for every call, none of whose
            // arguments it can read. A global of the name isn't meant.
            let named = param_in_expr(expr, &names, false);
            let consts = match named.map(|(name, span)| (name.to_string(), span)) {
                Some((name, span)) => {
                    self.error(TypeErrorKind::DefaultReadsParam(name), span);
                    None
                }
                None => self.fold_default(program, *ty, expr, &sig.type_params),
            };
            defaults.push(Some(match consts {
                Some(consts) => DefaultValue::Folded(consts),
                None => DefaultValue::Failed,
            }));
        }
        defaults
    }

    /// The folded value of `expr`, the default of a field or parameter of
    /// type `ty` in a struct or function with type parameters `params`.
    /// `None` after reporting an error, or if `ty` is the error type.
    fn fold_default(
        &mut self,
        program: &Program,
        ty: Ty,
        expr: &parse::Expr,
        params: &[Ident],
    ) -> Option<Vec<Const>> {
        // The default is folded once for every instance, so it can neither
        // name a type parameter nor be a value laid out by one.
        let named = param_in_expr(expr, params, true);
        let named = named.map(|(name, span)| (name.to_string(), span));
        let held = self.held_param(ty, true);
        let held = held.map(|param| (self.param_name(param), expr.span));
        if let Some((param, span)) = named.or(held) {
            self.error(TypeErrorKind::DefaultUsesParam(param), span);
            return None;
        }
        let errors = self.errors.len();
        let mut body = Body::new(self, Ty::Unit);
        body.global = Some(program);
        body.default = true;
        let value = body.check(expr, ty);
        let consts = self.fold_value(&value, expr.span);
        (self.errors.len() == errors && ty != Ty::Error).then_some(consts)
    }

    /// The default of field `index` of struct `id`. An instance of a generic
    /// struct is given its fields before defaults are folded, so its own
    /// is read from its declaration.
    fn field_default(&self, id: StructId, index: usize) -> Option<&DefaultValue> {
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
        let item = def.item;
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
        let field_defaults = |body: &Self| -> Vec<_> {
            let defaults = (0..params.len()).map(|i| body.ck.field_default(id, i).cloned());
            defaults.collect()
        };
        let mut defaults = field_defaults(self);
        let binding = self.bind_args(&params, &defaults, args, true, span);
        // The defaults are folded when the first of them is used.
        let mut used = (0..)
            .zip(&defaults)
            .filter(|(i, _)| !binding.contains(&Some(*i)));
        let pending = used.any(|(_, default)| matches!(default, Some(DefaultValue::Pending)));
        if pending && self.folded(item, &ty, span) {
            defaults = field_defaults(self);
        }
        let checked = args.iter().map(|_| None).collect();
        self.bound_args(&params, &defaults, args, binding, checked)
    }
}

/// The first of the parameters `params` that `expr` names, and where. With
/// `types` they are type parameters, which a type may name too. No item or
/// local shares a type parameter's name.
fn param_in_expr<'a>(
    expr: &'a parse::Expr,
    params: &[Ident],
    types: bool,
) -> Option<(&'a str, Span)> {
    let within = |e: &'a parse::Expr| param_in_expr(e, params, types);
    let any = |exprs: &'a [parse::Expr]| exprs.iter().find_map(within);
    let in_type = |ty: &'a parse::Type| match types {
        true => param_in_type(ty, params, false),
        false => None,
    };
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
        | ExprKind::AddrOf(_, inner) => within(inner),
        ExprKind::Repeat(a, b)
        | ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::Pipe(a, b) => within(a).or_else(|| within(b)),
        ExprKind::Call(callee, args) => {
            within(callee).or_else(|| args.iter().find_map(|arg| within(&arg.value)))
        }
        ExprKind::Cast(value, ty) => within(value).or_else(|| in_type(ty)),
        ExprKind::FnType(ty) => in_type(ty),
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

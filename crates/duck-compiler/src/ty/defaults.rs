//! Defaults: the constant a struct's field has where a constructor gives it
//! no value, and a function's parameter where a call gives it no argument.
//! Each is folded once, and every instance of a generic struct or function
//! shares its declaration's. They are folded with the globals and enum
//! members, which may use them as they may use those: a field's with its
//! struct, and a parameter's with its function.

use crate::ir::Const;
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, Arg, ExprKind, FnSig, Ident, StructDecl, TypeKind};

use super::{Body, Checker, Dep, StructId, Ty, TypeErrorKind, Value, param_names};

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
    /// Checks and folds the defaults of struct `id`'s fields. A field that
    /// a `use` makes one of them has the default of the field it is, which
    /// is folded first.
    pub(super) fn define_defaults(&mut self, program: &Program, id: StructId, decl: &StructDecl) {
        for index in 0..self.structs[id.0 as usize].fields.len() {
            let field = &self.structs[id.0 as usize].fields[index];
            let (Some((used, at)), Some(_), span) = (field.used, &field.default, field.span) else {
                continue;
            };
            let def = &self.structs[used.0 as usize];
            let (item, name) = (def.item, def.name.clone());
            let (default, default_ty) = match self.folded(Some(program), item, &name, span) {
                true => (
                    self.field_default(used, at).cloned(),
                    self.field_default_ty(used, at),
                ),
                false => (Some(DefaultValue::Failed), None),
            };
            let field = &mut self.structs[id.0 as usize].fields[index];
            (field.default, field.default_ty) = (default, default_ty);
        }
        for field in decl.entries.iter().filter_map(parse::Entry::own) {
            let Some(expr) = &field.default else {
                continue;
            };
            let fields = &self.structs[id.0 as usize].fields;
            // A repeated field isn't one of the struct's.
            let Some(index) = fields.iter().position(|def| def.span == field.span) else {
                continue;
            };
            let ty = fields[index].ty;
            let names = param_names(&decl.params);
            let tys = self.structs[id.0 as usize].params.clone();
            let (consts, own) = self.fold_default(program, ty, expr, &names, &tys);
            let field = &mut self.structs[id.0 as usize].fields[index];
            field.default_ty = own;
            field.default = Some(match consts {
                Some(consts) => DefaultValue::Folded(consts),
                None => DefaultValue::Failed,
            });
        }
    }

    /// Checks and folds the defaults of the parameters of function `id`,
    /// which isn't generic and has the signature `sig`.
    pub(super) fn define_param_defaults(&mut self, program: &Program, id: usize, sig: &FnSig) {
        let params = self.funcs[id].params.clone();
        self.funcs[id].defaults = self.fold_param_defaults(program, sig, &params, &[]).0;
    }

    /// The default of each parameter of `sig` that has one, checked and
    /// folded. `params` are its parameters as resolved, and `tys` its type
    /// parameters. With them is the type of each default that has one of
    /// its own, as [`Self::fold_default`] finds.
    pub(super) fn fold_param_defaults(
        &mut self,
        program: &Program,
        sig: &FnSig,
        params: &[(String, Ty)],
        tys: &[Ty],
    ) -> (Vec<Option<DefaultValue>>, Vec<Option<Ty>>) {
        let names: Vec<_> = sig.params.iter().map(|param| param.name.clone()).collect();
        let type_names = sig.type_param_names();
        let (mut defaults, mut own) = (Vec::new(), Vec::new());
        for (param, (_, ty)) in sig.params.iter().zip(params) {
            own.push(None);
            let Some(expr) = &param.default else {
                defaults.push(None);
                continue;
            };
            // A type parameter has none, which is reported where it's
            // declared.
            if param.ty.is_type() {
                defaults.push(Some(DefaultValue::Failed));
                continue;
            }
            // The default is folded once for every call, none of whose
            // arguments it can read. A global of the name isn't meant.
            let named = param_in_expr(expr, &names, false);
            let consts = match named.map(|(name, span)| (name.to_string(), span)) {
                Some((name, span)) => {
                    self.error(TypeErrorKind::DefaultReadsParam(name), span);
                    None
                }
                None => {
                    let (consts, found) = self.fold_default(program, *ty, expr, &type_names, tys);
                    own.pop();
                    own.push(found);
                    consts
                }
            };
            defaults.push(Some(match consts {
                Some(consts) => DefaultValue::Folded(consts),
                None => DefaultValue::Failed,
            }));
        }
        (defaults, own)
    }

    /// The folded value of `expr`, the default of a field or parameter of
    /// type `ty` in a struct or function whose type parameters are `tys`,
    /// named `names`. `None` after reporting an error, or if `ty` is the
    /// error type.
    ///
    /// A default needn't have the type `ty` as declared: it may have one of
    /// the types that `ty` stands for, as a `&Heap` is one of those a `&A`
    /// stands for. That type is given with the value. A call that leaves
    /// the argument out takes its type parameters from it, where no
    /// argument settles them, and it is the default only where the
    /// parameter or field then has that type.
    fn fold_default(
        &mut self,
        program: &Program,
        ty: Ty,
        expr: &parse::Expr,
        names: &[Ident],
        tys: &[Ty],
    ) -> (Option<Vec<Const>>, Option<Ty>) {
        if let Some((name, span)) = param_in_expr(expr, names, true) {
            self.error(TypeErrorKind::DefaultUsesParam(name.to_string()), span);
            return (None, None);
        }
        let errors = self.errors.len();
        let mut body = Body::new(self, Ty::Unit);
        body.global = Some(program);
        body.default = true;
        let (found, value) = body.expr(expr, Some(ty));
        let locals = body.locals;
        let mut own = None;
        if self.fits(found, ty) || found == Ty::Error || ty == Ty::Error {
            // It is folded once for every instance, so it isn't a value
            // laid out by a type parameter.
            if let Some(param) = self.held_param(ty, true) {
                let kind = TypeErrorKind::DefaultUsesParam(self.param_name(param));
                self.error(kind, expr.span);
            }
        } else {
            let mut bound = vec![None; tys.len()];
            self.unify(ty, found, &mut bound);
            let args = tys
                .iter()
                .zip(bound)
                .map(|(param, arg)| arg.unwrap_or(*param));
            let args: Vec<_> = args.collect();
            let stood = self.substitute(ty, &args, expr.span);
            if self.has_param(found) || !self.fits(found, stood) {
                let kind = TypeErrorKind::Mismatch {
                    expected: self.ty_name(ty),
                    found: self.ty_name(found),
                };
                self.error(kind, expr.span);
            } else if self.check_bounds(tys, &args, expr.span) {
                own = Some(found);
            }
        }
        let consts = self.evaluate(program, locals, value, expr.span);
        let folded = self.errors.len() == errors && ty != Ty::Error;
        (consts.filter(|_| folded), own.filter(|_| folded))
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

    /// The type of the default of field `index` of struct `id`, if it has
    /// one of its own, read from its declaration as the default is.
    fn field_default_ty(&self, id: StructId, index: usize) -> Option<Ty> {
        let def = &self.structs[id.0 as usize];
        let decl = def
            .instance
            .as_ref()
            .map_or(id, |instance| instance.generic);
        self.structs[decl.0 as usize].fields[index].default_ty
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
        // A default names what a constant built with it may call.
        self.ck.note(Dep::Item(item));
        // A default with a type of its own is taken only as that type.
        for (i, (name, expected)) in params.iter().enumerate() {
            let own = self.ck.field_default_ty(id, i);
            let Some(own) = own.filter(|_| !binding.contains(&Some(i))) else {
                continue;
            };
            if !self.ck.fits(own, *expected) && *expected != Ty::Error {
                let kind = TypeErrorKind::DefaultMismatch {
                    param: name.clone(),
                    expected: self.ck.ty_name(*expected),
                    found: self.ck.ty_name(own),
                };
                self.error(kind, span);
            }
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
        | ExprKind::Placeholder
        | ExprKind::Dot(_)
        | ExprKind::Break
        | ExprKind::Continue
        | ExprKind::Todo => None,
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
        ExprKind::Cast(value, ty, _) => within(value).or_else(|| in_type(ty)),
        ExprKind::FnType(ty) => in_type(ty),
        ExprKind::Assign { target, value, .. } => within(target).or_else(|| within(value)),
        ExprKind::Return(value) => value.as_deref().and_then(within),
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
            let mut args = args.iter().flatten();
            named.or_else(|| args.find_map(|arg| param_in_type(&arg.ty, params, false)))
        }
        TypeKind::Pointer(_, pointee) => param_in_type(pointee, params, false),
        TypeKind::Qualified(_, inner) => param_in_type(inner, params, true),
        TypeKind::Fn(args, ret) => any(args).or_else(|| {
            ret.as_deref()
                .and_then(|ret| param_in_type(ret, params, false))
        }),
        TypeKind::Todo => None,
    }
}

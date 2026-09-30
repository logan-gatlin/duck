//! Generic structs: resolving their declarations with type parameters,
//! rejecting ones with infinitely many or infinitely large instances, and
//! instantiating them with type arguments, including those written in
//! expressions, like the `i32` in `Box(i32)(value: 1)`.

use crate::lex::Span;
use crate::parse::{self, Arg, ExprKind, Ident, TypeKind};

use super::{
    ARRAY, Body, Checker, Item, StructDef, StructId, TUPLE, Ty, TypeErrorKind, Value,
    is_builtin_type,
};

/// A use of a generic struct with type arguments.
pub(super) struct Instance {
    pub(super) generic: StructId,
    pub(super) args: Vec<Ty>,
    /// Where it was first used, which errors in its fields are reported at.
    pub(super) site: Span,
}

/// A type parameter of a generic struct.
pub(super) struct ParamDef {
    pub(super) name: String,
    /// Position in the struct's type parameters.
    pub(super) index: usize,
}

/// A type argument of a generic declaration's field that holds one of the
/// declaration's type parameters, which it passes on to another generic.
#[derive(Clone, Copy)]
struct Flow {
    from: FieldRef,
    /// The generic declaration it passes the type argument to.
    to: StructId,
    /// Whether the type parameter is wrapped in a larger type, as in `&T`
    /// or `Box(T)`, rather than passed as is.
    expands: bool,
}

/// Which lists of type arguments a type takes.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Arity {
    /// No list: the type is written by name alone.
    Plain,
    /// A list of exactly this many.
    Exactly(usize),
    /// A list that is empty or has at least this many.
    NoneOrAtLeast(usize),
}

/// A field of a struct, by position.
#[derive(Clone, Copy, PartialEq, Eq)]
struct FieldRef {
    owner: StructId,
    index: usize,
}

impl Arity {
    /// Whether a type with this arity is written with a list of type
    /// arguments.
    pub(super) fn takes_args(self) -> bool {
        self != Self::Plain
    }

    /// The error for writing the type `name` with `args` type arguments, or
    /// with no list if `None`. `None` if the type takes them.
    pub(super) fn check(self, name: &str, args: Option<usize>) -> Option<TypeErrorKind> {
        let name = name.to_string();
        match (self, args) {
            (Self::Plain, None) => None,
            (Self::Plain, Some(_)) => Some(TypeErrorKind::NotGeneric(name)),
            (_, None) => Some(TypeErrorKind::MissingTypeArgs(name)),
            (Self::Exactly(expected), Some(found)) if found != expected => {
                Some(TypeErrorKind::TypeArgCount {
                    name,
                    expected,
                    found,
                })
            }
            (Self::NoneOrAtLeast(at_least), Some(found)) if found != 0 && found < at_least => {
                Some(TypeErrorKind::TooFewTypeArgs {
                    name,
                    at_least,
                    found,
                })
            }
            _ => None,
        }
    }
}

impl Checker {
    /// Brings the type parameters of struct `id` into scope, reporting
    /// repeated ones and ones named after a type.
    pub(super) fn declare_type_params(&mut self, id: usize, params: &[Ident]) {
        for (i, param) in params.iter().enumerate() {
            if params[..i].iter().any(|p| p.name == param.name) {
                self.error(
                    TypeErrorKind::DuplicateParam(param.name.clone()),
                    param.span,
                );
            } else if is_builtin_type(&param.name)
                || matches!(
                    self.items.get(&param.name),
                    Some(Item::Struct(_) | Item::Enum(_))
                )
            {
                self.error(TypeErrorKind::DuplicateItem(param.name.clone()), param.span);
            } else {
                let ty = self.structs[id].params[i];
                self.type_params.push((param.name.clone(), ty));
            }
        }
    }

    /// Whether struct `id` is a generic declaration, or an instance whose type
    /// arguments hold type parameters. Neither is ever laid out.
    pub(super) fn is_open(&self, id: StructId) -> bool {
        let def = &self.structs[id.0 as usize];
        match &def.instance {
            Some(instance) => instance.args.iter().any(|arg| self.has_param(*arg)),
            None => !def.params.is_empty(),
        }
    }

    /// Whether `ty` holds a type parameter anywhere within it.
    fn has_param(&self, ty: Ty) -> bool {
        match ty {
            Ty::Param(_) => true,
            Ty::Struct(id) => self.is_open(id) && self.structs[id.0 as usize].instance.is_some(),
            _ => self
                .components(ty)
                .into_iter()
                .any(|component| self.has_param(component)),
        }
    }

    /// Reports each field of a generic declaration that passes a type
    /// parameter, wrapped in a larger type, around a cycle of generic
    /// structs back to itself, and cuts the cycle by giving the field the
    /// error type. Such a struct would have infinitely many instances.
    pub(super) fn break_expansions(&mut self, decl_count: usize) {
        let mut edges = Vec::new();
        for id in 0..decl_count {
            for (index, field) in self.structs[id].fields.iter().enumerate() {
                let owner = StructId(id as u32);
                self.push_param_flows(field.ty, FieldRef { owner, index }, &mut edges);
            }
        }
        let mut cut = Vec::new();
        for edge in &edges {
            if edge.expands
                && !cut.contains(&edge.from)
                && flows_to(&edges, &cut, edge.to, edge.from.owner)
            {
                let def = &mut self.structs[edge.from.owner.0 as usize];
                let field = &mut def.fields[edge.from.index];
                field.ty = Ty::Error;
                let (kind, span) = (
                    TypeErrorKind::ExpansiveRecursion(def.name.clone()),
                    field.span,
                );
                self.error(kind, span);
                cut.push(edge.from);
            }
        }
    }

    /// Pushes a flow for each type argument in `ty` that holds a type
    /// parameter of the declaration whose field `from` is.
    fn push_param_flows(&self, ty: Ty, from: FieldRef, out: &mut Vec<Flow>) {
        let Ty::Struct(id) = ty else {
            for component in self.components(ty) {
                self.push_param_flows(component, from, out);
            }
            return;
        };
        let Some(instance) = &self.structs[id.0 as usize].instance else {
            return;
        };
        for arg in &instance.args {
            if self.has_param(*arg) {
                out.push(Flow {
                    from,
                    to: instance.generic,
                    expands: !matches!(arg, Ty::Param(_)),
                });
            }
            self.push_param_flows(*arg, from, out);
        }
    }

    /// Reads a type written as an expression, such as the `Box(&i32)` in
    /// `Box(&i32)(value: p)`. `None` after reporting an error.
    fn type_syntax(&mut self, expr: &parse::Expr) -> Option<parse::Type> {
        let kind = match &expr.kind {
            ExprKind::Name(name) => TypeKind::Named(name.clone(), None),
            ExprKind::Call(callee, args) => {
                let ExprKind::Name(name) = &callee.kind else {
                    self.error(TypeErrorKind::NotAType, callee.span);
                    return None;
                };
                return self.applied_type_syntax(name, args, expr.span);
            }
            ExprKind::AddrOf(pointee) => TypeKind::Pointer(Box::new(self.type_syntax(pointee)?)),
            _ => {
                self.error(TypeErrorKind::NotAType, expr.span);
                return None;
            }
        };
        Some(parse::Type {
            kind,
            span: expr.span,
        })
    }

    /// Reads `name(args)`, written as an expression spanning `span`, as the
    /// type `name` given type arguments. `None` after reporting an error.
    fn applied_type_syntax(&mut self, name: &str, args: &[Arg], span: Span) -> Option<parse::Type> {
        let mut types = Vec::new();
        for arg in args {
            if let Some(label) = &arg.label {
                self.error(TypeErrorKind::LabelledTypeArg, label.span);
            }
            types.push(self.type_syntax(&arg.value));
        }
        let types = types.into_iter().collect::<Option<_>>()?;
        Some(parse::Type {
            kind: TypeKind::Named(name.to_string(), Some(types)),
            span,
        })
    }

    /// Which lists of type arguments the type `name` takes. `None` for names
    /// that aren't types.
    pub(super) fn type_arity(&self, name: &str) -> Option<Arity> {
        match self.items.get(name) {
            _ if name == ARRAY => Some(Arity::Exactly(1)),
            _ if name == TUPLE => Some(Arity::NoneOrAtLeast(2)),
            Some(Item::Struct(id)) => match self.structs[id.0 as usize].params.len() {
                0 => Some(Arity::Plain),
                n => Some(Arity::Exactly(n)),
            },
            Some(Item::Enum(_)) => Some(Arity::Plain),
            _ if is_builtin_type(name) => Some(Arity::Plain),
            _ => None,
        }
    }

    /// Whether `name` is a type written with a list of type arguments.
    pub(super) fn takes_type_args(&self, name: &str) -> bool {
        self.type_arity(name).is_some_and(Arity::takes_args)
    }

    /// The instance of generic struct `generic` with type arguments `args`,
    /// first used at `site`. Instances are given their fields as soon as
    /// every generic struct is defined, and reported at `site` if a pointer
    /// in them can't be stored once every struct is.
    pub(super) fn instantiate(&mut self, generic: StructId, args: Vec<Ty>, site: Span) -> Ty {
        if let Some(id) = self.instances.get(&(generic, args.clone())) {
            return Ty::Struct(*id);
        }
        let id = StructId(self.structs.len() as u32);
        let names: Vec<_> = args.iter().map(|arg| self.ty_name(*arg)).collect();
        self.structs.push(StructDef {
            name: format!(
                "{}({})",
                self.structs[generic.0 as usize].name,
                names.join(", ")
            ),
            params: Vec::new(),
            instance: Some(Instance {
                generic,
                args: args.clone(),
                site,
            }),
            fields: Vec::new(),
        });
        self.instances.insert((generic, args), id);
        if self.is_open(id) {
            return Ty::Struct(id);
        }
        if !self.generics_defined {
            self.pending.push(id);
            return Ty::Struct(id);
        }
        let first_new = id.0 as usize;
        self.fill_instance(id);
        if self.structs_defined {
            self.check_field_pointers(first_new..self.structs.len());
        }
        Ty::Struct(id)
    }

    /// Gives instance `id` the fields of its generic declaration, with type
    /// arguments in place of type parameters.
    pub(super) fn fill_instance(&mut self, id: StructId) {
        let instance = self.structs[id.0 as usize].instance.as_ref().unwrap();
        let (generic, args, site) = (instance.generic, instance.args.clone(), instance.site);
        let mut fields = self.structs[generic.0 as usize].fields.clone();
        for field in &mut fields {
            field.ty = self.substitute(field.ty, &args, site);
        }
        self.structs[id.0 as usize].fields = fields;
    }

    /// `ty` with each type parameter replaced by its argument in `args`.
    fn substitute(&mut self, ty: Ty, args: &[Ty], site: Span) -> Ty {
        match ty {
            Ty::Param(id) => args[self.params[id.0 as usize].index],
            Ty::Struct(id) => match &self.structs[id.0 as usize].instance {
                Some(instance) if self.is_open(id) => {
                    let (generic, inner) = (instance.generic, instance.args.clone());
                    let inner = inner
                        .into_iter()
                        .map(|arg| self.substitute(arg, args, site))
                        .collect();
                    self.instantiate(generic, inner, site)
                }
                _ => ty,
            },
            _ => {
                let components = self
                    .components(ty)
                    .into_iter()
                    .map(|component| self.substitute(component, args, site))
                    .collect();
                self.rebuild(ty, components)
            }
        }
    }
}

impl Body<'_> {
    /// A generic type `name` called directly: as `Box(i32)`, a type used as a
    /// value, or as `Box(value: 1)`, a constructor missing type arguments.
    pub(super) fn generic_call(
        &mut self,
        name: &str,
        callee: &parse::Expr,
        args: &[Arg],
        span: Span,
    ) -> (Ty, Value) {
        if args.iter().all(|arg| arg.label.is_none()) {
            let ty = match self.ck.applied_type_syntax(name, args, span) {
                Some(ty) => self.ck.resolve_ty(&ty),
                None => Ty::Error,
            };
            return self.type_value(ty, span);
        }
        // The arguments may be fields or mislabelled type arguments, so they
        // aren't checked.
        self.error(
            TypeErrorKind::MissingTypeArgs(name.to_string()),
            callee.span,
        );
        (Ty::Error, Value::default())
    }

    /// Resolves a type written as an expression.
    pub(super) fn expr_type(&mut self, expr: &parse::Expr) -> Ty {
        match self.ck.type_syntax(expr) {
            Some(ty) => self.ck.resolve_ty(&ty),
            None => Ty::Error,
        }
    }

    /// Whether `expr(args)` gives a type its type arguments, rather than
    /// building a struct that is then called. A generic type always takes
    /// type arguments; any other struct is taken to when none are labelled,
    /// so that giving it some is reported.
    pub(super) fn names_type(&self, expr: &parse::Expr, args: &[Arg]) -> bool {
        match &expr.kind {
            ExprKind::Name(name) if self.lookup(name).is_none() => {
                self.ck.takes_type_args(name)
                    || matches!(self.ck.items.get(name), Some(Item::Struct(_)))
                        && args.iter().all(|arg| arg.label.is_none())
            }
            _ => false,
        }
    }
}

/// Whether type parameters flow from declaration `from` to `to` along
/// `edges`, not counting those from the fields in `cut`.
fn flows_to(edges: &[Flow], cut: &[FieldRef], from: StructId, to: StructId) -> bool {
    let mut seen = vec![from];
    let mut stack = vec![from];
    while let Some(id) = stack.pop() {
        if id == to {
            return true;
        }
        for edge in edges
            .iter()
            .filter(|e| e.from.owner == id && !cut.contains(&e.from))
        {
            if !seen.contains(&edge.to) {
                seen.push(edge.to);
                stack.push(edge.to);
            }
        }
    }
    false
}

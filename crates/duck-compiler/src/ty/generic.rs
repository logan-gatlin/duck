//! Generic structs: resolving their declarations with type parameters,
//! rejecting ones with infinitely many or infinitely large instances, and
//! instantiating them with type arguments, including those written in
//! expressions, like the `i32` in `Box(i32)(value: 1)`.

use std::mem;

use crate::lex::Span;
use crate::parse::{self, Arg, ExprKind, Ident, TypeKind, TypeParam};

use super::{
    ARRAY, Body, Checker, FieldDef, Item, OPTION, ParamId, RESULT, StructDef, StructId, TUPLE, Ty,
    TypeErrorKind, VARRAY, Value, Visit, is_builtin_type, module_path, path_text,
};

/// A use of a generic struct with type arguments.
pub(super) struct Instance {
    pub(super) generic: StructId,
    pub(super) args: Vec<Ty>,
    /// Where it was first used, which errors in its fields are reported at.
    pub(super) site: Span,
    /// Whether it has been given its fields.
    filled: bool,
    /// Whether it holds values nested too deep, or would if its fields
    /// weren't cut short, so that nothing is made of it.
    pub(super) too_deep: bool,
}

/// A type parameter of a generic struct or function.
pub(super) struct ParamDef {
    pub(super) name: String,
    /// Position in its declaration's type parameters.
    pub(super) index: usize,
    /// The struct whose fields its type arguments start with, once it is
    /// resolved, if the type parameter is bounded.
    pub(super) bound: Option<Ty>,
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
    /// A new [`Ty::Param`] for each of a declaration's type parameters.
    pub(super) fn new_params(&mut self, params: &[Ident]) -> Vec<Ty> {
        params
            .iter()
            .enumerate()
            .map(|(index, param)| {
                self.params.push(ParamDef {
                    name: param.name.clone(),
                    index,
                    bound: None,
                });
                Ty::Param(ParamId(self.params.len() as u32 - 1))
            })
            .collect()
    }

    /// The type that type parameter `name` stands for, if one is in scope.
    pub(super) fn type_param(&self, name: &str) -> Option<Ty> {
        let param = self.type_params.iter().find(|(param, _)| param == name);
        param.map(|(_, ty)| *ty)
    }

    /// The name of type parameter `param`, a [`Ty::Param`].
    pub(super) fn param_name(&self, param: Ty) -> String {
        match param {
            Ty::Param(id) => self.params[id.0 as usize].name.clone(),
            _ => unreachable!("type parameters are `Ty::Param`"),
        }
    }

    /// Brings a declaration's type parameters, whose types are `tys`, into
    /// scope, reporting repeated ones and ones named after a type or item.
    pub(super) fn declare_type_params(&mut self, params: &[Ident], tys: &[Ty]) {
        for (i, param) in params.iter().enumerate() {
            if params[..i].iter().any(|p| p.name == param.name) {
                self.error(
                    TypeErrorKind::DuplicateParam(param.name.clone()),
                    param.span,
                );
            } else if is_builtin_type(&param.name) || self.item(&param.name).is_some() {
                self.error(TypeErrorKind::DuplicateItem(param.name.clone()), param.span);
            } else {
                self.type_params.push((param.name.clone(), tys[i]));
            }
        }
    }

    /// Resolves the bound of each of a declaration's type parameters
    /// `params` that has one, whose types are `tys`. A bound is a struct, a
    /// union, an enum or an array, and of `params` it names only those
    /// before its own, so that no bound leads back to itself. Any other is
    /// reported and bounds nothing.
    pub(super) fn resolve_bounds(&mut self, params: &[TypeParam], tys: &[Ty]) {
        for (i, (param, ty)) in params.iter().zip(tys).enumerate() {
            let (Some(written), Ty::Param(id)) = (&param.bound, *ty) else {
                continue;
            };
            let bound = self.resolve_ty(written);
            if !matches!(
                bound,
                Ty::Struct(_) | Ty::Enum(_) | Ty::Array(_) | Ty::Error
            ) {
                self.error(TypeErrorKind::NotABound(self.ty_name(bound)), written.span);
                continue;
            }
            let later = &tys[i..params.len()];
            if let Some(later) = later.iter().find(|later| self.holds(bound, **later)) {
                let (bound, param) = (self.ty_name(bound), self.param_name(*later));
                let kind = TypeErrorKind::BoundNamesLater { bound, param };
                self.error(kind, written.span);
                continue;
            }
            self.params[id.0 as usize].bound = Some(bound);
        }
    }

    /// What is known of `ty` where it is declared: the bound of a bounded
    /// type parameter, which its type arguments are laid out as where the
    /// body of a generic function is checked as declared. Any other type
    /// is itself.
    pub(super) fn known(&self, ty: Ty) -> Ty {
        match ty {
            Ty::Param(id) => self.params[id.0 as usize].bound.unwrap_or(ty),
            _ => ty,
        }
    }

    /// Whether a `ty` is a type that `bound` bounds.
    ///
    /// A struct is bounded by one that it starts as: it has as many fields
    /// or more, of which those that `bound` has are named and typed as its
    /// are, in order. So a field of `bound` is where it would be in a `ty`,
    /// in memory and among its leaves.
    ///
    /// A union is bounded by one that starts as it does, and so is an
    /// enum: `ty` has as many variants or members or fewer, which are
    /// named, and hold or are what the first of `bound` do, in order. So
    /// every value of a `ty` is the same variant or member of `bound`.
    ///
    /// Either way, what `ty` holds [fits](Self::fits) where `bound` holds
    /// it: a `&var T` or a `varray(T)` is where `bound` has one that only
    /// reads.
    ///
    /// An array bounds those that fit it, and the structs that start as
    /// one: their first fields are its `ptr` and `len`.
    ///
    /// A type parameter is bounded by what its own bound is.
    pub(super) fn meets(&self, ty: Ty, bound: Ty) -> bool {
        self.starts_like(ty, bound, false)
    }

    /// Whether a `ty` starts as `bound` does, as one that [meets] it does.
    /// If `exact`, what it holds is also typed just as what `bound` holds
    /// is: nothing that writes its memory is where `bound` only reads it.
    /// So a `ty` can be written as a `bound` is, through a pointer to one.
    ///
    /// [meets]: Self::meets
    pub(super) fn starts_like(&self, ty: Ty, bound: Ty, exact: bool) -> bool {
        let fits = |found: Ty, want: Ty| found == want || !exact && self.fits(found, want);
        let ty = self.known(ty);
        if ty == bound || ty == Ty::Error || bound == Ty::Error {
            return true;
        }
        match (ty, bound) {
            (Ty::Struct(have), Ty::Struct(want)) => {
                let (have, want) = (
                    &self.structs[have.0 as usize],
                    &self.structs[want.0 as usize],
                );
                match (have.union, want.union) {
                    (false, false) => starts_as(&have.fields, &want.fields, fits),
                    (true, true) => {
                        let fits = |field, first| fits(first, field);
                        starts_as(&want.fields, &have.fields, fits)
                    }
                    _ => false,
                }
            }
            // An array, or a struct that starts as one, whose `ptr` is
            // where `bound` has its own.
            (_, Ty::Array(want)) => {
                let want = self.arrays[want.0 as usize];
                self.array_ptr(ty).is_some_and(|ptr| fits(ptr, want))
            }
            (Ty::Enum(have), Ty::Enum(want)) => self.enum_starts_as(want, have),
            _ => false,
        }
    }

    /// Whether `ty` is a union or an enum.
    pub(super) fn is_sum(&self, ty: Ty) -> bool {
        matches!(ty, Ty::Enum(_)) || self.union_id(ty).is_some()
    }

    /// Whether whether `ty` is bounded by another type isn't known yet: it
    /// is an enum whose members' values aren't folded.
    fn unfolded(&self, ty: Ty) -> bool {
        matches!(self.known(ty), Ty::Enum(id) if !self.enum_folded(id))
    }

    /// The type that a field named `field` is looked up in, as a field of a
    /// `ty`: the bound of a bounded type parameter, and otherwise `ty`
    /// itself. An instance of a generic function looks it up in the bound
    /// too, as its declaration did, with its type arguments in place of the
    /// type parameters the bound names: its type argument starts as the
    /// bound does, so the field is where the bound has it, and what sees
    /// the field in the bound reads it whether or not the type argument's
    /// own is `pub`.
    pub(super) fn read_as(&mut self, ty: Ty, field: &Ident) -> Ty {
        let key = (field.span.file, field.span.start);
        let bound = self.known(ty);
        if bound != ty {
            self.bound_uses.insert(key, bound);
            return bound;
        }
        match self.bound_uses.get(&key) {
            Some(bound) if !self.instance_chain.is_empty() => {
                let args: Vec<_> = self.type_params.iter().map(|(_, arg)| *arg).collect();
                self.substitute(*bound, &args, field.span)
            }
            _ => ty,
        }
    }

    /// Reports, at `site`, each of the type arguments `args` that doesn't
    /// start as the bound of its type parameter does, one of `params`, once
    /// the bound has `args` in place of the type parameters it names.
    /// Whether none was.
    pub(super) fn check_bounds(&mut self, params: &[Ty], args: &[Ty], site: Span) -> bool {
        let mut met = true;
        for (param, arg) in params.iter().zip(args) {
            let Ty::Param(id) = *param else {
                continue;
            };
            let Some(bound) = self.params[id.0 as usize].bound else {
                continue;
            };
            let bound = self.substitute(bound, args, site);
            // An enum is compared once its members' values are folded.
            if self.unfolded(*arg) || self.unfolded(bound) {
                self.pending_bounds.push((*arg, bound, site));
            } else if !self.meets(*arg, bound) {
                self.bound_error(*arg, bound, site);
                met = false;
            }
        }
        met
    }

    /// Reports, at `site`, that a `ty` isn't a type that `bound` bounds.
    fn bound_error(&mut self, ty: Ty, bound: Ty, site: Span) {
        let what = match bound {
            Ty::Enum(_) => Some("members"),
            _ if self.union_id(bound).is_some() => Some("variants"),
            _ => None,
        };
        let (ty, bound) = (self.ty_name(ty), self.ty_name(bound));
        let kind = match what {
            Some(what) => TypeErrorKind::NotWithin { ty, bound, what },
            None => TypeErrorKind::BoundNotMet { ty, bound },
        };
        self.error(kind, site);
    }

    /// Checks the type arguments that were given a type parameter bounded
    /// by an enum, or were an enum, before every enum's members were
    /// folded.
    pub(super) fn check_pending_bounds(&mut self) {
        for (ty, bound, site) in mem::take(&mut self.pending_bounds) {
            if !self.meets(ty, bound) {
                self.bound_error(ty, bound, site);
            }
        }
    }

    /// Checks the type arguments of struct `id`, if it's an instance,
    /// against the bounds of its declaration's type parameters, which is
    /// done once every struct has its fields.
    pub(super) fn check_instance_bounds(&mut self, id: StructId) {
        let Some(instance) = &self.structs[id.0 as usize].instance else {
            return;
        };
        let (args, site) = (instance.args.clone(), instance.site);
        let params = self.structs[instance.generic.0 as usize].params.clone();
        self.check_bounds(&params, &args, site);
    }

    /// Whether struct `id` is a generic declaration, or an instance whose type
    /// arguments hold type parameters. No value of either is ever run.
    pub(super) fn is_open(&self, id: StructId) -> bool {
        let def = &self.structs[id.0 as usize];
        match &def.instance {
            Some(instance) => instance.args.iter().any(|arg| self.has_param(*arg)),
            None => !def.params.is_empty(),
        }
    }

    /// Whether `ty` holds a type parameter anywhere within it.
    pub(super) fn has_param(&self, ty: Ty) -> bool {
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
            ExprKind::Name(_) | ExprKind::Field(..) => {
                return self.path_type(expr, None, expr.span);
            }
            ExprKind::Call(callee, args) => {
                return self.applied_type_syntax(callee, args, expr.span);
            }
            ExprKind::AddrOf(mutability, pointee) => {
                TypeKind::Pointer(*mutability, Box::new(self.type_syntax(pointee)?))
            }
            ExprKind::FnType(ty) => return Some(ty.clone()),
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

    /// Reads `callee(args)`, written as an expression spanning `span`, as
    /// the type `callee` names given type arguments. `None` after reporting
    /// an error.
    pub(super) fn applied_type_syntax(
        &mut self,
        callee: &parse::Expr,
        args: &[Arg],
        span: Span,
    ) -> Option<parse::Type> {
        let args = self.type_args_syntax(args)?;
        self.path_type(callee, Some(args), span)
    }

    /// Reads `path`, a name or `module.name`, as the type it names, given
    /// type arguments `args` if any, written as an expression spanning
    /// `span`. `None` after reporting an error.
    fn path_type(
        &mut self,
        path: &parse::Expr,
        args: Option<Vec<parse::Type>>,
        span: Span,
    ) -> Option<parse::Type> {
        let (modules, name) = match &path.kind {
            ExprKind::Name(name) => (
                Vec::new(),
                Ident {
                    name: name.clone(),
                    span: path.span,
                },
            ),
            ExprKind::Field(inner, field) => match module_path(inner) {
                Some(modules) => (modules, field.clone()),
                None => {
                    self.error(TypeErrorKind::NotAType, inner.span);
                    return None;
                }
            },
            _ => {
                self.error(TypeErrorKind::NotAType, path.span);
                return None;
            }
        };
        let mut ty = parse::Type {
            kind: TypeKind::Named(name.name, args),
            span: Span {
                start: name.span.start,
                ..span
            },
        };
        for module in modules.into_iter().rev() {
            ty = parse::Type {
                kind: TypeKind::Qualified(module, Box::new(ty)),
                span,
            };
        }
        Some(ty)
    }

    /// Reads `args`, written as expressions, as a list of type arguments.
    /// `None` after reporting an error.
    fn type_args_syntax(&mut self, args: &[Arg]) -> Option<Vec<parse::Type>> {
        let mut types = Vec::new();
        for arg in args {
            if let Some(label) = &arg.label {
                self.error(TypeErrorKind::LabelledTypeArg, label.span);
            }
            types.push(self.type_syntax(&arg.value));
        }
        types.into_iter().collect()
    }

    /// Which lists of type arguments the type `name` takes. `None` for names
    /// that aren't types.
    pub(super) fn type_arity(&self, name: &str) -> Option<Arity> {
        match self.item(name) {
            _ if name == ARRAY || name == VARRAY || name == OPTION => Some(Arity::Exactly(1)),
            _ if name == RESULT => Some(Arity::Exactly(2)),
            _ if name == TUPLE => Some(Arity::NoneOrAtLeast(2)),
            Some(item @ (Item::Struct(_) | Item::Enum(_))) => self.item_arity(item),
            _ if is_builtin_type(name) => Some(Arity::Plain),
            _ => None,
        }
    }

    /// Which lists of type arguments `item` takes. `None` for items that
    /// aren't types.
    pub(super) fn item_arity(&self, item: Item) -> Option<Arity> {
        match item {
            Item::Struct(id) => match self.structs[id.0 as usize].params.len() {
                0 => Some(Arity::Plain),
                n => Some(Arity::Exactly(n)),
            },
            Item::Enum(_) => Some(Arity::Plain),
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
    /// in them can't be stored once every struct is, or if they contain
    /// themselves. One whose type arguments hold type parameters has its
    /// pointers reported once they are given theirs, which the body of a
    /// generic function checked as declared needs. The error type if a type
    /// argument is, or if the instance holds values nested too deep, which
    /// is reported.
    pub(super) fn instantiate(&mut self, generic: StructId, args: Vec<Ty>, site: Span) -> Ty {
        if args.contains(&Ty::Error) {
            return Ty::Error;
        }
        let id = match self.instances.get(&(generic, args.clone())) {
            Some(id) => *id,
            None => {
                let id = StructId(self.structs.len() as u32);
                let names: Vec<_> = args.iter().map(|arg| self.ty_name(*arg)).collect();
                let decl = &self.structs[generic.0 as usize];
                self.structs.push(StructDef {
                    name: format!("{}({})", decl.name, names.join(", ")),
                    module: decl.module,
                    item: decl.item,
                    is_pub: decl.is_pub,
                    union: decl.union,
                    params: Vec::new(),
                    instance: Some(Instance {
                        generic,
                        args: args.clone(),
                        site,
                        filled: false,
                        too_deep: false,
                    }),
                    fields: Vec::new(),
                    depth: None,
                });
                self.instances.insert((generic, args), id);
                if !self.generics_defined {
                    self.pending.push(id);
                    return Ty::Struct(id);
                }
                self.fill_instance(id);
                if self.structs_defined {
                    self.check_instances(id.0 as usize);
                    self.check_instance_bounds(id);
                }
                // Measured as soon as it has its fields, so that instances
                // which hold ever more of each other stop at the limit.
                self.value_depth(id);
                id
            }
        };
        let instance = &self.structs[id.0 as usize].instance;
        match instance.as_ref().is_some_and(|instance| instance.too_deep) {
            true => Ty::Error,
            false => Ty::Struct(id),
        }
    }

    /// Checks the instances from `first` on, which were made after every
    /// struct was defined, as those before them were then: reports each that
    /// contains itself, and each pointer in them that can't be stored.
    fn check_instances(&mut self, first: usize) {
        // Those before them are known not to contain themselves.
        let mut visits = vec![Visit::Done; first];
        visits.resize(self.structs.len(), Visit::New);
        for id in first..self.structs.len() {
            self.break_cycles(id, &mut visits, false);
            // What it holds was measured before it was all there.
            self.structs[id].depth = None;
        }
        self.check_field_pointers(first..self.structs.len());
    }

    /// Gives instance `id` the fields of its generic declaration, with type
    /// arguments in place of type parameters, unless it has them. Does
    /// nothing for a struct that is no instance.
    pub(super) fn fill_instance(&mut self, id: StructId) {
        let index = id.0 as usize;
        let Some(instance) = &mut self.structs[index].instance else {
            return;
        };
        if mem::replace(&mut instance.filled, true) {
            return;
        }
        let (generic, args, site) = (instance.generic, instance.args.clone(), instance.site);
        // Until it has its fields, it counts for nothing in what holds it.
        self.structs[index].depth = Some(0);
        let mut fields = self.structs[generic.0 as usize].fields.clone();
        let mut too_deep = false;
        for field in &mut fields {
            let ty = self.substitute(field.ty, &args, site);
            // Only an instance nested too deep is an error the declaration
            // doesn't have.
            too_deep |= ty == Ty::Error && field.ty != Ty::Error;
            field.ty = ty;
        }
        let def = &mut self.structs[index];
        def.fields = fields;
        def.depth = None;
        if let Some(instance) = &mut def.instance {
            instance.too_deep |= too_deep;
        }
    }

    /// `ty` with each type parameter replaced by its argument in `args`. The
    /// error type if that nests an instance too deep, which is reported at
    /// `site`, unless it is where the declaration is.
    pub(super) fn substitute(&mut self, ty: Ty, args: &[Ty], site: Span) -> Ty {
        match ty {
            Ty::Param(id) => args[self.params[id.0 as usize].index],
            Ty::Struct(id) => match &self.structs[id.0 as usize].instance {
                Some(instance) if self.is_open(id) => {
                    let (generic, inner) = (instance.generic, instance.args.clone());
                    // Nested too deep whatever its type parameters are.
                    self.value_depth(id);
                    let instance = &self.structs[id.0 as usize].instance;
                    if instance.as_ref().is_some_and(|instance| instance.too_deep) {
                        return Ty::Error;
                    }
                    let inner = inner
                        .into_iter()
                        .map(|arg| self.substitute(arg, args, site))
                        .collect();
                    self.instantiate(generic, inner, site)
                }
                _ => ty,
            },
            _ => {
                let components: Vec<_> = self
                    .components(ty)
                    .into_iter()
                    .map(|component| self.substitute(component, args, site))
                    .collect();
                // An instance within it is nested too deep.
                if components.contains(&Ty::Error) {
                    return Ty::Error;
                }
                self.rebuild(ty, components)
            }
        }
    }
}

impl Body<'_> {
    /// A generic type `callee` called directly: as `Box(i32)`, a type used
    /// as a value, or as `Box(value: 1)`, a constructor missing type
    /// arguments.
    pub(super) fn generic_call(
        &mut self,
        callee: &parse::Expr,
        args: &[Arg],
        span: Span,
    ) -> (Ty, Value) {
        if args.iter().all(|arg| arg.label.is_none()) {
            let ty = match self.ck.applied_type_syntax(callee, args, span) {
                Some(ty) => self.ck.resolve_ty(&ty),
                None => Ty::Error,
            };
            return self.type_value(ty, span);
        }
        // The arguments may be fields or mislabelled type arguments, so they
        // aren't checked.
        self.error(
            TypeErrorKind::MissingTypeArgs(path_text(callee)),
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
    /// type arguments; any other struct is taken to when it's given some and
    /// none are labelled, so that giving it some is reported.
    pub(super) fn names_type(&self, expr: &parse::Expr, args: &[Arg]) -> bool {
        let takes_args = match &expr.kind {
            ExprKind::Name(name) if self.lookup(name).is_none() => self.ck.takes_type_args(name),
            ExprKind::Field(..) => self
                .named(expr)
                .and_then(|item| self.ck.item_arity(item))
                .is_some_and(Arity::takes_args),
            _ => return false,
        };
        takes_args
            || matches!(self.named(expr), Some(Item::Struct(_)))
                && !args.is_empty()
                && args.iter().all(|arg| arg.label.is_none())
    }
}

/// Whether `fields` start as `first` do: there are as many or more, and
/// those that `first` has are named as its are, in order, and typed so that
/// `fits` holds of the two types. Of variants, they also hold a value or
/// none as those of `first` do.
fn starts_as(fields: &[FieldDef], first: &[FieldDef], fits: impl Fn(Ty, Ty) -> bool) -> bool {
    let mut pairs = fields.iter().zip(first);
    fields.len() >= first.len()
        && pairs.all(|(field, first)| {
            let failed = field.ty == Ty::Error || first.ty == Ty::Error;
            let typed = fits(field.ty, first.ty) || failed;
            field.name == first.name && field.bare == first.bare && typed
        })
}

/// The names of the type parameters `params`.
pub(super) fn param_names(params: &[TypeParam]) -> Vec<Ident> {
    params.iter().map(|param| param.name.clone()).collect()
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

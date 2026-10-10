//! Generic structs: resolving their declarations with type parameters,
//! rejecting ones with infinitely many or infinitely large instances, and
//! instantiating them with type arguments, including those written in
//! expressions, like the `i32` in `Box(i32)(value: 1)`.

use std::mem;

use crate::lex::Span;
use crate::parse::{self, Arg, ExprKind, Ident, TypeKind, TypeParam};

use super::{
    ARRAY, ARRAY_FIELDS, Body, Checker, FieldDef, Item, OPTION, ParamId, RESULT, StructDef,
    StructId, TUPLE, Ty, TypeErrorKind, VARRAY, Value, Visit, is_builtin_type, module_path,
    path_text,
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
    /// What its type arguments [meet](Checker::meets), once it is
    /// resolved, if the type parameter is bounded: a struct, a union, an
    /// enum, an array, or a [list](Checker::list_of) of the types that a
    /// struct uses.
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
    /// A list of any number.
    Any,
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
    /// union, an enum or an array, or a list of structs and arrays, and of
    /// `params` it names only those before its own, so that no bound leads
    /// back to itself. Any other is reported and bounds nothing.
    pub(super) fn resolve_bounds(&mut self, params: &[TypeParam], tys: &[Ty]) {
        for (i, (param, ty)) in params.iter().zip(tys).enumerate() {
            let (Some(first), Some(last), Ty::Param(id)) =
                (param.bound.first(), param.bound.last(), *ty)
            else {
                continue;
            };
            let span = Span {
                end: last.span.end,
                ..first.span
            };
            let bound = match &param.bound[..] {
                [written] => {
                    let bound = self.resolve_ty(written);
                    if !matches!(
                        bound,
                        Ty::Struct(_) | Ty::Enum(_) | Ty::Array(_) | Ty::Error
                    ) {
                        self.error(TypeErrorKind::NotABound(self.ty_name(bound)), span);
                        continue;
                    }
                    bound
                }
                listed => {
                    let uses = listed.iter().map(|written| self.listed_ty(written));
                    let uses: Vec<_> = uses.collect();
                    let list = self.list_of(uses, span);
                    if let Ty::Struct(id) = list {
                        self.list_bounds.push((id, span));
                    }
                    list
                }
            };
            let later = &tys[i..params.len()];
            if let Some(later) = later.iter().find(|later| self.holds(bound, **later)) {
                let (bound, param) = (self.ty_name(bound), self.param_name(*later));
                let kind = TypeErrorKind::BoundNamesLater { bound, param };
                self.error(kind, span);
                continue;
            }
            self.params[id.0 as usize].bound = Some(bound);
        }
    }

    /// Resolves `written`, one of the types that a bound lists: a struct or
    /// an array, as a struct uses. The error type after reporting any
    /// other.
    fn listed_ty(&mut self, written: &parse::Type) -> Ty {
        let ty = self.resolve_ty(written);
        if matches!(ty, Ty::Struct(_) | Ty::Array(_) | Ty::Error) && !self.is_sum(ty) {
            return ty;
        }
        self.error(TypeErrorKind::NotListed(self.ty_name(ty)), written.span);
        Ty::Error
    }

    /// Declares the struct that every list is an instance of. It is
    /// generic over any number of types, has no name, and is no item.
    pub(super) fn declare_list(&mut self) {
        self.list = Some(StructId(self.structs.len() as u32));
        self.structs.push(StructDef {
            name: String::new(),
            module: self.entry,
            item: 0,
            is_pub: true,
            union: false,
            params: Vec::new(),
            instance: None,
            uses: Vec::new(),
            fields: Vec::new(),
            depth: None,
        });
    }

    /// The list `(A, B)` of `uses`, written at `site`, which bounds the
    /// structs whose first `use` lines name those types: a struct that
    /// uses each of them and has no fields of its own. So a type parameter
    /// that it bounds has their fields, laid out as a type argument's are.
    /// The error type if one of `uses` is.
    fn list_of(&mut self, uses: Vec<Ty>, site: Span) -> Ty {
        let Some(list) = self.list else {
            unreachable!("the list is declared before any bound is resolved")
        };
        self.instantiate(list, uses, site)
    }

    /// The types that `ty` lists, if it's a [list](Self::list_of).
    pub(super) fn listed(&self, ty: Ty) -> Option<&[Ty]> {
        let Ty::Struct(id) = ty else {
            return None;
        };
        let instance = self.structs[id.0 as usize].instance.as_ref()?;
        (Some(instance.generic) == self.list).then_some(&instance.args[..])
    }

    /// Reports each list that bounds a type parameter and names a type or
    /// a field twice, as no struct does, so that nothing meets it.
    pub(super) fn check_lists(&mut self) {
        for (id, span) in mem::take(&mut self.list_bounds) {
            let def = &self.structs[id.0 as usize];
            let twice = (0..def.uses.len()).find(|i| def.uses[..*i].contains(&def.uses[*i]));
            if let Some(twice) = twice {
                let kind = TypeErrorKind::ListedTwice(self.ty_name(def.uses[twice]));
                self.error(kind, span);
                continue;
            }
            let mut names: Vec<String> = Vec::new();
            for used in &def.uses {
                let fields: Vec<_> = match *used {
                    Ty::Struct(used) => {
                        let fields = self.structs[used.0 as usize].fields.iter();
                        fields.map(|field| field.name.clone()).collect()
                    }
                    _ => ARRAY_FIELDS.iter().map(|name| name.to_string()).collect(),
                };
                names.extend(fields);
            }
            let repeated = (0..names.len()).find(|i| names[..*i].contains(&names[*i]));
            if let Some(repeated) = repeated {
                let (bound, field) = (def.name.clone(), names.swap_remove(repeated));
                self.error(TypeErrorKind::BoundRepeats { bound, field }, span);
            }
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
    /// A struct bounds those that [start as](Self::starts_as) it does, and
    /// so does an array, which a struct starts as too. So a field of
    /// `bound` is where it would be in a `ty`, in memory and among its
    /// leaves. A [list](Self::list_of) bounds the structs that start as a
    /// struct whose first `use` lines name what it lists, in order.
    ///
    /// A union is bounded by one that starts as it does, and so is an
    /// enum: the variants or members of a `ty` are the first of `bound`.
    /// So every value of a `ty` is the same variant or member of `bound`.
    ///
    /// Nothing else relates the two: not what they hold, however alike.
    ///
    /// A type parameter is bounded by what its own bound is.
    pub(super) fn meets(&self, ty: Ty, bound: Ty) -> bool {
        self.starts_like(ty, bound, false)
    }

    /// Whether a `ty` [meets] `bound`. If `exact`, it is also typed just as
    /// `bound` is: no `varray` is where `bound` has an array that only
    /// reads. So a `ty` can be written as a `bound` is, through a pointer
    /// to one.
    ///
    /// [meets]: Self::meets
    pub(super) fn starts_like(&self, ty: Ty, bound: Ty, exact: bool) -> bool {
        let ty = self.known(ty);
        match self.is_sum(bound) {
            true => self.starts_as(bound, ty, exact),
            false => self.starts_as(ty, bound, exact),
        }
    }

    /// Whether a `ty` starts as `first` does: it is `first`, or its first
    /// `use` names a type that starts as `first` does. What it has of that
    /// type then comes before all else it has, as it is there. A `ty`
    /// starts as a list does if a type that it starts as uses what the list
    /// does, first and in order.
    ///
    /// An array is one that it [fits](Self::fits), unless `exact`. A `use`
    /// that failed to resolve names any type.
    fn starts_as(&self, ty: Ty, first: Ty, exact: bool) -> bool {
        let same = |have: Ty, want: Ty| {
            let arrays = matches!((have, want), (Ty::Array(_), Ty::Array(_)));
            let failed = have == Ty::Error || want == Ty::Error;
            have == want || failed || arrays && !exact && self.fits(have, want)
        };
        let listed = self.listed(first);
        self.starts(ty).any(|ty| {
            let used = self.used_by(ty);
            let lists = listed.is_some_and(|listed| {
                let mut pairs = used.iter().zip(listed);
                used.len() >= listed.len() && pairs.all(|(used, listed)| same(*used, *listed))
            });
            same(ty, first) || lists
        })
    }

    /// Whether a `ty` holds what one that [meets] `bound` does: the fields
    /// that a struct or a list starts with, named and typed as they are
    /// there, the `ptr` and `len` of an array that it [fits], or the first
    /// variants of a union. So a `use` would make it one that does, if it
    /// isn't. An enum is never said to: the values of its members aren't
    /// known where its bound is first asked.
    ///
    /// [fits]: Self::fits
    ///
    /// [meets]: Self::meets
    fn resembles(&self, ty: Ty, bound: Ty) -> bool {
        let (ty, first) = match self.is_sum(bound) {
            true => (bound, self.known(ty)),
            false => (self.known(ty), bound),
        };
        match (ty, first) {
            (Ty::Struct(have), Ty::Struct(want)) => {
                let (have, want) = (
                    &self.structs[have.0 as usize],
                    &self.structs[want.0 as usize],
                );
                have.union == want.union && fields_start_as(&have.fields, &want.fields)
            }
            (Ty::Struct(have), Ty::Array(_)) if !self.is_sum(ty) => {
                let fields = &self.structs[have.0 as usize].fields;
                let names = fields.iter().map(|field| field.name.as_str());
                let mut tys = fields.iter().map(|field| field.ty).zip(self.members(first));
                names.take(2).eq(ARRAY_FIELDS) && tys.all(|(ty, of)| self.fits(ty, of))
            }
            _ => false,
        }
    }

    /// Whether `ty` is a union or an enum.
    pub(super) fn is_sum(&self, ty: Ty) -> bool {
        matches!(ty, Ty::Enum(_)) || self.union_id(ty).is_some()
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
            if !self.meets(*arg, bound) {
                self.bound_error(*arg, bound, site);
                met = false;
            }
        }
        met
    }

    /// Reports, at `site`, that a `ty` isn't a type that `bound` bounds.
    fn bound_error(&mut self, ty: Ty, bound: Ty, site: Span) {
        let kind = self.not_used(ty, bound).unwrap_or_else(|| {
            let sum = self.is_sum(bound);
            let (ty, bound) = (self.ty_name(ty), self.ty_name(bound));
            match sum {
                true => TypeErrorKind::NotWithin { ty, bound },
                false => TypeErrorKind::BoundNotMet { ty, bound },
            }
        });
        self.error(kind, site);
    }

    /// The error for a `ty` that isn't a type that `bound` bounds, if it
    /// [resembles](Self::resembles) one: it only lacks a `use`.
    pub(super) fn not_used(&self, ty: Ty, bound: Ty) -> Option<TypeErrorKind> {
        if self.meets(ty, bound) || !self.resembles(ty, bound) {
            return None;
        }
        // A union uses what it bounds.
        let (by, used, what) = match self.is_sum(bound) {
            true => (bound, ty, "variants"),
            false => (ty, bound, "fields"),
        };
        let (ty, used) = (self.ty_name(by), self.ty_name(used));
        Some(TypeErrorKind::NotUsed { ty, used, what })
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
            ExprKind::Todo => TypeKind::Todo,
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
            _ if name == TUPLE => Some(Arity::Any),
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
                    uses: Vec::new(),
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

    /// Gives instance `id` the fields of its generic declaration and the
    /// types that it uses, with type arguments in place of type parameters,
    /// unless it has them. A [list](Self::list_of) uses its type arguments,
    /// and is given their fields. Does nothing for a struct that is no
    /// instance.
    pub(super) fn fill_instance(&mut self, id: StructId) {
        let index = id.0 as usize;
        let Some(instance) = &mut self.structs[index].instance else {
            return;
        };
        if mem::replace(&mut instance.filled, true) {
            return;
        }
        let (generic, args, site) = (instance.generic, instance.args.clone(), instance.site);
        if Some(generic) == self.list {
            self.structs[index].fields = self.listed_fields(&args, site);
            self.structs[index].uses = args;
            return;
        }
        // Until it has its fields, it counts for nothing in what holds it.
        self.structs[index].depth = Some(0);
        let mut uses = self.structs[generic.0 as usize].uses.clone();
        for used in &mut uses {
            *used = self.substitute(*used, &args, site);
        }
        self.structs[index].uses = uses;
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

    /// The fields of a list of `uses` written at `site`: those of each
    /// struct and the `ptr` and `len` of each array, in order, as a struct
    /// that uses them has them. One named as another before it is left
    /// out, which [`Self::check_lists`] reports.
    fn listed_fields(&mut self, uses: &[Ty], site: Span) -> Vec<FieldDef> {
        let mut fields: Vec<FieldDef> = Vec::new();
        for used in uses {
            let held = match *used {
                Ty::Struct(used) => {
                    self.fill_instance(used);
                    let mut held = self.structs[used.0 as usize].fields.clone();
                    for (index, field) in held.iter_mut().enumerate() {
                        field.default = None;
                        field.default_ty = None;
                        field.used = Some((used, index));
                        field.span = site;
                    }
                    held
                }
                _ => self.array_fields(*used, site),
            };
            for field in held {
                if !fields.iter().any(|f| f.name == field.name) {
                    fields.push(field);
                }
            }
        }
        fields
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
/// those that `first` has, which are some, are named and typed as its are,
/// in order. Of variants, they also hold a value or none as those of
/// `first` do.
fn fields_start_as(fields: &[FieldDef], first: &[FieldDef]) -> bool {
    let mut pairs = fields.iter().zip(first);
    fields.len() >= first.len()
        && !first.is_empty()
        && pairs.all(|(field, first)| {
            field.name == first.name && field.bare == first.bare && field.ty == first.ty
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

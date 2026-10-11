//! Results that hide their type. `opaque(Bound)` in the result of a
//! function stands for one type that the function's body gives it, which
//! the `return`s settle: each as an argument would settle a type parameter
//! that `Bound` bounds. It is a type of its own, which only that function
//! gives a value of, so a function returns a closure by it, whose type
//! nothing writes.
//!
//! Outside the body, all that is known of the type is its bound: a value of
//! it is used as a value of a type parameter so bounded is. It is laid out
//! as the type it hides, which is found by lowering the body, where a call
//! first asks for it.

use crate::file::FileId;
use crate::ir::FuncId;
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, TypeArg};

use super::generic::ParamDef;
use super::{
    Body, Checker, GenericFnId, Item, OPAQUE, OPEN_FUNCS, OpaqueId, ParamId, Ty, TypeErrorKind,
    Value, Visit,
};

/// The result of a function, while it is resolved: where `opaque` is
/// written.
pub(super) struct Hiding {
    pub(super) owner: Owner,
    /// The name of the function, as an error says it.
    pub(super) func: String,
    pub(super) is_pub: bool,
    /// How many opaque types the result has so far.
    pub(super) count: usize,
}

/// A type that the result of a function hides.
pub(super) struct OpaqueDef {
    owner: Owner,
    /// The name of the function whose result hides it.
    func: String,
    /// What bounds the type it hides, if anything does.
    pub(super) bound: Option<Ty>,
    /// The type parameter that stands for it in the result of its function
    /// until a `return` settles it: what a `return` gives in its place.
    hole: Ty,
    /// The type it hides, once a `return` of its function settles it.
    hidden: Option<Ty>,
    /// How far the body of its function is lowered, which settles it.
    state: Visit,
    /// Whether an error says why nothing settles it.
    reported: bool,
    /// Whether its function is `pub`, and the module that declares it.
    is_pub: bool,
    module: FileId,
    /// For that of an instance of a generic function, the one that the
    /// declaration's result has in its place.
    decl: Option<OpaqueId>,
}

/// The function whose result hides a type.
#[derive(Clone, PartialEq)]
pub(super) enum Owner {
    Func(FuncId),
    /// A generic function, as declared.
    Generic(GenericFnId),
    /// The instance of a generic function with these type arguments.
    Instance(GenericFnId, Vec<Ty>),
}

impl Checker {
    /// Resolves `opaque(args)`, written at `span`: a type that the result
    /// it is written in hides, bounded as a type parameter is by `args`.
    /// The error type after reporting one written anywhere else.
    pub(super) fn resolve_opaque(&mut self, args: &Option<Vec<TypeArg>>, span: Span) -> Ty {
        // What bounds it hides nothing of its own.
        let site = self.opaque_site.take();
        let args = args.iter().flatten();
        let mut written = Vec::new();
        for arg in args {
            if let Some(label) = &arg.label {
                self.error(TypeErrorKind::LabelledTypeArg, label.span);
            }
            written.push(arg.ty.clone());
        }
        let bound = match written.is_empty() {
            true => Some(None),
            false => self.bound_of(&written, span).map(Some),
        };
        let Some(mut site) = site else {
            self.error(TypeErrorKind::OpaqueOutsideResult, span);
            return Ty::Error;
        };
        let index = site.count;
        site.count += 1;
        let (owner, func, is_pub) = (site.owner.clone(), site.func.clone(), site.is_pub);
        self.opaque_site = Some(site);
        let Some(bound) = bound.filter(|bound| *bound != Some(Ty::Error)) else {
            return Ty::Error;
        };
        let hole = self.new_hole(bound, self.type_params.len() + index);
        self.opaques.push(OpaqueDef {
            owner,
            func,
            bound,
            hole,
            hidden: None,
            state: Visit::New,
            reported: false,
            is_pub,
            module: self.module,
            decl: None,
        });
        Ty::Opaque(OpaqueId(self.opaques.len() as u32 - 1))
    }

    /// A type parameter bounded by `bound`, to stand for an opaque type
    /// that nothing has settled. It is the `index`th of those in scope.
    fn new_hole(&mut self, bound: Option<Ty>, index: usize) -> Ty {
        self.params.push(ParamDef {
            name: self.opaque_text(bound),
            index,
            bound,
            hole: true,
        });
        Ty::Param(ParamId(self.params.len() as u32 - 1))
    }

    /// Whether `ty` holds a type that a result hides and no `return` has
    /// settled, so that nothing is known to be of it.
    pub(super) fn has_hole(&self, ty: Ty) -> bool {
        match ty {
            Ty::Param(id) => self.params[id.0 as usize].hole,
            _ => self
                .written_parts(ty)
                .into_iter()
                .any(|part| self.has_hole(part)),
        }
    }

    /// `opaque(Bound)`, as one that `bound` bounds is written.
    fn opaque_text(&self, bound: Option<Ty>) -> String {
        let bounds = match bound {
            None => String::new(),
            Some(bound) => match self.listed(bound) {
                Some(listed) => {
                    let listed: Vec<_> = listed.iter().map(|ty| self.ty_name(*ty)).collect();
                    listed.join(", ")
                }
                None => self.ty_name(bound),
            },
        };
        format!("{OPAQUE}({bounds})")
    }

    /// The name of opaque type `id`: as it is written, and the function
    /// whose result hides it, as no other is it.
    pub(super) fn opaque_name(&self, id: OpaqueId) -> String {
        let def = &self.opaques[id.0 as usize];
        format!("{} of {}", self.opaque_text(def.bound), def.func)
    }

    /// What bounds the type that opaque type `id` hides, if anything.
    pub(super) fn opaque_bound(&self, id: OpaqueId) -> Option<Ty> {
        self.opaques[id.0 as usize].bound
    }

    /// The type that a `ty` is, if it is an opaque one that has been
    /// settled: what it hides, and what that hides. Any other is itself.
    pub(super) fn hiding(&self, ty: Ty) -> Ty {
        match ty {
            Ty::Opaque(id) => match self.opaques[id.0 as usize].hidden {
                Some(hidden) => self.hiding(hidden),
                None => ty,
            },
            _ => ty,
        }
    }

    /// Whether opaque type `id` is of a generic function as declared, or
    /// of an instance whose type arguments hold type parameters: one that
    /// no function gives a value of.
    pub(super) fn is_open_opaque(&self, id: OpaqueId) -> bool {
        match &self.opaques[id.0 as usize].owner {
            Owner::Func(id) => id.0 >= OPEN_FUNCS,
            Owner::Generic(_) => true,
            Owner::Instance(_, args) => args.iter().any(|arg| self.has_param(*arg)),
        }
    }

    /// The opaque type in `ty` that the module `within` can't name, or that
    /// isn't `pub`: one of a function that isn't, or one that a type which
    /// isn't bounds.
    pub(super) fn private_opaque(&self, id: OpaqueId, within: Option<FileId>) -> Option<Ty> {
        let def = &self.opaques[id.0 as usize];
        if !def.is_pub && within != Some(def.module) {
            return Some(Ty::Opaque(id));
        }
        let bound = def.bound?;
        match self.listed(bound) {
            Some(listed) => listed.iter().find_map(|ty| self.private_part(*ty, within)),
            None => self.private_part(bound, within),
        }
    }

    /// The opaque types written in `ty`.
    pub(super) fn opaques_in(&self, ty: Ty) -> Vec<OpaqueId> {
        fn push(ck: &Checker, ty: Ty, out: &mut Vec<OpaqueId>) {
            match ty {
                Ty::Opaque(id) if !out.contains(&id) => out.push(id),
                Ty::Opaque(_) => {}
                _ => {
                    for part in ck.written_parts(ty) {
                        push(ck, part, out);
                    }
                }
            }
        }
        let mut out = Vec::new();
        push(self, ty, &mut out);
        out
    }

    /// The opaque types that `ret` holds which are function `func`'s own
    /// to settle, as `ret` is its result: those written there, and not
    /// those of a type argument. A generic function checked as declared is
    /// no function.
    pub(super) fn own_opaques(&self, func: Option<FuncId>, ret: Ty) -> Vec<OpaqueId> {
        let owns = |id: &OpaqueId| match &self.opaques[id.0 as usize].owner {
            Owner::Func(owner) => Some(*owner) == func,
            Owner::Generic(_) => func.is_none(),
            Owner::Instance(generic, args) => {
                let instance = self.fn_instances.get(&(*generic, args.clone()));
                func.is_some() && instance == func.as_ref()
            }
        };
        self.opaques_in(ret).into_iter().filter(owns).collect()
    }

    /// The opaque type that an instance of a generic function has where
    /// its declaration's result has opaque type `id`: its own, bounded as
    /// `id` is with `args` in place of the type parameters, which are those
    /// of the function. Any other opaque type is itself.
    pub(super) fn opaque_instance(&mut self, id: OpaqueId, args: &[Ty], site: Span) -> Ty {
        let def = &self.opaques[id.0 as usize];
        let (decl, generic, args) = match (&def.owner, def.decl) {
            (Owner::Generic(generic), _) => (id, *generic, args.to_vec()),
            // One of an instance that names type parameters, which are
            // those `args` are for.
            (Owner::Instance(generic, inner), Some(decl)) if self.is_open_opaque(id) => {
                let (generic, inner) = (*generic, inner.clone());
                let inner = inner.into_iter();
                let inner = inner.map(|arg| self.substitute(arg, args, site));
                (decl, generic, inner.collect())
            }
            _ => return Ty::Opaque(id),
        };
        if let Some(instance) = self.opaque_instances.get(&(decl, args.clone())) {
            return Ty::Opaque(*instance);
        }
        let def = &self.opaques[decl.0 as usize];
        let (bound, is_pub, module) = (def.bound, def.is_pub, def.module);
        let Ty::Param(hole) = def.hole else {
            unreachable!("a hole is a type parameter")
        };
        let index = self.params[hole.0 as usize].index;
        let bound = bound.map(|bound| self.substitute(bound, &args, site));
        let hole = self.new_hole(bound, index);
        let instance = OpaqueId(self.opaques.len() as u32);
        let names: Vec<_> = args.iter().map(|arg| self.ty_name(*arg)).collect();
        let func = format!("{}({})", self.generic_fn_name(generic), names.join(", "));
        self.opaques.push(OpaqueDef {
            owner: Owner::Instance(generic, args.clone()),
            func,
            bound,
            hole,
            hidden: None,
            state: Visit::New,
            reported: false,
            is_pub,
            module,
            decl: Some(decl),
        });
        self.opaque_instances.insert((decl, args), instance);
        Ty::Opaque(instance)
    }

    /// `ty` with each of the opaque types `own` replaced: by what it hides,
    /// if that is settled, and otherwise by the type parameter that stands
    /// for it until it is. So it is `ty` as the body of the function whose
    /// result it is sees it.
    pub(super) fn revealed(&mut self, ty: Ty, own: &[OpaqueId], site: Span) -> Ty {
        match ty {
            Ty::Opaque(id) if own.contains(&id) => {
                let def = &self.opaques[id.0 as usize];
                def.hidden.unwrap_or(def.hole)
            }
            Ty::Struct(id) => {
                let Some(instance) = &self.structs[id.0 as usize].instance else {
                    return ty;
                };
                let (generic, args) = (instance.generic, instance.args.clone());
                let seen: Vec<_> = args
                    .iter()
                    .map(|arg| self.revealed(*arg, own, site))
                    .collect();
                match seen == args {
                    true => ty,
                    false => self.instantiate(generic, seen, site),
                }
            }
            _ => {
                let components = self.components(ty);
                let seen: Vec<_> = components
                    .iter()
                    .map(|component| self.revealed(*component, own, site))
                    .collect();
                match seen == components {
                    true => ty,
                    false => self.rebuild(ty, seen),
                }
            }
        }
    }

    /// Settles opaque type `id` as one that hides a `hidden`, which a
    /// `return` at `span` gives in its place, unless that is no type it
    /// hides: one that memory can't hold, or that its bound doesn't bound.
    fn hide(&mut self, id: OpaqueId, hidden: Ty, span: Span) {
        let bound = self.opaques[id.0 as usize].bound;
        let storable = self.storable(hidden);
        if !storable {
            self.error(TypeErrorKind::NotStorable(self.ty_name(hidden)), span);
        }
        let met = bound.is_none_or(|bound| self.check_bound(hidden, bound, span));
        // One that would hide itself is reported where it is called for.
        let cyclic = self.hides(hidden, id);
        let def = &mut self.opaques[id.0 as usize];
        match storable && met && !cyclic && hidden != Ty::Error {
            true => def.hidden = Some(hidden),
            false => def.reported = true,
        }
    }

    /// Whether `ty` holds opaque type `id`, or one that hides a type which
    /// does.
    fn hides(&self, ty: Ty, id: OpaqueId) -> bool {
        self.opaques_in(ty).into_iter().any(|held| {
            let hidden = self.opaques[held.0 as usize].hidden;
            held == id || hidden.is_some_and(|hidden| self.hides(hidden, id))
        })
    }

    /// Finds what each opaque type in `ty` hides, which a call at `span`
    /// gives a value of: the function whose result hides it is lowered
    /// now, unless it has been. A generic function checked as declared
    /// calls nothing, so it needs none.
    pub(super) fn settle(&mut self, program: &Program, ty: Ty, span: Span) {
        for id in self.opaques_in(ty) {
            let def = &self.opaques[id.0 as usize];
            if def.hidden.is_some() {
                continue;
            }
            // Of a generic function checked as declared, the one that the
            // declaration has, which is what its body settles.
            let (asked, func) = match (&def.owner, def.decl) {
                (Owner::Instance(..), Some(decl)) if self.open => (decl, None),
                (Owner::Func(func), _) if func.0 < OPEN_FUNCS && !self.open => (id, Some(*func)),
                (Owner::Instance(generic, args), _) if !self.open => {
                    let instance = self.fn_instances.get(&(*generic, args.clone()));
                    (id, instance.copied())
                }
                _ => continue,
            };
            let def = &self.opaques[asked.0 as usize];
            match (def.state, func) {
                // Its body is what asks: it gives itself what it gives.
                (Visit::Active, _) => {
                    if !def.reported && def.hidden.is_none() {
                        self.error(TypeErrorKind::OpaqueCycle(def.func.clone()), span);
                    }
                    self.opaques[asked.0 as usize].reported = true;
                }
                (Visit::New, Some(func)) => {
                    self.lower_early(program, func);
                    // One that failed to check is never lowered.
                    self.opaques[id.0 as usize].state = Visit::Done;
                }
                _ => {}
            }
        }
    }

    /// Says that the body of the function that hides each of `own` is
    /// being lowered, which is to settle them.
    pub(super) fn open_opaques(&mut self, own: &[OpaqueId]) {
        for id in own {
            self.opaques[id.0 as usize].state = Visit::Active;
        }
    }

    /// Says that the body of function `func`, declared at `span`, is
    /// lowered, which hides each of `own`, and reports each that no
    /// `return` of it settled, unless the body has an error to mend first,
    /// as `failed` says.
    pub(super) fn close_opaques(&mut self, own: &[OpaqueId], func: &str, failed: bool, span: Span) {
        for id in own {
            let def = &mut self.opaques[id.0 as usize];
            def.state = Visit::Done;
            if def.hidden.is_some() || def.reported || failed {
                continue;
            }
            def.reported = true;
            let kind = TypeErrorKind::NoOpaqueType {
                func: func.to_string(),
                opaque: self.opaque_text(self.opaques[id.0 as usize].bound),
            };
            self.error(kind, span);
        }
    }
}

impl Body<'_> {
    /// Finds what each opaque type in `ty` hides, the type of what a call
    /// at `span` gives.
    pub(super) fn settle(&mut self, ty: Ty, span: Span) {
        if let Some(program) = self.global.or(self.program) {
            self.ck.settle(program, ty, span);
        }
    }

    /// The value of `return value`, checked against the result of the
    /// function. Where that hides a type that no `return` has settled yet,
    /// this one settles it, as an argument settles a type parameter: it is
    /// whatever the value has in its place.
    pub(super) fn returned(&mut self, value: &parse::Expr) -> Value {
        let span = value.span;
        let own = self.opaques.clone();
        if own.is_empty() {
            return self.check(value, self.ret);
        }
        let want = self.ck.revealed(self.ret, &own, span);
        let hole = |ck: &Checker, id: &OpaqueId| {
            let def = &ck.opaques[id.0 as usize];
            def.hidden.is_none().then_some(def.hole)
        };
        let holes = own.iter().filter_map(|id| Some((*id, hole(self.ck, id)?)));
        let holes: Vec<_> = holes.collect();
        // A generic function is the instance that the bound calls.
        let called = match want {
            Ty::Param(id) if !holes.is_empty() => self.ck.params[id.0 as usize].bound,
            _ => None,
        };
        let called = called.and_then(|bound| self.ck.called_as(bound));
        let (ty, mut lowered) = match (self.named(value), called) {
            (Some(Item::GenericFn(generic)), Some((takes, gives))) => {
                let called = self.generic_fn_called(generic, Some((takes, Some(gives))), span);
                self.ck.record(span, called.0);
                called
            }
            _ => self.expr(value, Some(want)),
        };
        // A `never` says nothing of what would be there, and what failed
        // to check is already reported.
        if matches!(ty, Ty::Never | Ty::Error) {
            lowered.scalars = self.blank(want).scalars;
            return lowered;
        }
        let index = |ck: &Checker, hole: Ty| match hole {
            Ty::Param(hole) => ck.params[hole.0 as usize].index,
            _ => unreachable!("a hole is a type parameter"),
        };
        // The type parameters of the function stand for themselves.
        let own_params = self.ck.type_params.iter().map(|(_, ty)| Some(*ty));
        let mut bound: Vec<_> = own_params.collect();
        let width = holes.iter().map(|(_, hole)| index(self.ck, *hole) + 1);
        bound.resize(bound.len().max(width.max().unwrap_or(0)), None);
        self.ck.unify(want, ty, &mut bound);
        let mut settled = true;
        for (id, hole) in &holes {
            // What still has one of them in it says nothing of it.
            let given = bound[index(self.ck, *hole)];
            let given = given.filter(|ty| !self.ck.has_hole(*ty));
            match given {
                Some(hidden) => self.ck.hide(*id, hidden, span),
                None => {
                    let opaque = self.ck.opaque_text(self.ck.opaques[id.0 as usize].bound);
                    self.error(TypeErrorKind::ReturnBeforeOpaque(opaque), span);
                    self.ck.opaques[id.0 as usize].reported = true;
                }
            }
            settled &= self.ck.opaques[id.0 as usize].hidden.is_some();
        }
        // What isn't settled is reported, and nothing is of it. What the
        // function gives itself is what its result hides.
        if settled {
            let want = self.ck.revealed(self.ret, &own, span);
            let found = self.ck.revealed(ty, &own, span);
            self.expect(found, want, span);
        }
        lowered
    }

    /// The value that an opaque type's bound takes apart, which a `value`
    /// of type `ty` is as: that of the union that bounds what `ty` hides,
    /// which is wider than it. Any other is itself.
    pub(super) fn as_opaque_bound(&mut self, ty: Ty, value: Value) -> Value {
        let (Ty::Opaque(id), hidden) = (ty, self.ck.hiding(ty)) else {
            return value;
        };
        let Some(bound) = self.ck.opaque_bound(id) else {
            return value;
        };
        match self.ck.union_id(bound).is_some() && hidden != ty {
            true => match self.ck.cast_value(hidden, bound, value) {
                Some((_, value)) => value,
                None => Value::default(),
            },
            false => value,
        }
    }
}

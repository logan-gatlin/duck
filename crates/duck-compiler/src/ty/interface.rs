//! The interface of a package: what a program that uses the package is
//! checked against, with nothing of the package's source but what it
//! declares.
//!
//! A package is compiled once, whole, and what it compiles to is kept: its
//! [`Artifact`], which linking makes a part of the module of every program
//! that uses it, and the interface the artifact holds. The interface has the
//! package's items as they were parsed, but for the bodies of the functions
//! that aren't generic, which only the artifact has anything of, and its
//! `use`s. A program that uses the package declares and defines those items
//! as it does its own, with the same passes, so that the types of the
//! package are those of the program and nothing of the checker is written
//! as bytes. What the package's constants are, which is found by folding
//! and running what those bodies hold, the interface keeps as results, each
//! numbered as the artifact numbers what it holds: the globals, the values
//! of the members of each enum, the defaults of fields and parameters, the
//! types that the results of its functions hide, and the signatures of the
//! functions the checker made for it. A type is written in terms of what
//! declares it, as the ids of one check are not those of another.
//!
//! In the package's turn, the checker takes those results in place of
//! folding and lowering anything, and numbers a placeholder for each of what
//! the artifact places, runs, defines and takes pointers to, so that what
//! the program lowers names them as the artifact's: linking then puts the
//! artifact in their place.

use crate::codec::{Decode, DecodeError, Encode, Reader, Writer, bad, lists};
use crate::file::FileId;
use crate::ir::{self, Const, DataId, FuncId, GlobalId, Symbol, ValueId};
use crate::lex::Span;
use crate::load::{Compiled, Program, Use};
use crate::parse::{Item, ItemKind};
use crate::visit::{self, Node};

use super::artifact::{Extract, Foreign, Kind, RETURN_AREA};
use super::defaults::DefaultValue;
use super::evaluate::Dep;
use super::link::{DataDef, Finding, Placing, ValueDef};
use super::nested::NestedFn;
use super::opaque::{OpaqueDef, Owner};
use super::{
    Checker, EnumId, FuncSig, GenericFnId, GlobalDef, Prim, Scalar, Slots, StructId, Synth, Ty,
    Visit, zero,
};

lists!(
    Vec<String>,
    GlobalId,
    Written,
    SynthRecord,
    GlobalRecord,
    (usize, Vec<GlobalRecord>),
    Member,
    (usize, Vec<Member>),
    (usize, DefaultRecord),
    (usize, Vec<(usize, DefaultRecord)>),
    Option<DefaultRecord>,
    (FuncId, Vec<Option<DefaultRecord>>),
    Option<Written>,
    (String, Written),
    GenericDefaults,
    OpaqueRecord,
    (FuncId, Vec<OpaqueRecord>),
    (FileId, String, Vec<u8>),
    DepRecord,
    (usize, Vec<DepRecord>),
    (FuncId, Vec<DepRecord>),
);

/// What a program that uses a package is checked against: see the module.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct Interface {
    /// The path a `use` leads to each file of the package by from its root,
    /// the root's first, which is empty.
    pub(crate) modules: Vec<Vec<String>>,
    /// The packages it uses, by the names it uses them as.
    pub(crate) depends: Vec<String>,
    /// Its items, uses and what the bodies that are kept include, written
    /// with each file as its index in `modules`, and a package it uses as
    /// `modules.len()` and its index in `depends`.
    declared: Vec<u8>,
    pub(super) results: Results,
}

/// What is read of an interface's declarations, for the files a program
/// gives them.
pub struct Declared {
    pub items: Vec<Item>,
    pub uses: Vec<Use>,
    /// What each `module.include` of a body that is kept includes: by the
    /// file and the path it is written in.
    pub includes: Vec<(FileId, String, Vec<u8>)>,
}

/// What checking a package found that a program that uses it can't find
/// again without the bodies the interface leaves out, numbered as the
/// package's artifact numbers what it holds. An item is by its place among
/// the package's.
#[derive(Debug, Clone, Default, PartialEq)]
pub(super) struct Results {
    /// Each function the checker made for the package, in the order of the
    /// artifact's.
    synths: Vec<SynthRecord>,
    /// The globals of each binding, in the order they are bound.
    bindings: Vec<(usize, Vec<GlobalRecord>)>,
    /// The value of each member of each enum, and whether it is known.
    members: Vec<(usize, Vec<Member>)>,
    /// The default of each field of each struct that has one.
    fields: Vec<(usize, Vec<(usize, DefaultRecord)>)>,
    /// The default of each parameter of each function that has one, by the
    /// function.
    param_defaults: Vec<(FuncId, Vec<Option<DefaultRecord>>)>,
    /// The default of each parameter of each generic function that has one,
    /// folded, and the type of each that has one of its own.
    generic_defaults: Vec<GenericDefaults>,
    /// The types that the result of each function hides, by the function,
    /// in the order of the result, each with what bounds it.
    opaques: Vec<(FuncId, Vec<OpaqueRecord>)>,
    /// What the constants of each item name, and what the body of each
    /// function names: the functions whose pointers they take and the
    /// items whose constants they read, which code run for a constant that
    /// reads them may call.
    item_deps: Vec<(usize, Vec<DepRecord>)>,
    func_deps: Vec<(FuncId, Vec<DepRecord>)>,
}

/// A type that the result of a function hides, and what bounds it.
#[derive(Debug, Clone, PartialEq)]
struct OpaqueRecord {
    hidden: Written,
    bound: Option<Written>,
}

/// A type that a result hides, and what bounds it, as the checker has them.
type Hidden = (Ty, Option<Ty>);

/// What a constant or a body names: see [`Dep`].
#[derive(Debug, Clone, PartialEq)]
enum DepRecord {
    Func(FuncId),
    Item(usize),
}

/// The value of a member of an enum, and whether it is known.
type Member = (Vec<Scalar>, bool);

/// The defaults of a generic function, by its item: each parameter's,
/// folded, and the type of each that has one of its own.
type GenericDefaults = (usize, Vec<Option<DefaultRecord>>, Vec<Option<Written>>);

/// A function the checker made for a package, as its artifact has it.
#[derive(Debug, Clone, PartialEq)]
struct SynthRecord {
    name: String,
    params: Vec<Written>,
    ret: Written,
    /// What values of its type hold, for one declared in a function, and
    /// what it captures, each by name and type.
    held: Option<(Written, Vec<(String, Written)>)>,
    /// What it was made for, which a program that uses the package has it
    /// for rather than making one of its own.
    kind: SynthKind,
}

/// Why the checker made a function: see [`Synth`].
#[derive(Debug, Clone, PartialEq)]
enum SynthKind {
    /// The instance of the generic function that an item declares, with
    /// these type arguments.
    Instance(usize, Vec<Written>),
    /// Compares two arrays of this type.
    Eq(Written),
    /// Calls this imported function.
    Wrapper(FuncId),
    /// One that nothing else is given for.
    Other,
}

/// A global of a package, as checking found it.
#[derive(Debug, Clone, PartialEq)]
struct GlobalRecord {
    ty: Written,
    mutable: bool,
    slots: SlotRecord,
    known: bool,
}

/// Where a global is: see [`Slots`].
#[derive(Debug, Clone, PartialEq)]
enum SlotRecord {
    Global(Vec<GlobalId>),
    Const(Vec<Scalar>),
}

/// The default of a field or a parameter, as checking left it.
#[derive(Debug, Clone, PartialEq)]
enum DefaultRecord {
    Folded(Vec<Scalar>),
    Failed,
    Pending,
}

/// A type as an interface writes it: in terms of what declares it, which
/// a program that reads it has declared too, rather than of the ids of the
/// check that found it.
#[derive(Debug, Clone, PartialEq)]
enum Written {
    Prim(Prim),
    Unit,
    Never,
    Error,
    Type,
    /// A struct or a union, by the item that declares it.
    Struct(usize),
    Enum(usize),
    /// An instance of a generic struct or union with these type arguments.
    Instance(Base, Vec<Written>),
    /// A built-in union, by its place among them, or the built-in list.
    Builtin(u8),
    Ptr(Box<Written>, bool),
    Tuple(Vec<Written>),
    Array(Box<Written>, bool),
    Fn(Vec<Written>, Box<Written>),
    /// The type of a function, by the artifact's number for it.
    Func(FuncId),
    /// The type that the result of a function hides, by the function and
    /// its place in the result.
    Opaque(FuncId, usize),
    /// A type parameter, by the item that declares it and its place there.
    Param(usize, usize),
}

/// A generic declaration that an instance is of: an item's, a built-in
/// union by its place among them, or the built-in list.
#[derive(Debug, Clone, PartialEq)]
enum Base {
    Decl(usize),
    Builtin(u8),
    List,
}

/// What a package that is compiled already was given in the checker in
/// place of lowering it, which what names it is resolved by.
pub(super) struct Imported {
    /// Its imported functions, its defined functions and the functions the
    /// checker made for it, each in the artifact's order.
    imports: Vec<FuncId>,
    defined: Vec<FuncId>,
    synths: Vec<FuncId>,
    /// Where its globals, its data and its values start.
    globals: usize,
    data: usize,
    values: usize,
}

/// The built-in list, as [`Written::Builtin`] writes it.
const LIST: u8 = u8::MAX;

/// The version of the format of an interface, which changes whenever it
/// does, and which its bytes start with.
const VERSION: u32 = 1;

impl Interface {
    /// Its declarations, with each file as the id the program gives it:
    /// `files` are the ids of its files, in the order of its modules, and
    /// `libraries` those of the libraries of the packages it depends on, in
    /// the order of those.
    pub fn declared(
        &self,
        files: &[FileId],
        libraries: &[FileId],
    ) -> Result<Declared, DecodeError> {
        if files.len() != self.modules.len() || libraries.len() != self.depends.len() {
            return Err(DecodeError(
                "the files aren't those of the package".to_string(),
            ));
        }
        let mut r = Reader::mapped(&self.declared, files).with_libraries(libraries);
        let version = u32::decode(&mut r)?;
        if version != VERSION {
            let why = format!("the interface is of version {version}, and this is {VERSION}");
            return Err(DecodeError(why));
        }
        let items = Decode::decode(&mut r)?;
        let uses = (0..usize::decode(&mut r)?).map(|_| read_use(&mut r));
        let declared = Declared {
            items,
            uses: uses.collect::<Result<_, _>>()?,
            includes: Decode::decode(&mut r)?,
        };
        match r.done() {
            true => Ok(declared),
            false => Err(DecodeError(
                "the interface has bytes after its end".to_string(),
            )),
        }
    }
}

impl Checker {
    /// The interface of package `package` of `program`, whose artifact
    /// `extract` is making: what it names of other packages, it names as
    /// the artifact does.
    pub(super) fn interface(
        &self,
        program: &Program,
        package: usize,
        extract: &mut Extract,
    ) -> Interface {
        let own = &program.packages[package];
        let share = extract.share(package).clone();
        let is_own = |file: &FileId| own.files.contains(file);
        let depends: Vec<_> = program
            .depends
            .iter()
            .filter(|d| d.from == own.root)
            .collect();
        // Nothing of what is written is of another package's file, so what
        // the writer comes to is in its order.
        let mut w = Writer::mapped(own.files.clone());
        VERSION.encode(&mut w);
        let items: Vec<Item> = program.items[share.items.clone()]
            .iter()
            .map(stripped)
            .collect();
        items.encode(&mut w);
        let uses: Vec<_> = program.uses.iter().filter(|u| is_own(&u.module)).collect();
        uses.len().encode(&mut w);
        for used in uses {
            used.module.encode(&mut w);
            used.name.encode(&mut w);
            match depends.iter().position(|d| d.library == used.target) {
                Some(depend) if !is_own(&used.target) => {
                    w.tag(1);
                    depend.encode(&mut w);
                }
                _ => {
                    w.tag(0);
                    used.target.encode(&mut w);
                }
            }
            used.target_path.encode(&mut w);
            used.path.encode(&mut w);
            used.members.encode(&mut w);
            used.is_pub.encode(&mut w);
            used.decl.encode(&mut w);
        }
        let mut includes: Vec<(FileId, String, Vec<u8>)> = Vec::new();
        for item in &items {
            visit::each(item, &mut |node| {
                if let Node::Expr(expr) = node
                    && let Some(path) = expr.included()
                    && let Some(Ok(bytes)) =
                        program.includes.get(&(item.span.file, path.to_string()))
                    && !includes
                        .iter()
                        .any(|(f, p, _)| *f == item.span.file && p == path)
                {
                    includes.push((item.span.file, path.to_string(), bytes.to_vec()));
                }
            });
        }
        includes.encode(&mut w);
        let mut modules: Vec<Vec<String>> = own.modules.clone();
        modules.extend(w.files[own.files.len()..].iter().map(|_| Vec::new()));
        Interface {
            modules,
            depends: depends.iter().map(|d| d.name.clone()).collect(),
            declared: w.bytes,
            results: self.results(program, package, extract),
        }
    }

    /// What checking package `package` found: see [`Results`].
    fn results(&self, program: &Program, package: usize, extract: &mut Extract) -> Results {
        let share = extract.share(package).clone();
        let items = share.items.clone();
        let synths_start = self.funcs.len() - self.synths.len();
        let scalars = |extract: &mut Extract, scalars: &[Scalar]| -> Vec<Scalar> {
            scalars.iter().map(|s| extract.scalar(*s)).collect()
        };
        let default = |extract: &mut Extract, default: &DefaultValue| match default {
            DefaultValue::Folded(values) => DefaultRecord::Folded(scalars(extract, values)),
            DefaultValue::Failed => DefaultRecord::Failed,
            DefaultValue::Pending => DefaultRecord::Pending,
        };
        let mut results = Results::default();
        for index in items.clone() {
            let local = index - items.start;
            match &program.items[index].kind {
                ItemKind::Binding(decl) if !decl.binds_type() => {
                    let first = self.constants[index].id;
                    let count = super::pattern_names(&decl.pattern).len();
                    let mut globals = Vec::new();
                    for global in self.globals[first..first + count].iter().flatten() {
                        globals.push(GlobalRecord {
                            ty: self.written(global.ty, extract),
                            mutable: global.mutable,
                            slots: match &global.slots {
                                Slots::Global(ids) => SlotRecord::Global(
                                    ids.iter().map(|id| extract.global(*id)).collect(),
                                ),
                                Slots::Const(values) => SlotRecord::Const(scalars(extract, values)),
                                Slots::Local(_) | Slots::Memory { .. } => {
                                    unreachable!("a global is in a global or is a constant")
                                }
                            },
                            known: global.known,
                        });
                    }
                    results.bindings.push((local, globals));
                }
                ItemKind::Enum(_) => {
                    let id = self.enums.iter().position(|e| e.item == index);
                    let def = &self.enums[id.expect("every enum is declared")];
                    let members = def.members.iter();
                    let members = members.map(|m| (scalars(extract, &m.value), m.known));
                    results.members.push((local, members.collect()));
                }
                ItemKind::Struct(_) | ItemKind::Union(_) => {
                    let id = self.struct_of(index);
                    let fields = self.structs[id.0 as usize].fields.iter().enumerate();
                    let defaults = fields.filter_map(|(i, field)| {
                        field.default.as_ref().map(|d| (i, default(extract, d)))
                    });
                    let defaults: Vec<_> = defaults.collect();
                    if !defaults.is_empty() {
                        results.fields.push((local, defaults));
                    }
                }
                ItemKind::Fn(decl) if decl.sig.is_generic() => {
                    let id = self.generic_fn_items.iter().position(|i| *i == index);
                    let generic =
                        &self.generic_fns[id.expect("every generic function is declared")];
                    if generic.sig.defaults.iter().any(Option::is_some) {
                        let mut defaults = Vec::new();
                        for folded in &generic.sig.defaults {
                            defaults.push(folded.as_ref().map(|d| default(extract, d)));
                        }
                        let mut tys = Vec::new();
                        for ty in &generic.default_tys {
                            tys.push(ty.map(|ty| self.written(ty, extract)));
                        }
                        results.generic_defaults.push((local, defaults, tys));
                    }
                }
                _ => {}
            }
        }
        let own_funcs = share.imports.clone().chain(share.defined.clone());
        for id in own_funcs.map(|id| FuncId(id as u32)) {
            let defaults = &self.funcs[id.0 as usize].defaults;
            if defaults.iter().any(Option::is_some) {
                let defaults = defaults.iter();
                let defaults = defaults.map(|d| d.as_ref().map(|d| default(extract, d)));
                let defaults = defaults.collect();
                results.param_defaults.push((extract.func(id), defaults));
            }
        }
        for local in share.synths.clone() {
            let id = FuncId((synths_start + local) as u32);
            let sig = &self.funcs[id.0 as usize];
            let held = self.nested_fns.get(&id).map(|nested| nested.held());
            let held = held.map(|held| {
                let mut captures = Vec::new();
                for capture in self.captures(id) {
                    captures.push((capture.name.clone(), self.written(capture.ty, extract)));
                }
                (self.written(held, extract), captures)
            });
            let kind = match &self.synths[local] {
                Synth::Instance(instance) => {
                    let item = self.generic_fn_items[instance.generic.0 as usize];
                    let mut args = Vec::new();
                    for arg in &instance.args {
                        args.push(self.written(*arg, extract));
                    }
                    SynthKind::Instance(extract.item(item), args)
                }
                Synth::Eq(ty) => SynthKind::Eq(self.written(*ty, extract)),
                Synth::Wrapper(import) => SynthKind::Wrapper(extract.func(*import)),
                Synth::Export(..) | Synth::Nested | Synth::Foreign | Synth::Tests => {
                    SynthKind::Other
                }
            };
            results.synths.push(SynthRecord {
                name: sig.name.clone(),
                params: sig
                    .params
                    .iter()
                    .map(|(_, ty)| self.written(*ty, extract))
                    .collect(),
                ret: self.written(sig.ret, extract),
                held,
                kind,
            });
        }
        // The types the results of its functions hide, by function, in the
        // order of the result: those of instances of generic functions are
        // the instances', which are functions the checker made.
        let mut hidden: Vec<(FuncId, Vec<Hidden>)> = Vec::new();
        for def in self.opaques.iter() {
            let func = match &def.owner {
                Owner::Func(id) => *id,
                Owner::Instance(generic, args) => {
                    match self.fn_instances.get(&(*generic, args.clone())) {
                        Some(id) => *id,
                        None => continue,
                    }
                }
                Owner::Generic(_) => continue,
            };
            let owned = share.imports.contains(&(func.0 as usize))
                || share.defined.contains(&(func.0 as usize))
                || (func.0 as usize)
                    .checked_sub(synths_start)
                    .is_some_and(|local| share.synths.contains(&local));
            let Some(ty) = def.hidden.filter(|_| owned) else {
                continue;
            };
            match hidden.iter_mut().find(|(id, _)| *id == func) {
                Some((_, tys)) => tys.push((ty, def.bound)),
                None => hidden.push((func, vec![(ty, def.bound)])),
            }
        }
        for (func, tys) in hidden {
            let mut records = Vec::new();
            for (hidden, bound) in tys {
                records.push(OpaqueRecord {
                    hidden: self.written(hidden, extract),
                    bound: bound.map(|bound| self.written(bound, extract)),
                });
            }
            results.opaques.push((extract.func(func), records));
        }
        let dep = |extract: &mut Extract, dep: &Dep| match dep {
            Dep::Func(id) => DepRecord::Func(extract.func(*id)),
            Dep::Item(item) => DepRecord::Item(extract.item(*item)),
        };
        for index in items.clone() {
            if let Some(deps) = self.item_deps.get(&index).filter(|deps| !deps.is_empty()) {
                let deps = deps.iter().map(|d| dep(extract, d)).collect();
                results.item_deps.push((index - items.start, deps));
            }
        }
        let own = share.defined.clone().map(|id| FuncId(id as u32));
        let synths = share
            .synths
            .clone()
            .map(|local| FuncId((synths_start + local) as u32));
        for id in own.chain(synths) {
            if let Some(deps) = self.func_deps.get(&id).filter(|deps| !deps.is_empty()) {
                let deps = deps.iter().map(|d| dep(extract, d)).collect();
                results.func_deps.push((extract.func(id), deps));
            }
        }
        results
    }

    /// The struct or union that item `index` declares.
    fn struct_of(&self, index: usize) -> StructId {
        let decls = self.structs.iter().enumerate().filter(|(id, def)| {
            let id = StructId(*id as u32);
            def.instance.is_none() && !self.builtin_unions.contains(&id) && self.list != Some(id)
        });
        let mut decls = decls.filter(|(_, def)| def.item == index);
        let (id, _) = decls.next().expect("every struct is declared");
        StructId(id as u32)
    }

    /// `ty` as an interface writes it, naming what declares it as `extract`
    /// numbers items and functions.
    fn written(&self, ty: Ty, extract: &mut Extract) -> Written {
        match ty {
            Ty::Prim(prim) => Written::Prim(prim),
            Ty::Unit => Written::Unit,
            Ty::Never => Written::Never,
            Ty::Error => Written::Error,
            Ty::Type => Written::Type,
            Ty::Struct(id) => {
                let def = &self.structs[id.0 as usize];
                if let Some(instance) = &def.instance {
                    let builtin = self
                        .builtin_unions
                        .iter()
                        .position(|b| *b == instance.generic);
                    let base = match (self.list == Some(instance.generic), builtin) {
                        (true, _) => Base::List,
                        (false, Some(at)) => Base::Builtin(at as u8),
                        (false, None) => {
                            let item = self.structs[instance.generic.0 as usize].item;
                            Base::Decl(extract.item(item))
                        }
                    };
                    let args = instance.args.iter().map(|arg| self.written(*arg, extract));
                    return Written::Instance(base, args.collect());
                }
                if let Some(at) = self.builtin_unions.iter().position(|b| *b == id) {
                    return Written::Builtin(at as u8);
                }
                if self.list == Some(id) {
                    return Written::Builtin(LIST);
                }
                Written::Struct(extract.item(def.item))
            }
            Ty::Enum(id) => Written::Enum(extract.item(self.enums[id.0 as usize].item)),
            Ty::Ptr(id) => {
                let (pointee, mutable) = self.pointees[id.0 as usize];
                Written::Ptr(Box::new(self.written(pointee, extract)), mutable)
            }
            Ty::Tuple(id) => {
                let elems = self.tuples[id.0 as usize].iter();
                Written::Tuple(elems.map(|elem| self.written(*elem, extract)).collect())
            }
            Ty::Array(id) => {
                let Ty::Ptr(ptr) = self.arrays[id.0 as usize] else {
                    unreachable!("an array has a pointer to its elements")
                };
                let (elem, mutable) = self.pointees[ptr.0 as usize];
                Written::Array(Box::new(self.written(elem, extract)), mutable)
            }
            Ty::Fn(id) => {
                let (params, ret) = &self.fn_tys[id.0 as usize];
                let params = params.iter().map(|p| self.written(*p, extract)).collect();
                Written::Fn(params, Box::new(self.written(*ret, extract)))
            }
            Ty::Func(id) => Written::Func(extract.func(id)),
            Ty::Param(id) => {
                let param = Ty::Param(id);
                let structs = self.structs.iter().filter(|def| def.instance.is_none());
                if let Some(def) = structs.clone().find(|def| def.params.contains(&param)) {
                    let at = def.params.iter().position(|p| *p == param).unwrap();
                    return Written::Param(extract.item(def.item), at);
                }
                let mut generics = self.generic_fns.iter().enumerate();
                let generic = generics.find(|(_, g)| g.params.contains(&param));
                let (id, generic) = generic.expect("every type parameter is declared");
                let at = generic.params.iter().position(|p| *p == param).unwrap();
                Written::Param(extract.item(self.generic_fn_items[id]), at)
            }
            Ty::Opaque(id) => {
                let def = &self.opaques[id.0 as usize];
                let func = match &def.owner {
                    Owner::Func(func) => *func,
                    Owner::Instance(generic, args) => self.fn_instances[&(*generic, args.clone())],
                    Owner::Generic(_) => {
                        unreachable!("a generic function's result is an instance's")
                    }
                };
                let same = self.opaques.iter().take(id.0 as usize);
                let at = same.filter(|other| other.owner == def.owner).count();
                Written::Opaque(extract.func(func), at)
            }
        }
    }

    /// Gives package `package` of `program`, which `compiled` is already,
    /// what it compiled to, in place of folding and lowering it: see the
    /// module.
    pub(super) fn import_turn(&mut self, program: &Program, package: usize, compiled: &Compiled) {
        let artifact = &*compiled.artifact;
        let results = &artifact.interface.results;
        let items = program.packages[package].items.clone();
        let root = program.packages[package].root;
        let site = Span {
            file: root,
            start: 0,
            end: 0,
        };
        // Its functions, as declared: those the checker made for it are
        // placeholders, numbered after everything so far.
        let decls = self.funcs.len() - self.synths.len();
        let owned = |id: usize, ck: &Self| items.contains(&ck.func_items[id]);
        let imports = (0..self.import_count as usize).filter(|id| owned(*id, self));
        let defined = (self.import_count as usize..decls).filter(|id| owned(*id, self));
        let mut tables = Imported {
            imports: imports.map(|id| FuncId(id as u32)).collect(),
            defined: defined.map(|id| FuncId(id as u32)).collect(),
            synths: Vec::new(),
            globals: self.ir_globals.len(),
            data: self.link.data.len(),
            values: self.link.values.len(),
        };
        for record in &results.synths {
            let id = FuncId(self.funcs.len() as u32);
            self.synths.push(Synth::Foreign);
            self.funcs.push(FuncSig {
                name: record.name.clone(),
                params: Vec::new(),
                defaults: Vec::new(),
                ret: Ty::Unit,
            });
            tables.synths.push(id);
        }
        self.imported.insert(package, tables);
        // Placeholders for what it places, runs, defines and takes pointers
        // to, numbered as the artifact numbers them.
        for _ in 0..artifact.data.len() {
            self.link.data.push(DataDef {
                bytes: Vec::new(),
                fills: Vec::new(),
                align: 1,
                count: Scalar::Known(Const::I32(1)),
                how: Placing::Own,
            });
        }
        let nothing = ir::Func {
            name: String::new(),
            exports: Vec::new(),
            params: Vec::new(),
            results: Vec::new(),
            locals: Vec::new(),
            body: Vec::new(),
        };
        // Each as if asked for now, as far as the program is numbered.
        let (funcs, globals, table) = (self.funcs.len(), self.ir_globals.len(), self.table.len());
        for _ in 0..artifact.values.len() {
            self.link.values.push(ValueDef {
                how: Finding::Fold(nothing.clone()),
                item: None,
                span: site,
                instances: Vec::new(),
                funcs,
                globals,
                table,
                errors: 0,
            });
        }
        for global in &artifact.globals {
            self.ir_globals.push(global.clone());
            self.ir_inits.push(Scalar::Known(zero(global.ty)));
        }
        for id in &artifact.table {
            let func = self.foreign_func(program, package, *id);
            let next = self.table.len() as u32 + 1;
            self.table_indices.entry(func).or_insert(next);
            self.table.push(func);
        }
        // What its functions' results hide: each is there before anything
        // names it, as the signature of a function the checker made may,
        // and is settled once every one is.
        let mut settled = Vec::new();
        for (func, hidden) in &results.opaques {
            let func = self.foreign_func(program, package, *func);
            let owner = Owner::Func(func);
            for (at, record) in hidden.iter().enumerate() {
                let mut same = (0..self.opaques.len()).filter(|i| self.opaques[*i].owner == owner);
                let id = match same.nth(at) {
                    Some(id) => id,
                    None => {
                        let name = self.funcs[func.0 as usize].name.clone();
                        let bound = record.bound.as_ref();
                        let bound = bound.map(|bound| self.adopt(program, package, bound, site));
                        let def = OpaqueDef::settled(owner.clone(), name, root, bound);
                        self.opaques.push(def);
                        self.opaques.len() - 1
                    }
                };
                settled.push((id, &record.hidden));
            }
        }
        // One that hides a type that names another is settled after it,
        // as making an instance of what it hides checks what that hides.
        let mut done = vec![false; settled.len()];
        for at in 0..settled.len() {
            self.settle_hidden(program, package, &settled, &mut done, at, site);
        }
        // The functions the checker made for it, as it found them.
        for (local, record) in results.synths.iter().enumerate() {
            let id = self.imported[&package].synths[local];
            let params = record.params.iter();
            let params = params.map(|p| ("".to_string(), self.adopt(program, package, p, site)));
            let params = params.collect();
            let ret = self.adopt(program, package, &record.ret, site);
            self.funcs[id.0 as usize].params = params;
            self.funcs[id.0 as usize].ret = ret;
            if let Some((held, captures)) = &record.held {
                let held = self.adopt(program, package, held, site);
                let captures = captures.iter();
                let captures = captures
                    .map(|(name, ty)| (name.clone(), self.adopt(program, package, ty, site)));
                let captures = captures.collect();
                let name = record.name.clone();
                self.nested_fns
                    .insert(id, NestedFn::foreign(name, held, captures, site));
            }
            // What it was made for is had, rather than made again.
            match &record.kind {
                SynthKind::Instance(item, args) => {
                    let index = self.foreign_item(program, package, *item);
                    let generic = self.generic_fn_items.iter().position(|i| *i == index);
                    let generic =
                        GenericFnId(generic.expect("every generic function is declared") as u32);
                    let mut adopted = Vec::new();
                    for arg in args {
                        adopted.push(self.adopt(program, package, arg, site));
                    }
                    self.fn_instances.insert((generic, adopted), id);
                }
                SynthKind::Eq(ty) => {
                    let ty = self.adopt(program, package, ty, site);
                    self.eq_funcs.insert(ty, id);
                }
                SynthKind::Wrapper(import) => {
                    let import = self.foreign_func(program, package, *import);
                    self.wrappers.insert(import, id);
                }
                SynthKind::Other => {}
            }
        }
        // Its constants, as checking found them.
        for (local, globals) in &results.bindings {
            let first = self.constants[items.start + local].id;
            for (offset, record) in globals.iter().enumerate() {
                let slots = match &record.slots {
                    SlotRecord::Global(ids) => {
                        let ids = ids
                            .iter()
                            .map(|id| self.foreign_global(program, package, *id));
                        Slots::Global(ids.collect())
                    }
                    SlotRecord::Const(values) => {
                        Slots::Const(self.foreign_scalars(program, package, values))
                    }
                };
                self.globals[first + offset] = Some(GlobalDef {
                    ty: self.adopt(program, package, &record.ty, site),
                    mutable: record.mutable,
                    slots,
                    known: record.known,
                });
            }
        }
        for (local, members) in &results.members {
            let index = items.start + local;
            let id = self.enums.iter().position(|e| e.item == index);
            let id = id.expect("every enum is declared");
            for (member, (value, known)) in members.iter().enumerate() {
                let value = self.foreign_scalars(program, package, value);
                self.enums[id].members[member].value = value;
                self.enums[id].members[member].known = *known;
            }
        }
        for (local, defaults) in &results.fields {
            let id = self.struct_of(items.start + local);
            for (field, default) in defaults {
                let default = self.foreign_default(program, package, default);
                self.structs[id.0 as usize].fields[*field].default = Some(default);
            }
        }
        for (func, defaults) in &results.param_defaults {
            let func = self.foreign_func(program, package, *func);
            let defaults = defaults.iter();
            let defaults = defaults.map(|d| {
                d.as_ref()
                    .map(|d| self.foreign_default(program, package, d))
            });
            self.funcs[func.0 as usize].defaults = defaults.collect();
        }
        for (local, defaults, tys) in &results.generic_defaults {
            let index = items.start + local;
            let id = self.generic_fn_items.iter().position(|i| *i == index);
            let id = id.expect("every generic function is declared");
            let defaults = defaults.iter();
            let defaults = defaults.map(|d| {
                d.as_ref()
                    .map(|d| self.foreign_default(program, package, d))
            });
            self.generic_fns[id].sig.defaults = defaults.collect();
            let mut adopted = Vec::new();
            for ty in tys {
                adopted.push(ty.as_ref().map(|ty| self.adopt(program, package, ty, site)));
            }
            self.generic_fns[id].default_tys = adopted;
        }
        // Nothing of it is folded or lowered: its constants are found, and
        // its functions are the artifact's. What they name is known, for
        // code run for a constant to call.
        for index in items.clone() {
            self.constants[index].state = Visit::Done;
            self.item_deps.insert(index, Vec::new());
        }
        for (local, deps) in &results.item_deps {
            let deps = deps
                .iter()
                .map(|d| self.foreign_dep(program, package, d))
                .collect();
            self.item_deps.insert(items.start + local, deps);
        }
        for (func, deps) in &results.func_deps {
            let func = self.foreign_func(program, package, *func);
            let deps = deps
                .iter()
                .map(|d| self.foreign_dep(program, package, d))
                .collect();
            self.func_deps.insert(func, deps);
        }
        let tables = &self.imported[&package];
        let funcs: Vec<_> = tables
            .defined
            .iter()
            .chain(&tables.synths)
            .copied()
            .collect();
        for id in funcs {
            let name = self.funcs[id.0 as usize].name.clone();
            self.lowered.insert(
                id,
                ir::Func {
                    name,
                    ..nothing.clone()
                },
            );
            self.normally.insert(id);
        }
        // What is checked of a package wherever it is compiled: that what
        // it imports is what the world of this program gives. Its generic
        // functions are checked as declared in the turn of the next package
        // that is compiled, as what that places is that package's: nothing
        // more may be numbered as this package's than its artifact has.
        self.check_lists(&items);
        if !self.unread {
            self.check_imports(program, &items);
        }
    }

    /// Settles opaque type `at` of `settled`, the opaque types of package
    /// `package` with what each hides as written, after those that what it
    /// hides names.
    fn settle_hidden(
        &mut self,
        program: &Program,
        package: usize,
        settled: &[(usize, &Written)],
        done: &mut [bool],
        at: usize,
        site: Span,
    ) {
        if done[at] {
            return;
        }
        done[at] = true;
        let (id, written) = settled[at];
        let mut named = Vec::new();
        opaques_in(written, &mut named);
        for (func, index) in named {
            let func = self.foreign_func(program, package, func);
            let owner = Owner::Func(func);
            let mut same = (0..self.opaques.len()).filter(|i| self.opaques[*i].owner == owner);
            if let Some(other) = same.nth(index)
                && let Some(before) = settled.iter().position(|(id, _)| *id == other)
            {
                self.settle_hidden(program, package, settled, done, before, site);
            }
        }
        let ty = self.adopt(program, package, written, site);
        self.opaques[id].hidden = Some(ty);
        self.opaques[id].state = Visit::Done;
    }

    /// Whether function `id` is one of a package that is compiled already,
    /// whose body is in that package's artifact.
    pub(super) fn is_foreign(&self, id: FuncId) -> bool {
        let first = self.funcs.len() - self.synths.len();
        match (id.0 as usize).checked_sub(first) {
            Some(local) => matches!(self.synths[local], Synth::Foreign),
            None => self.imported.values().any(|tables| {
                tables.defined.binary_search(&id).is_ok()
                    || tables.imports.binary_search(&id).is_ok()
            }),
        }
    }

    /// The package of `program` whose artifact `foreign`, of the artifact
    /// of package `package`, names, and the index there.
    fn foreign_package(&self, program: &Program, package: usize, foreign: Foreign) -> usize {
        let artifact = &program.imported[self.compiled_of(program, package)].artifact;
        let name = &artifact.uses[foreign.package as usize];
        let found = program.packages.iter().position(|p| p.name == *name);
        found.expect("every package an artifact uses is linked before it")
    }

    /// Which of the packages of `program` that are compiled already is
    /// package `package`.
    fn compiled_of(&self, program: &Program, package: usize) -> usize {
        let root = program.packages[package].root;
        let found = program.imported.iter().position(|c| c.root == root);
        found.expect("the package is compiled already")
    }

    /// Function `id`, as the artifact of package `package` numbers it.
    fn foreign_func(&self, program: &Program, package: usize, id: FuncId) -> FuncId {
        let artifact = &program.imported[self.compiled_of(program, package)].artifact;
        let tables = &self.imported[&package];
        let (imports, own) = (
            tables.imports.len(),
            tables.defined.len() + tables.synths.len(),
        );
        let id = id.0 as usize;
        if id < imports {
            return tables.imports[id];
        }
        if id < imports + own {
            return self.own_func(tables, id - imports);
        }
        let foreign = artifact.foreign.funcs[id - imports - own];
        let other = self.foreign_package(program, package, foreign);
        let tables = &self.imported[&other];
        match foreign.kind {
            Kind::Import => tables.imports[foreign.index as usize],
            _ => self.own_func(tables, foreign.index as usize),
        }
    }

    /// The function at `index` among those a package defines and those
    /// the checker made for it, of a package with `tables`.
    fn own_func(&self, tables: &Imported, index: usize) -> FuncId {
        match index.checked_sub(tables.defined.len()) {
            Some(synth) => tables.synths[synth],
            None => tables.defined[index],
        }
    }

    /// Global `id`, as the artifact of package `package` numbers it.
    fn foreign_global(&self, program: &Program, package: usize, id: GlobalId) -> GlobalId {
        let artifact = &program.imported[self.compiled_of(program, package)].artifact;
        let own = artifact.globals.len();
        let (package, index) = match (id.0 as usize).checked_sub(own) {
            None => (package, id.0 as usize),
            Some(at) => {
                let foreign = artifact.foreign.globals[at];
                (
                    self.foreign_package(program, package, foreign),
                    foreign.index as usize,
                )
            }
        };
        GlobalId((self.imported[&package].globals + index) as u32)
    }

    /// The item at `index`, as the artifact of package `package` numbers
    /// items, in the program.
    fn foreign_item(&self, program: &Program, package: usize, index: usize) -> usize {
        let artifact = &program.imported[self.compiled_of(program, package)].artifact;
        let own = program.packages[package].items.len();
        match index.checked_sub(own) {
            None => program.packages[package].items.start + index,
            Some(at) => {
                let foreign = artifact.foreign.items[at];
                let other = self.foreign_package(program, package, foreign);
                program.packages[other].items.start + foreign.index as usize
            }
        }
    }

    /// `scalars`, each as the artifact of package `package` numbers what
    /// it names, as the program numbers it.
    fn foreign_scalars(
        &self,
        program: &Program,
        package: usize,
        scalars: &[Scalar],
    ) -> Vec<Scalar> {
        let scalar = |scalar: &Scalar| match scalar {
            Scalar::Known(c) => Scalar::Known(*c),
            Scalar::Linked(ty, symbol) => {
                Scalar::Linked(*ty, self.foreign_symbol(program, package, *symbol))
            }
        };
        scalars.iter().map(scalar).collect()
    }

    /// `dep`, as the artifact of package `package` numbers what it names, as
    /// the program numbers it.
    fn foreign_dep(&self, program: &Program, package: usize, dep: &DepRecord) -> Dep {
        match dep {
            DepRecord::Func(id) => Dep::Func(self.foreign_func(program, package, *id)),
            DepRecord::Item(item) => Dep::Item(self.foreign_item(program, package, *item)),
        }
    }

    fn foreign_default(
        &self,
        program: &Program,
        package: usize,
        default: &DefaultRecord,
    ) -> DefaultValue {
        match default {
            DefaultRecord::Folded(values) => {
                DefaultValue::Folded(self.foreign_scalars(program, package, values))
            }
            DefaultRecord::Failed => DefaultValue::Failed,
            DefaultRecord::Pending => DefaultValue::Pending,
        }
    }

    /// `symbol`, as the artifact of package `package` numbers what it names,
    /// as the program numbers it.
    fn foreign_symbol(&self, program: &Program, package: usize, symbol: Symbol) -> Symbol {
        let artifact = &program.imported[self.compiled_of(program, package)].artifact;
        match symbol {
            Symbol::Func(id) => Symbol::Func(self.foreign_func(program, package, id)),
            Symbol::Data(id, offset) => {
                let own = artifact.data.len();
                let (package, index) = match (id.0 as usize).checked_sub(own) {
                    None => (package, id.0 as usize),
                    Some(at) => {
                        let foreign = artifact.foreign.data[at];
                        if foreign.package == RETURN_AREA {
                            let Some(Scalar::Linked(_, Symbol::Data(area, _))) = self.return_area
                            else {
                                unreachable!("the return area is placed before any package's data")
                            };
                            return Symbol::Data(area, offset);
                        }
                        (
                            self.foreign_package(program, package, foreign),
                            foreign.index as usize,
                        )
                    }
                };
                Symbol::Data(
                    DataId((self.imported[&package].data + index) as u32),
                    offset,
                )
            }
            Symbol::Value(id, scalar) => {
                let own = artifact.values.len();
                let (package, index) = match (id.0 as usize).checked_sub(own) {
                    None => (package, id.0 as usize),
                    Some(at) => {
                        let foreign = artifact.foreign.values[at];
                        (
                            self.foreign_package(program, package, foreign),
                            foreign.index as usize,
                        )
                    }
                };
                Symbol::Value(
                    ValueId((self.imported[&package].values + index) as u32),
                    scalar,
                )
            }
        }
    }

    /// The type that `written` writes, of the artifact of package
    /// `package`: an instance that isn't made yet is made at `site`.
    fn adopt(&mut self, program: &Program, package: usize, written: &Written, site: Span) -> Ty {
        match written {
            Written::Prim(prim) => Ty::Prim(*prim),
            Written::Unit => Ty::Unit,
            Written::Never => Ty::Never,
            Written::Error => Ty::Error,
            Written::Type => Ty::Type,
            Written::Struct(item) => {
                Ty::Struct(self.struct_of(self.foreign_item(program, package, *item)))
            }
            Written::Enum(item) => {
                let index = self.foreign_item(program, package, *item);
                let id = self.enums.iter().position(|e| e.item == index);
                Ty::Enum(EnumId(id.expect("every enum is declared") as u32))
            }
            Written::Instance(base, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.adopt(program, package, arg, site))
                    .collect();
                match base {
                    Base::List => self.list_of(args, site),
                    Base::Builtin(at) => {
                        let generic = self.builtin_unions[*at as usize];
                        self.instantiate(generic, args, site)
                    }
                    Base::Decl(item) => {
                        let generic = self.struct_of(self.foreign_item(program, package, *item));
                        self.instantiate(generic, args, site)
                    }
                }
            }
            Written::Builtin(LIST) => Ty::Struct(self.list.expect("the list is declared")),
            Written::Builtin(at) => Ty::Struct(self.builtin_unions[*at as usize]),
            Written::Ptr(pointee, mutable) => {
                let pointee = self.adopt(program, package, pointee, site);
                self.ptr_to(pointee, *mutable)
            }
            Written::Tuple(elems) => {
                let elems = elems
                    .iter()
                    .map(|elem| self.adopt(program, package, elem, site));
                let elems = elems.collect();
                self.tuple_of(elems)
            }
            Written::Array(elem, mutable) => {
                let elem = self.adopt(program, package, elem, site);
                self.array_of(elem, *mutable)
            }
            Written::Fn(params, ret) => {
                let params = params
                    .iter()
                    .map(|p| self.adopt(program, package, p, site))
                    .collect();
                let ret = self.adopt(program, package, ret, site);
                self.fn_of(params, ret)
            }
            Written::Func(id) => Ty::Func(self.foreign_func(program, package, *id)),
            Written::Opaque(func, at) => {
                let func = self.foreign_func(program, package, *func);
                let owner = Owner::Func(func);
                let mut same = (0..self.opaques.len()).filter(|i| self.opaques[*i].owner == owner);
                let id = same
                    .nth(*at)
                    .expect("what a result hides is settled before it is named");
                Ty::Opaque(super::OpaqueId(id as u32))
            }
            Written::Param(item, at) => {
                let index = self.foreign_item(program, package, *item);
                match &program.items[index].kind {
                    ItemKind::Struct(_) | ItemKind::Union(_) => {
                        let id = self.struct_of(index);
                        self.structs[id.0 as usize].params[*at]
                    }
                    _ => {
                        let id = self.generic_fn_items.iter().position(|i| *i == index);
                        let id =
                            GenericFnId(id.expect("every generic function is declared") as u32);
                        self.generic_fns[id.0 as usize].params[*at]
                    }
                }
            }
        }
    }
}

/// Adds each opaque type that `written` names, by its function and its
/// place in the result, to `out`.
fn opaques_in(written: &Written, out: &mut Vec<(FuncId, usize)>) {
    match written {
        Written::Opaque(func, at) => out.push((*func, *at)),
        Written::Instance(_, args) | Written::Tuple(args) => {
            args.iter().for_each(|arg| opaques_in(arg, out));
        }
        Written::Ptr(inner, _) | Written::Array(inner, _) => opaques_in(inner, out),
        Written::Fn(params, ret) => {
            params.iter().for_each(|param| opaques_in(param, out));
            opaques_in(ret, out);
        }
        Written::Prim(_)
        | Written::Unit
        | Written::Never
        | Written::Error
        | Written::Type
        | Written::Struct(_)
        | Written::Enum(_)
        | Written::Builtin(_)
        | Written::Func(_)
        | Written::Param(..) => {}
    }
}

/// `item` with the body of a function that isn't generic left out, which
/// its artifact has what is made of: a generic function's body is kept, as
/// each instance of it is made where it is used.
fn stripped(item: &Item) -> Item {
    let mut item = item.clone();
    if let ItemKind::Fn(decl) = &mut item.kind
        && !decl.sig.is_generic()
    {
        decl.body = Vec::new();
    }
    item
}

impl Encode for Interface {
    fn encode(&self, w: &mut Writer) {
        self.modules.encode(w);
        self.depends.encode(w);
        self.declared.encode(w);
        self.results.encode(w);
    }
}

impl Decode for Interface {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Self {
            modules: Decode::decode(r)?,
            depends: Decode::decode(r)?,
            declared: Decode::decode(r)?,
            results: Decode::decode(r)?,
        })
    }
}

impl Encode for Results {
    fn encode(&self, w: &mut Writer) {
        self.synths.encode(w);
        self.bindings.encode(w);
        self.members.encode(w);
        self.fields.encode(w);
        self.param_defaults.encode(w);
        self.generic_defaults.encode(w);
        self.opaques.encode(w);
        self.item_deps.encode(w);
        self.func_deps.encode(w);
    }
}

impl Decode for Results {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Self {
            synths: Decode::decode(r)?,
            bindings: Decode::decode(r)?,
            members: Decode::decode(r)?,
            fields: Decode::decode(r)?,
            param_defaults: Decode::decode(r)?,
            generic_defaults: Decode::decode(r)?,
            opaques: Decode::decode(r)?,
            item_deps: Decode::decode(r)?,
            func_deps: Decode::decode(r)?,
        })
    }
}

impl Encode for OpaqueRecord {
    fn encode(&self, w: &mut Writer) {
        self.hidden.encode(w);
        self.bound.encode(w);
    }
}

impl Decode for OpaqueRecord {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Self {
            hidden: Decode::decode(r)?,
            bound: Decode::decode(r)?,
        })
    }
}

impl Encode for DepRecord {
    fn encode(&self, w: &mut Writer) {
        match self {
            Self::Func(id) => {
                w.tag(0);
                id.encode(w);
            }
            Self::Item(item) => {
                w.tag(1);
                item.encode(w);
            }
        }
    }
}

impl Decode for DepRecord {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        match r.tag()? {
            0 => Ok(Self::Func(Decode::decode(r)?)),
            1 => Ok(Self::Item(Decode::decode(r)?)),
            tag => Err(bad("dependency", tag)),
        }
    }
}

impl Encode for SynthRecord {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.params.encode(w);
        self.ret.encode(w);
        self.held.encode(w);
        self.kind.encode(w);
    }
}

impl Decode for SynthRecord {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Self {
            name: Decode::decode(r)?,
            params: Decode::decode(r)?,
            ret: Decode::decode(r)?,
            held: Decode::decode(r)?,
            kind: Decode::decode(r)?,
        })
    }
}

impl Encode for SynthKind {
    fn encode(&self, w: &mut Writer) {
        match self {
            Self::Instance(item, args) => {
                w.tag(0);
                item.encode(w);
                args.encode(w);
            }
            Self::Eq(ty) => {
                w.tag(1);
                ty.encode(w);
            }
            Self::Wrapper(import) => {
                w.tag(2);
                import.encode(w);
            }
            Self::Other => w.tag(3),
        }
    }
}

impl Decode for SynthKind {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        match r.tag()? {
            0 => Ok(Self::Instance(Decode::decode(r)?, Decode::decode(r)?)),
            1 => Ok(Self::Eq(Decode::decode(r)?)),
            2 => Ok(Self::Wrapper(Decode::decode(r)?)),
            3 => Ok(Self::Other),
            tag => Err(bad("synthesized function", tag)),
        }
    }
}

impl Encode for GlobalRecord {
    fn encode(&self, w: &mut Writer) {
        self.ty.encode(w);
        self.mutable.encode(w);
        match &self.slots {
            SlotRecord::Global(ids) => {
                w.tag(0);
                ids.encode(w);
            }
            SlotRecord::Const(values) => {
                w.tag(1);
                values.encode(w);
            }
        }
        self.known.encode(w);
    }
}

impl Decode for GlobalRecord {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Self {
            ty: Decode::decode(r)?,
            mutable: Decode::decode(r)?,
            slots: match r.tag()? {
                0 => SlotRecord::Global(Decode::decode(r)?),
                1 => SlotRecord::Const(Decode::decode(r)?),
                tag => return Err(bad("slots", tag)),
            },
            known: Decode::decode(r)?,
        })
    }
}

impl Encode for DefaultRecord {
    fn encode(&self, w: &mut Writer) {
        match self {
            Self::Folded(values) => {
                w.tag(0);
                values.encode(w);
            }
            Self::Failed => w.tag(1),
            Self::Pending => w.tag(2),
        }
    }
}

impl Decode for DefaultRecord {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        match r.tag()? {
            0 => Ok(Self::Folded(Decode::decode(r)?)),
            1 => Ok(Self::Failed),
            2 => Ok(Self::Pending),
            tag => Err(bad("default", tag)),
        }
    }
}

impl Encode for Written {
    fn encode(&self, w: &mut Writer) {
        match self {
            Self::Prim(prim) => {
                w.tag(0);
                prim.encode(w);
            }
            Self::Unit => w.tag(1),
            Self::Never => w.tag(2),
            Self::Error => w.tag(3),
            Self::Type => w.tag(4),
            Self::Struct(item) => {
                w.tag(5);
                item.encode(w);
            }
            Self::Enum(item) => {
                w.tag(6);
                item.encode(w);
            }
            Self::Instance(base, args) => {
                w.tag(7);
                match base {
                    Base::List => w.tag(0),
                    Base::Decl(item) => {
                        w.tag(1);
                        item.encode(w);
                    }
                    Base::Builtin(at) => {
                        w.tag(2);
                        at.encode(w);
                    }
                }
                args.encode(w);
            }
            Self::Builtin(at) => {
                w.tag(8);
                at.encode(w);
            }
            Self::Ptr(pointee, mutable) => {
                w.tag(9);
                pointee.encode(w);
                mutable.encode(w);
            }
            Self::Tuple(elems) => {
                w.tag(10);
                elems.encode(w);
            }
            Self::Array(elem, mutable) => {
                w.tag(11);
                elem.encode(w);
                mutable.encode(w);
            }
            Self::Fn(params, ret) => {
                w.tag(12);
                params.encode(w);
                ret.encode(w);
            }
            Self::Func(id) => {
                w.tag(13);
                id.encode(w);
            }
            Self::Opaque(func, at) => {
                w.tag(14);
                func.encode(w);
                at.encode(w);
            }
            Self::Param(item, at) => {
                w.tag(15);
                item.encode(w);
                at.encode(w);
            }
        }
    }
}

impl Decode for Written {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Self::Prim(Decode::decode(r)?),
            1 => Self::Unit,
            2 => Self::Never,
            3 => Self::Error,
            4 => Self::Type,
            5 => Self::Struct(Decode::decode(r)?),
            6 => Self::Enum(Decode::decode(r)?),
            7 => {
                let base = match r.tag()? {
                    0 => Base::List,
                    1 => Base::Decl(Decode::decode(r)?),
                    2 => Base::Builtin(Decode::decode(r)?),
                    tag => return Err(bad("generic", tag)),
                };
                Self::Instance(base, Decode::decode(r)?)
            }
            8 => Self::Builtin(Decode::decode(r)?),
            9 => Self::Ptr(Decode::decode(r)?, Decode::decode(r)?),
            10 => Self::Tuple(Decode::decode(r)?),
            11 => Self::Array(Decode::decode(r)?, Decode::decode(r)?),
            12 => Self::Fn(Decode::decode(r)?, Decode::decode(r)?),
            13 => Self::Func(Decode::decode(r)?),
            14 => Self::Opaque(Decode::decode(r)?, Decode::decode(r)?),
            15 => Self::Param(Decode::decode(r)?, Decode::decode(r)?),
            tag => return Err(bad("type", tag)),
        })
    }
}

/// A `use` of an interface, with its files as the reader gives them, and
/// the library of a package it leads to as the reader gives that.
fn read_use(r: &mut Reader) -> Result<Use, DecodeError> {
    Ok(Use {
        module: Decode::decode(r)?,
        name: Decode::decode(r)?,
        target: match r.tag()? {
            0 => Decode::decode(r)?,
            1 => {
                let library = usize::decode(r)?;
                r.library(library)?
            }
            tag => return Err(bad("use", tag)),
        },
        target_path: Decode::decode(r)?,
        path: Decode::decode(r)?,
        members: Decode::decode(r)?,
        is_pub: Decode::decode(r)?,
        decl: Decode::decode(r)?,
    })
}

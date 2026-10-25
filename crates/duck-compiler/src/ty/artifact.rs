//! What a package of a program compiles to: the [`Artifact`] that linking
//! makes a module of, with those of the packages it depends on and of
//! those that depend on it.
//!
//! A package is checked and lowered after every package it depends on, as
//! a whole, so what is lowered of it is made of its own source and of what
//! those it depends on are, and of nothing else. An artifact holds it,
//! numbered as its own: its imports, the functions it defines and those the
//! checker makes for it, its globals, the functions it is first to take
//! pointers to, what it places in memory, its constants that are only known
//! by running them, what is checked of those once they are, and the order
//! it asks for each to be placed, found or checked in. What it names of
//! another package it names by that package's name and its place there.
//!
//! The checker makes each instance of a generic function, and each other
//! function it makes, once for the whole program: a package that uses one
//! that a package lowered before it made names that one, though it may not
//! depend on that package. Its artifact is then of the program, and not of
//! the package alone.
//!
//! [`link`] makes a module of the artifacts of a program, each package's
//! after those it depends on: it numbers each package's after those before
//! it, and places, runs and checks what each asks for, in turn. That is the
//! module that [`super::check`] makes of the whole program.
//!
//! [`Artifact::encode`] writes one as bytes, and [`Artifact::decode`] reads
//! them back, so that one is kept, sent and linked elsewhere.

use std::ops::Range;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::codec::{Decode, DecodeError, Encode, Reader, Writer, bad, ids, lists};
use crate::file::{FileId, FileManager, Settings};
use crate::ir::{
    self, BinOp, Const, DataId, Expr, FuncId, FuncType, GlobalId, LoadOp, LocalId, Stmt, StoreOp,
    Symbol, UnOp, ValType, ValueId,
};
use crate::lex::Span;
use crate::load::Program;
use crate::world::RUN_EXPORT;

use super::canonical::RETURN_AREA_ALIGN;
use super::interface::Interface;
use super::link::{
    Check, CheckDef, DataDef, Event, Fill, Finding, Linking, Lowered, Placing, ValueDef,
};
use super::unions::Holds;
use super::{
    Cell, Checker, DEFAULT_FUEL, InstanceSite, Leaf, PAGE_SIZE, Prim, Scalar, TypeError,
    TypeErrorKind,
};

/// What an artifact's bytes start with, and the version of their format,
/// which changes whenever the format does.
const MAGIC: &[u8; 8] = b"duckart\0";
pub const VERSION: u32 = 6;

/// The package that the return area is of, among those an artifact uses:
/// none, as it is the program's.
pub(super) const RETURN_AREA: u32 = u32::MAX;

/// The binary operators, in the order of their tags.
const BIN_OPS: [BinOp; 30] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::Div,
    BinOp::DivS,
    BinOp::DivU,
    BinOp::RemS,
    BinOp::RemU,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::ShrS,
    BinOp::ShrU,
    BinOp::Min,
    BinOp::Max,
    BinOp::Eq,
    BinOp::Ne,
    BinOp::Lt,
    BinOp::LtS,
    BinOp::LtU,
    BinOp::Le,
    BinOp::LeS,
    BinOp::LeU,
    BinOp::Gt,
    BinOp::GtS,
    BinOp::GtU,
    BinOp::Ge,
    BinOp::GeS,
    BinOp::GeU,
];

/// The primitive types, in the order of their tags.
const PRIMS: [Prim; 13] = [
    Prim::I8,
    Prim::I16,
    Prim::I32,
    Prim::I64,
    Prim::Int,
    Prim::U8,
    Prim::U16,
    Prim::U32,
    Prim::U64,
    Prim::Uint,
    Prim::F32,
    Prim::F64,
    Prim::Bool,
];

/// What a package of a program compiles to.
#[derive(Debug, Clone, PartialEq)]
pub struct Artifact {
    /// The name of the package, which another names it by.
    pub name: String,
    /// The packages it names what of, by name.
    pub(super) uses: Vec<String>,
    /// The files of its spans, by name.
    files: Vec<String>,
    /// How many items of the program are its own.
    pub(super) items: usize,
    imports: Vec<ir::Import>,
    /// The functions it defines, and after those the functions the checker
    /// made for it, in the order they were made.
    funcs: Vec<ir::Func>,
    /// How many of `funcs` it defines.
    defined: usize,
    pub(super) globals: Vec<ir::Global>,
    /// What each of `globals` starts as.
    inits: Vec<Scalar>,
    /// The functions it was the first to take pointers to, in order.
    pub(super) table: Vec<FuncId>,
    pub(super) data: Vec<DataDef>,
    pub(super) values: Vec<ValueDef>,
    checks: Vec<CheckDef>,
    events: Vec<Event>,
    /// What it names of other packages: functions, globals, data, values
    /// and items, each numbered after its own of the kind.
    pub(super) foreign: Foreigns,
    /// What a program that uses the package is checked against.
    pub(super) interface: Interface,
    /// The function the program runs, if it is the package of the entry
    /// and the program has one: of it or of a package it uses.
    start: Option<FuncId>,
    /// The most bytes that its imports and what it exports pass in the
    /// return area.
    passed: u32,
}

/// What an artifact names of other packages, by kind, each numbered after
/// those it has of its own of the kind.
#[derive(Debug, Clone, Default, PartialEq)]
pub(super) struct Foreigns {
    pub(super) funcs: Vec<Foreign>,
    pub(super) globals: Vec<Foreign>,
    pub(super) data: Vec<Foreign>,
    pub(super) values: Vec<Foreign>,
    pub(super) items: Vec<Foreign>,
}

/// What an artifact names of another package.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) struct Foreign {
    /// The package, by its place among those the artifact uses: or
    /// [`RETURN_AREA`].
    pub(super) package: u32,
    pub(super) kind: Kind,
    /// Its place among those of its kind there.
    pub(super) index: u32,
}

/// What kind of thing a [`Foreign`] is.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Kind {
    Import,
    /// A function that a package defines, or that the checker made for it,
    /// numbered after those it defines.
    Func,
    Global,
    Data,
    Value,
    /// An item whose constants a value is among, which runs on its fuel.
    Item,
}

/// What a package of a program has of what is lowered of the program, by
/// where it is in each list.
#[derive(Debug, Clone)]
pub(super) struct Share {
    pub(super) imports: Range<usize>,
    pub(super) defined: Range<usize>,
    /// Of the functions the checker made, by their place among those.
    pub(super) synths: Range<usize>,
    pub(super) globals: Range<usize>,
    pub(super) table: Range<usize>,
    pub(super) data: Range<usize>,
    pub(super) values: Range<usize>,
    pub(super) checks: Range<usize>,
    pub(super) events: Range<usize>,
    pub(super) items: Range<usize>,
}

/// Where each list of what is lowered of a program was, where a package
/// was about to be lowered: how many there were of each.
#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Marks {
    pub(super) synths: usize,
    pub(super) globals: usize,
    pub(super) table: usize,
    pub(super) data: usize,
    pub(super) values: usize,
    pub(super) checks: usize,
    pub(super) events: usize,
}

/// Making the artifact of one package of a lowered program.
pub(super) struct Extract<'c> {
    ck: &'c Checker,
    shares: &'c [Share],
    /// The name of each package.
    names: &'c [String],
    /// The package whose artifact it is.
    package: usize,
    uses: Vec<String>,
    /// The files of its spans, in the order they are numbered.
    files: Vec<FileId>,
    file_index: FxHashMap<FileId, usize>,
    foreign: Foreigns,
    foreign_index: FxHashMap<Foreign, u32>,
}

/// What lowering numbers that an artifact numbers as its own, and that
/// the module that runs a constant numbers as it holds them.
pub(super) enum Ref {
    Func(FuncId),
    Global(GlobalId),
    Symbol(Symbol),
}

/// Where each kind of what a package has starts in the program that links
/// it.
#[derive(Debug, Clone, Default)]
struct Base {
    imports: usize,
    /// Where the functions it defines start, and how many there are.
    defined: usize,
    defines: usize,
    synths: usize,
    globals: usize,
    table: usize,
    data: usize,
    values: usize,
    checks: usize,
    items: usize,
}

/// What linking is given of the program the artifacts make.
#[derive(Default)]
struct Linked {
    imports: Vec<ir::Import>,
    globals: Vec<ir::Global>,
    inits: Vec<Scalar>,
    table: Vec<FuncId>,
    data: Vec<DataDef>,
    values: Vec<ValueDef>,
    checks: Vec<CheckDef>,
    events: Vec<Event>,
}

/// Numbering what an artifact has as the program that links it does.
struct Join<'a> {
    artifact: &'a Artifact,
    /// Where what each package has starts, and where its files do.
    bases: &'a [(Base, usize)],
    package: usize,
    /// Each package the artifact uses, by its place among the program's.
    packages: &'a [usize],
}

impl Checker {
    /// Where each list of what is lowered is, for the package about to be
    /// lowered to start at.
    pub(super) fn marks(&self) -> Marks {
        Marks {
            synths: self.synths.len(),
            globals: self.ir_globals.len(),
            table: self.table.len(),
            data: self.link.data.len(),
            values: self.link.values.len(),
            checks: self.link.checks.len(),
            events: self.link.events.len(),
        }
    }

    /// The artifact of each package of `program`, which is lowered, with
    /// `imports` and `funcs` and the function `start` that it runs: those
    /// it depends on first. Each package is named by the name of its root
    /// module, and each file by its own, as `files` give them.
    pub(super) fn artifacts(
        &self,
        program: &Program,
        files: &mut impl FileManager,
        imports: &[ir::Import],
        funcs: &[ir::Func],
        start: Option<FuncId>,
    ) -> Vec<Artifact> {
        let names: Vec<_> = program
            .packages
            .iter()
            .map(|package| package.name.clone())
            .collect();
        let shares = self.shares(program);
        let mut artifacts = Vec::new();
        for (index, share) in shares.iter().enumerate() {
            // Its files are its package's, in their order, so that where an
            // error of linking is can be told from which package's file it
            // is in.
            let own_files = program.packages[index].files.clone();
            let file_index = own_files.iter().enumerate().map(|(i, f)| (*f, i)).collect();
            let mut extract = Extract {
                ck: self,
                shares: &shares,
                names: &names,
                package: index,
                uses: Vec::new(),
                files: own_files,
                file_index,
                foreign: Foreigns::default(),
                foreign_index: FxHashMap::default(),
            };
            // Only the package of the entry exports anything, and runs
            // what it names, which may be of another.
            let entry = program.packages[index].root == program.entry;
            let start = start.filter(|_| entry);
            // What the interface names of other packages, the artifact
            // names too.
            let interface = self.interface(program, index, &mut extract);
            let mut artifact = extract.artifact(share, imports, funcs, start);
            artifact.interface = interface;
            artifact.files = extract
                .files
                .iter()
                .map(|id| files.display_name(*id))
                .collect();
            let imports = share.imports.start as u32..share.imports.end as u32;
            artifact.passed = self.passed(program, imports, entry);
            artifacts.push(artifact);
        }
        artifacts
    }

    /// What each package of `program` has of what is lowered of it.
    fn shares(&self, program: &Program) -> Vec<Share> {
        let decls = self.funcs.len() - self.synths.len();
        let marks = &self.package_marks;
        let mut shares = Vec::new();
        for (index, package) in program.packages.iter().enumerate() {
            let items = package.items.clone();
            let of = |ids: Range<usize>| {
                let own: Vec<_> = ids
                    .filter(|id| items.contains(&self.func_items[*id]))
                    .collect();
                match (own.first(), own.last()) {
                    (Some(first), Some(last)) => *first..*last + 1,
                    _ => 0..0,
                }
            };
            let imports = of(0..self.import_count as usize);
            let defined = of(self.import_count as usize..decls);
            // What is made once every package is lowered is the entry's,
            // which is last.
            let next = marks.get(index + 1).copied();
            let (from, to) = (marks[index], next.unwrap_or(self.marks()));
            shares.push(Share {
                imports,
                defined,
                synths: from.synths..to.synths,
                globals: from.globals..to.globals,
                table: from.table..to.table,
                data: from.data..to.data,
                values: from.values..to.values,
                checks: from.checks..to.checks,
                events: from.events..to.events,
                items,
            });
        }
        shares
    }
}

impl Extract<'_> {
    /// What package `package` has of the program.
    pub(super) fn share(&self, package: usize) -> &Share {
        &self.shares[package]
    }

    fn artifact(
        &mut self,
        share: &Share,
        imports: &[ir::Import],
        funcs: &[ir::Func],
        start: Option<FuncId>,
    ) -> Artifact {
        let ck = self.ck;
        let first = ck.import_count as usize;
        let synths = ck.funcs.len() - ck.synths.len();
        let own = share
            .defined
            .clone()
            .chain(share.synths.clone().map(|i| synths + i));
        let mut own: Vec<_> = own.map(|id| funcs[id - first].clone()).collect();
        for func in &mut own {
            self.renumber_stmts(&mut func.body);
        }
        let inits = ck.ir_inits[share.globals.clone()].iter();
        let inits = inits.map(|init| self.scalar(*init)).collect();
        let table = ck.table[share.table.clone()].iter();
        let table = table.map(|id| self.func(*id)).collect();
        let data = ck.link.data[share.data.clone()].iter();
        let data = data.map(|def| self.data(def)).collect();
        let values = ck.link.values[share.values.clone()].iter();
        let values = values.map(|def| self.value(def, share)).collect();
        let checks = ck.link.checks[share.checks.clone()].iter();
        let checks = checks.map(|def| self.check(def)).collect();
        let events = ck.link.events[share.events.clone()].iter();
        let events = events
            .filter_map(|event| self.event(*event, share))
            .collect();
        Artifact {
            name: self.names[self.package].clone(),
            uses: self.uses.clone(),
            files: Vec::new(),
            items: share.items.len(),
            imports: imports[share.imports.clone()].to_vec(),
            defined: share.defined.len(),
            funcs: own,
            globals: ck.ir_globals[share.globals.clone()].to_vec(),
            inits,
            table,
            data,
            values,
            checks,
            events,
            foreign: self.foreign.clone(),
            start: start.map(|id| self.func(id)),
            passed: 0,
            interface: Interface::default(),
        }
    }

    /// The package that has function `id`, and the kind and place of it
    /// there.
    fn func_owner(&self, id: FuncId) -> (usize, Kind, u32) {
        let id = id.0 as usize;
        let synths = self.ck.funcs.len() - self.ck.synths.len();
        for (package, share) in self.shares.iter().enumerate() {
            if share.imports.contains(&id) {
                return (package, Kind::Import, (id - share.imports.start) as u32);
            }
            if share.defined.contains(&id) {
                return (package, Kind::Func, (id - share.defined.start) as u32);
            }
            if id >= synths && share.synths.contains(&(id - synths)) {
                let at = share.defined.len() + id - synths - share.synths.start;
                return (package, Kind::Func, at as u32);
            }
        }
        unreachable!("every function is a package's")
    }

    /// Function `id` of the program, numbered as the artifact's.
    pub(super) fn func(&mut self, id: FuncId) -> FuncId {
        let (package, kind, index) = self.func_owner(id);
        let share = &self.shares[self.package];
        let own = share.imports.len() as u32;
        let funcs = (share.defined.len() + share.synths.len()) as u32;
        if package == self.package {
            return FuncId(match kind {
                Kind::Import => index,
                _ => own + index,
            });
        }
        FuncId(own + funcs + self.foreign(package, kind, index))
    }

    /// Global `id` of the program, numbered as the artifact's.
    pub(super) fn global(&mut self, id: GlobalId) -> GlobalId {
        let at = id.0 as usize;
        let (package, share) = self.owner(|share| &share.globals, at);
        let own = self.shares[self.package].globals.len() as u32;
        let index = (at - share.globals.start) as u32;
        match package == self.package {
            true => GlobalId(index),
            false => GlobalId(own + self.foreign(package, Kind::Global, index)),
        }
    }

    /// Data `id` of the program, numbered as the artifact's.
    fn data_id(&mut self, id: DataId) -> DataId {
        let at = id.0 as usize;
        let own = self.shares[self.package].data.len() as u32;
        // The return area is placed before any package's data.
        if self.shares.iter().all(|share| !share.data.contains(&at)) {
            let foreign = Foreign {
                package: RETURN_AREA,
                kind: Kind::Data,
                index: 0,
            };
            return DataId(own + self.add_foreign(foreign));
        }
        let (package, share) = self.owner(|share| &share.data, at);
        let index = (at - share.data.start) as u32;
        match package == self.package {
            true => DataId(index),
            false => DataId(own + self.foreign(package, Kind::Data, index)),
        }
    }

    /// Value `id` of the program, numbered as the artifact's.
    fn value_id(&mut self, id: ValueId) -> ValueId {
        let at = id.0 as usize;
        let (package, share) = self.owner(|share| &share.values, at);
        let own = self.shares[self.package].values.len() as u32;
        let index = (at - share.values.start) as u32;
        match package == self.package {
            true => ValueId(index),
            false => ValueId(own + self.foreign(package, Kind::Value, index)),
        }
    }

    /// Item `item` of the program, numbered as the artifact's.
    pub(super) fn item(&mut self, item: usize) -> usize {
        let (package, share) = self.owner(|share| &share.items, item);
        let own = self.shares[self.package].items.len();
        let index = item - share.items.start;
        match package == self.package {
            true => index,
            false => own + self.foreign(package, Kind::Item, index as u32) as usize,
        }
    }

    /// The package whose range of `range` holds `at`, and its share.
    fn owner(&self, range: impl Fn(&Share) -> &Range<usize>, at: usize) -> (usize, &Share) {
        let mut shares = self.shares.iter().enumerate();
        let found = shares.find(|(_, share)| range(share).contains(&at));
        found.expect("every part of the program is a package's")
    }

    /// The place among those the artifact names of other packages of what
    /// is of `kind` at `index` of `package`.
    fn foreign(&mut self, package: usize, kind: Kind, index: u32) -> u32 {
        let name = &self.names[package];
        let used = match self.uses.iter().position(|used| used == name) {
            Some(used) => used,
            None => {
                self.uses.push(name.clone());
                self.uses.len() - 1
            }
        };
        let foreign = Foreign {
            package: used as u32,
            kind,
            index,
        };
        self.add_foreign(foreign)
    }

    fn add_foreign(&mut self, foreign: Foreign) -> u32 {
        if let Some(at) = self.foreign_index.get(&foreign) {
            return *at;
        }
        let list = match foreign.kind {
            Kind::Import | Kind::Func => &mut self.foreign.funcs,
            Kind::Global => &mut self.foreign.globals,
            Kind::Data => &mut self.foreign.data,
            Kind::Value => &mut self.foreign.values,
            Kind::Item => &mut self.foreign.items,
        };
        list.push(foreign);
        let at = list.len() as u32 - 1;
        self.foreign_index.insert(foreign, at);
        at
    }

    fn symbol(&mut self, symbol: Symbol) -> Symbol {
        match symbol {
            Symbol::Data(id, offset) => Symbol::Data(self.data_id(id), offset),
            Symbol::Value(id, index) => Symbol::Value(self.value_id(id), index),
            Symbol::Func(id) => Symbol::Func(self.func(id)),
        }
    }

    pub(super) fn scalar(&mut self, scalar: Scalar) -> Scalar {
        match scalar {
            Scalar::Known(c) => Scalar::Known(c),
            Scalar::Linked(ty, symbol) => Scalar::Linked(ty, self.symbol(symbol)),
        }
    }

    fn span(&mut self, span: Span) -> Span {
        let next = self.files.len();
        let index = *self.file_index.entry(span.file).or_insert(next);
        if index == next {
            self.files.push(span.file);
        }
        Span {
            file: FileId::minted(index),
            ..span
        }
    }

    fn renumber_stmts(&mut self, body: &mut [Stmt]) {
        renumber(body, &mut |r| match r {
            Ref::Func(id) => Ref::Func(self.func(id)),
            Ref::Global(id) => Ref::Global(self.global(id)),
            Ref::Symbol(symbol) => Ref::Symbol(self.symbol(symbol)),
        });
    }

    fn data(&mut self, def: &DataDef) -> DataDef {
        let fills = def.fills.iter().map(|fill| Fill {
            offset: fill.offset,
            cells: fill.cells.clone(),
            scalars: fill.scalars.iter().map(|s| self.scalar(*s)).collect(),
        });
        DataDef {
            bytes: def.bytes.clone(),
            fills: fills.collect(),
            align: def.align,
            count: self.scalar(def.count),
            how: def.how.clone(),
        }
    }

    fn value(&mut self, def: &ValueDef, share: &Share) -> ValueDef {
        let ck = self.ck;
        let decls = ck.funcs.len() - ck.synths.len();
        let how = match &def.how {
            Finding::Fold(thunk) => {
                let mut thunk = thunk.clone();
                self.renumber_stmts(&mut thunk.body);
                Finding::Fold(thunk)
            }
            Finding::Run { thunk, reached } => {
                let mut thunk = thunk.clone();
                self.renumber_stmts(&mut thunk.body);
                let reached = reached.iter().map(|id| self.func(*id)).collect();
                Finding::Run { thunk, reached }
            }
            Finding::Count { from, prim, member } => Finding::Count {
                from: self.scalar(*from),
                prim: *prim,
                member: member.clone(),
            },
        };
        let instances = def.instances.iter().map(|site| InstanceSite {
            name: site.name.clone(),
            span: self.span(site.span),
        });
        let instances = instances.collect();
        ValueDef {
            how,
            item: def.item.map(|item| self.item(item)),
            span: self.span(def.span),
            instances,
            // Each but the functions the checker makes, of which those
            // made for this package so far.
            funcs: def.funcs - decls - share.synths.start,
            globals: def.globals - share.globals.start,
            table: def.table - share.table.start,
            errors: 0,
        }
    }

    fn check(&mut self, def: &CheckDef) -> CheckDef {
        let check = match &def.check {
            Check::Distinct { members, from } => {
                let members = members.iter().map(|(name, span, value)| {
                    let value = value.iter().map(|s| self.scalar(*s)).collect();
                    (name.clone(), self.span(*span), value)
                });
                Check::Distinct {
                    members: members.collect(),
                    from: *from,
                }
            }
            Check::Empty {
                count,
                default,
                span,
            } => Check::Empty {
                count: self.scalar(*count),
                default: *default,
                span: self.span(*span),
            },
        };
        CheckDef { check, errors: 0 }
    }

    /// `event`, numbered as the artifact's, unless it is of the return
    /// area, which is the program's.
    fn event(&mut self, event: Event, share: &Share) -> Option<Event> {
        Some(match event {
            Event::Place(id) if !share.data.contains(&(id.0 as usize)) => return None,
            Event::Place(id) => Event::Place(DataId(id.0 - share.data.start as u32)),
            Event::Find(id) => Event::Find(ValueId(id.0 - share.values.start as u32)),
            Event::Check(index) => Event::Check(index - share.checks.start),
        })
    }
}

/// Gives each function, global and symbol that `body` names what `f`
/// makes of it.
pub(super) fn renumber(body: &mut [Stmt], f: &mut impl FnMut(Ref) -> Ref) {
    for stmt in body {
        match stmt {
            Stmt::SetLocal(_, value) | Stmt::Drop(value) => renumber_expr(value, f),
            Stmt::SetGlobal(id, value) => {
                if let Ref::Global(to) = f(Ref::Global(*id)) {
                    *id = to;
                }
                renumber_expr(value, f);
            }
            Stmt::Store { addr, value, .. } => {
                renumber_expr(addr, f);
                renumber_expr(value, f);
            }
            Stmt::MemoryFill {
                dst: a,
                value: b,
                len: c,
            }
            | Stmt::MemoryCopy {
                dst: a,
                src: b,
                len: c,
            } => [a, b, c].into_iter().for_each(|e| renumber_expr(e, f)),
            Stmt::Call { func, args, .. } => {
                if let Ref::Func(to) = f(Ref::Func(*func)) {
                    *func = to;
                }
                args.iter_mut().for_each(|arg| renumber_expr(arg, f));
            }
            Stmt::CallIndirect { args, index, .. } => {
                args.iter_mut().for_each(|arg| renumber_expr(arg, f));
                renumber_expr(index, f);
            }
            Stmt::Block(body) | Stmt::Loop(body) => renumber(body, f),
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                renumber_expr(cond, f);
                renumber(then_body, f);
                renumber(else_body, f);
            }
            Stmt::BrIf(_, cond) => renumber_expr(cond, f),
            Stmt::Return(values) => values.iter_mut().for_each(|e| renumber_expr(e, f)),
            Stmt::Br(_) | Stmt::Unreachable => {}
        }
    }
}

fn renumber_expr(expr: &mut Expr, f: &mut impl FnMut(Ref) -> Ref) {
    match expr {
        Expr::Const(_) | Expr::Local(_) | Expr::MemorySize => {}
        Expr::Global(id) => {
            if let Ref::Global(to) = f(Ref::Global(*id)) {
                *id = to;
            }
        }
        Expr::Symbol(_, symbol) => {
            if let Ref::Symbol(to) = f(Ref::Symbol(*symbol)) {
                *symbol = to;
            }
        }
        Expr::Unary(_, _, x) | Expr::Load { addr: x, .. } | Expr::MemoryGrow(x) => {
            renumber_expr(x, f);
        }
        Expr::Binary(_, _, a, b) => {
            renumber_expr(a, f);
            renumber_expr(b, f);
        }
        Expr::Call(func, args) => {
            if let Ref::Func(to) = f(Ref::Func(*func)) {
                *func = to;
            }
            args.iter_mut().for_each(|arg| renumber_expr(arg, f));
        }
        Expr::CallIndirect { args, index, .. } => {
            args.iter_mut().for_each(|arg| renumber_expr(arg, f));
            renumber_expr(index, f);
        }
        Expr::If {
            cond,
            then_expr,
            else_expr,
            ..
        } => [cond, then_expr, else_expr]
            .into_iter()
            .for_each(|e| renumber_expr(e, f)),
        Expr::Seq(body, value) => {
            renumber(body, f);
            renumber_expr(value, f);
        }
    }
}

/// The module that `artifacts` make, each package's after those it
/// depends on, linked as `settings` say: those the files of the program
/// have, which [`super::check`] makes the same module of. Or the errors of
/// linking them, each in the file of [`Artifact::linked_files`] that its
/// [`FileId`] is minted from the index of.
pub fn link(artifacts: &[Artifact], settings: &Settings) -> Result<ir::Module, Vec<TypeError>> {
    let artifacts: Vec<&Artifact> = artifacts.iter().collect();
    link_refs(&artifacts, settings)
}

/// Links `artifacts`, as [`link`] does, wherever each is kept.
pub fn link_refs(
    artifacts: &[&Artifact],
    settings: &Settings,
) -> Result<ir::Module, Vec<TypeError>> {
    let mut names = FxHashMap::default();
    for (index, artifact) in artifacts.iter().enumerate() {
        names.entry(artifact.name.clone()).or_insert(index);
    }
    let mut packages = Vec::new();
    for (index, artifact) in artifacts.iter().enumerate() {
        let mut used = Vec::new();
        for name in &artifact.uses {
            match names.get(name) {
                Some(at) if *at < index => used.push(*at),
                _ => {
                    let kind = TypeErrorKind::Unlinked {
                        artifact: artifact.name.clone(),
                        package: name.clone(),
                    };
                    return Err(vec![TypeError::nowhere(kind)]);
                }
            }
        }
        packages.push(used);
    }
    // The return area is placed before what any package places.
    let passed = artifacts.iter().map(|a| a.passed).max().unwrap_or(0);
    let placed_area = passed > 0;
    let imported: usize = artifacts.iter().map(|a| a.imports.len()).sum();
    let defined: usize = artifacts.iter().map(|a| a.defined).sum();
    let (mut bases, mut files) = (Vec::new(), 0);
    let mut at = Base {
        defined: imported,
        synths: imported + defined,
        data: usize::from(placed_area),
        ..Base::default()
    };
    for artifact in artifacts {
        at.defines = artifact.defined;
        bases.push((at.clone(), files));
        at.imports += artifact.imports.len();
        at.defined += artifact.defined;
        at.synths += artifact.funcs.len() - artifact.defined;
        at.globals += artifact.globals.len();
        at.table += artifact.table.len();
        at.data += artifact.data.len();
        at.values += artifact.values.len();
        at.checks += artifact.checks.len();
        at.items += artifact.items;
        files += artifact.files.len();
    }
    let mut program = Linked::default();
    if placed_area {
        let area = settings.return_area.unwrap_or(passed);
        program.data.push(DataDef {
            bytes: Vec::new(),
            fills: Vec::new(),
            align: RETURN_AREA_ALIGN,
            count: Scalar::Known(Const::I32(1)),
            how: Placing::Room(area.into()),
        });
        program.events.push(Event::Place(DataId(0)));
    }
    let (mut funcs, mut synths, mut start) = (Vec::new(), Vec::new(), None);
    for (index, artifact) in artifacts.iter().enumerate() {
        let join = Join {
            artifact,
            bases: &bases,
            package: index,
            packages: &packages[index],
        };
        program.imports.extend(artifact.imports.iter().cloned());
        for (i, func) in artifact.funcs.iter().enumerate() {
            let mut func = func.clone();
            join.renumber_stmts(&mut func.body);
            match i < artifact.defined {
                true => funcs.push(func),
                false => synths.push(func),
            }
        }
        program.globals.extend(artifact.globals.iter().cloned());
        let inits = artifact.inits.iter().map(|init| join.scalar(*init));
        program.inits.extend(inits);
        let table = artifact.table.iter().map(|id| join.func(*id));
        program.table.extend(table);
        let data = artifact.data.iter().map(|def| join.data(def));
        program.data.extend(data);
        let values = artifact.values.iter().map(|def| join.value(def));
        program.values.extend(values);
        let checks = artifact.checks.iter().map(|def| join.check(def));
        program.checks.extend(checks);
        let events = artifact.events.iter().map(|event| join.event(*event));
        program.events.extend(events);
        start = start.or(artifact.start.map(|id| join.func(id)));
    }
    funcs.extend(synths);
    let max_bytes = settings
        .max_pages
        .map(|pages| pages.saturating_mul(PAGE_SIZE));
    let max_addr = u64::from(u32::MAX);
    let data_limit = max_bytes.map_or(max_addr, |bytes| bytes.min(max_addr));
    let fuel_limit = settings.fuel.unwrap_or(DEFAULT_FUEL);
    let mut link = Linking::new(settings, data_limit, fuel_limit);
    link.data = program.data;
    link.values = program.values;
    link.checks = program.checks;
    link.events = program.events;
    let lowered = Lowered {
        imports: &program.imports,
        funcs: &funcs,
        globals: &program.globals,
        inits: &program.inits,
        table: &program.table,
    };
    let mut errors = Vec::new();
    link.link(&lowered, &mut errors);
    errors.extend(link.data_error().map(TypeError::nowhere));
    if errors.is_empty() {
        errors.extend(link.place_late_literals(&lowered).map(TypeError::nowhere));
    }
    if !errors.is_empty() {
        return Err(errors);
    }
    // The start function is called by the `run` that the world exports.
    if let Some(start) = start {
        funcs.push(run_export(start));
    }
    let library = settings.world.is_none();
    let globals = (program.globals, &program.inits[..]);
    Ok(link.module(
        program.imports,
        funcs,
        globals,
        program.table,
        settings,
        library,
    ))
}

/// The function that the `run` the world exports is, which calls `start`
/// and returns the `ok` of its `result`: a program that fails exits with a
/// status.
pub(super) fn run_export(start: FuncId) -> ir::Func {
    ir::Func {
        name: RUN_EXPORT.to_string(),
        exports: vec![RUN_EXPORT.to_string()],
        params: Vec::new(),
        results: vec![ValType::I32],
        locals: Vec::new(),
        body: vec![
            Stmt::Call {
                func: start,
                args: Vec::new(),
                dests: Vec::new(),
            },
            Stmt::Return(vec![Expr::Const(Const::I32(0))]),
        ],
    }
}

impl Join<'_> {
    /// Where what is of `kind` at `index` of package `package` is in the
    /// program.
    fn place(&self, package: usize, kind: Kind, index: u32) -> u32 {
        let base = &self.bases[package].0;
        let index = index as usize;
        (match kind {
            Kind::Import => base.imports + index,
            Kind::Func if index < base.defines => base.defined + index,
            Kind::Func => base.synths + index - base.defines,
            Kind::Global => base.globals + index,
            Kind::Data => base.data + index,
            Kind::Value => base.values + index,
            Kind::Item => base.items + index,
        }) as u32
    }

    /// What `foreign`, which the artifact names, is in the program.
    fn foreign(&self, foreign: &Foreign) -> u32 {
        match foreign.package {
            RETURN_AREA => 0,
            package => {
                let package = self.packages[package as usize];
                self.place(package, foreign.kind, foreign.index)
            }
        }
    }

    fn func(&self, id: FuncId) -> FuncId {
        let a = self.artifact;
        let index = id.0 as usize;
        let own = a.imports.len();
        FuncId(match index {
            _ if index < own => self.place(self.package, Kind::Import, index as u32),
            _ if index < own + a.funcs.len() => {
                self.place(self.package, Kind::Func, (index - own) as u32)
            }
            _ => self.foreign(&a.foreign.funcs[index - own - a.funcs.len()]),
        })
    }

    fn global(&self, id: GlobalId) -> GlobalId {
        let own = self.artifact.globals.len() as u32;
        GlobalId(match id.0 < own {
            true => self.place(self.package, Kind::Global, id.0),
            false => self.foreign(&self.artifact.foreign.globals[(id.0 - own) as usize]),
        })
    }

    fn data_id(&self, id: DataId) -> DataId {
        let own = self.artifact.data.len() as u32;
        DataId(match id.0 < own {
            true => self.place(self.package, Kind::Data, id.0),
            false => self.foreign(&self.artifact.foreign.data[(id.0 - own) as usize]),
        })
    }

    fn value_id(&self, id: ValueId) -> ValueId {
        let own = self.artifact.values.len() as u32;
        ValueId(match id.0 < own {
            true => self.place(self.package, Kind::Value, id.0),
            false => self.foreign(&self.artifact.foreign.values[(id.0 - own) as usize]),
        })
    }

    fn symbol(&self, symbol: Symbol) -> Symbol {
        match symbol {
            Symbol::Data(id, offset) => Symbol::Data(self.data_id(id), offset),
            Symbol::Value(id, index) => Symbol::Value(self.value_id(id), index),
            Symbol::Func(id) => Symbol::Func(self.func(id)),
        }
    }

    fn scalar(&self, scalar: Scalar) -> Scalar {
        match scalar {
            Scalar::Known(c) => Scalar::Known(c),
            Scalar::Linked(ty, symbol) => Scalar::Linked(ty, self.symbol(symbol)),
        }
    }

    fn span(&self, span: Span) -> Span {
        let files = self.bases[self.package].1;
        Span {
            file: FileId::minted(files + span.file.index()),
            ..span
        }
    }

    fn item(&self, item: usize) -> usize {
        let own = self.artifact.items;
        match item < own {
            true => self.place(self.package, Kind::Item, item as u32) as usize,
            false => self.foreign(&self.artifact.foreign.items[item - own]) as usize,
        }
    }

    fn renumber_stmts(&self, body: &mut [Stmt]) {
        renumber(body, &mut |r| match r {
            Ref::Func(id) => Ref::Func(self.func(id)),
            Ref::Global(id) => Ref::Global(self.global(id)),
            Ref::Symbol(symbol) => Ref::Symbol(self.symbol(symbol)),
        });
    }

    fn data(&self, def: &DataDef) -> DataDef {
        let fills = def.fills.iter().map(|fill| Fill {
            offset: fill.offset,
            cells: fill.cells.clone(),
            scalars: fill.scalars.iter().map(|s| self.scalar(*s)).collect(),
        });
        DataDef {
            bytes: def.bytes.clone(),
            fills: fills.collect(),
            align: def.align,
            count: self.scalar(def.count),
            how: def.how.clone(),
        }
    }

    fn value(&self, def: &ValueDef) -> ValueDef {
        let base = &self.bases[self.package].0;
        let how = match &def.how {
            Finding::Fold(thunk) => {
                let mut thunk = thunk.clone();
                self.renumber_stmts(&mut thunk.body);
                Finding::Fold(thunk)
            }
            Finding::Run { thunk, reached } => {
                let mut thunk = thunk.clone();
                self.renumber_stmts(&mut thunk.body);
                let reached = reached.iter().map(|id| self.func(*id)).collect();
                Finding::Run { thunk, reached }
            }
            Finding::Count { from, prim, member } => Finding::Count {
                from: self.scalar(*from),
                prim: *prim,
                member: member.clone(),
            },
        };
        let instances = def.instances.iter().map(|site| InstanceSite {
            name: site.name.clone(),
            span: self.span(site.span),
        });
        ValueDef {
            how,
            item: def.item.map(|item| self.item(item)),
            span: self.span(def.span),
            instances: instances.collect(),
            funcs: base.synths + def.funcs,
            globals: base.globals + def.globals,
            table: base.table + def.table,
            errors: 0,
        }
    }

    fn check(&self, def: &CheckDef) -> CheckDef {
        let check = match &def.check {
            Check::Distinct { members, from } => {
                let members = members.iter().map(|(name, span, value)| {
                    let value = value.iter().map(|s| self.scalar(*s)).collect();
                    (name.clone(), self.span(*span), value)
                });
                Check::Distinct {
                    members: members.collect(),
                    from: *from,
                }
            }
            Check::Empty {
                count,
                default,
                span,
            } => Check::Empty {
                count: self.scalar(*count),
                default: *default,
                span: self.span(*span),
            },
        };
        CheckDef { check, errors: 0 }
    }

    fn event(&self, event: Event) -> Event {
        let base = &self.bases[self.package].0;
        match event {
            Event::Place(id) => Event::Place(DataId(base.data as u32 + id.0)),
            Event::Find(id) => Event::Find(ValueId(base.values as u32 + id.0)),
            Event::Check(index) => Event::Check(base.checks + index),
        }
    }
}

impl Artifact {
    /// The files that the errors of linking `artifacts` are in, each at the
    /// index its [`FileId`] is minted from.
    pub fn linked_files(artifacts: &[Artifact]) -> Vec<String> {
        artifacts
            .iter()
            .flat_map(|a| a.files.iter().cloned())
            .collect()
    }

    /// The names of the packages it uses, whose artifacts are linked
    /// before it.
    pub fn uses(&self) -> &[String] {
        &self.uses
    }

    /// The interface of the package: what a program that uses it is
    /// checked against.
    pub fn interface(&self) -> &Interface {
        &self.interface
    }

    /// The artifact as bytes, which [`Self::decode`] reads.
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer::default();
        w.bytes.extend_from_slice(MAGIC);
        VERSION.encode(&mut w);
        self.name.encode(&mut w);
        self.uses.encode(&mut w);
        self.files.encode(&mut w);
        self.items.encode(&mut w);
        self.imports.encode(&mut w);
        self.funcs.encode(&mut w);
        self.defined.encode(&mut w);
        self.globals.encode(&mut w);
        self.inits.encode(&mut w);
        self.table.encode(&mut w);
        self.data.encode(&mut w);
        self.values.encode(&mut w);
        self.checks.encode(&mut w);
        self.events.encode(&mut w);
        self.foreign.encode(&mut w);
        self.start.encode(&mut w);
        self.passed.encode(&mut w);
        self.interface.encode(&mut w);
        w.bytes
    }

    /// The artifact that `bytes` are, as [`Self::encode`] wrote them.
    pub fn decode(bytes: &[u8]) -> Result<Self, DecodeError> {
        let mut r = Reader::new(bytes);
        if !r.starts_with(MAGIC) {
            return Err(DecodeError("these bytes are no artifact".to_string()));
        }
        let version = u32::decode(&mut r)?;
        if version != VERSION {
            let why = format!("the artifact is of version {version}, and this is {VERSION}");
            return Err(DecodeError(why));
        }
        let artifact = Self {
            name: Decode::decode(&mut r)?,
            uses: Decode::decode(&mut r)?,
            files: Decode::decode(&mut r)?,
            items: Decode::decode(&mut r)?,
            imports: Decode::decode(&mut r)?,
            funcs: Decode::decode(&mut r)?,
            defined: Decode::decode(&mut r)?,
            globals: Decode::decode(&mut r)?,
            inits: Decode::decode(&mut r)?,
            table: Decode::decode(&mut r)?,
            data: Decode::decode(&mut r)?,
            values: Decode::decode(&mut r)?,
            checks: Decode::decode(&mut r)?,
            events: Decode::decode(&mut r)?,
            foreign: Decode::decode(&mut r)?,
            start: Decode::decode(&mut r)?,
            passed: Decode::decode(&mut r)?,
            interface: Decode::decode(&mut r)?,
        };
        match r.done() {
            true => Ok(artifact),
            false => Err(DecodeError(
                "the artifact has bytes after its end".to_string(),
            )),
        }
    }
}

lists!(
    ir::Import,
    ir::Func,
    ir::Global,
    ir::Local,
    Stmt,
    Expr,
    ValType,
    LocalId,
    FuncId,
    Scalar,
    DataDef,
    Fill,
    Cell,
    Holds,
    ValueDef,
    InstanceSite,
    CheckDef,
    Event,
    Foreign,
    (String, Span, Vec<Scalar>),
);

impl Encode for FxHashSet<FuncId> {
    fn encode(&self, w: &mut Writer) {
        // In order, so that one set is always the same bytes.
        let mut ids: Vec<_> = self.iter().copied().collect();
        ids.sort_by_key(|id| id.0);
        ids.encode(w);
    }
}

impl Decode for FxHashSet<FuncId> {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Vec::<FuncId>::decode(r)?.into_iter().collect())
    }
}

impl Encode for ValType {
    fn encode(&self, w: &mut Writer) {
        w.tag(match self {
            ValType::I32 => 0,
            ValType::I64 => 1,
            ValType::F32 => 2,
            ValType::F64 => 3,
        });
    }
}

impl Decode for ValType {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => ValType::I32,
            1 => ValType::I64,
            2 => ValType::F32,
            3 => ValType::F64,
            tag => return Err(bad("type", tag)),
        })
    }
}

impl Encode for Const {
    fn encode(&self, w: &mut Writer) {
        match self {
            Const::I32(x) => {
                w.tag(0);
                x.encode(w);
            }
            Const::I64(x) => {
                w.tag(1);
                x.encode(w);
            }
            // A float as its bits, which keep a NaN's.
            Const::F32(x) => {
                w.tag(2);
                x.to_bits().encode(w);
            }
            Const::F64(x) => {
                w.tag(3);
                x.to_bits().encode(w);
            }
        }
    }
}

impl Decode for Const {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Const::I32(Decode::decode(r)?),
            1 => Const::I64(Decode::decode(r)?),
            2 => Const::F32(f32::from_bits(Decode::decode(r)?)),
            3 => Const::F64(f64::from_bits(Decode::decode(r)?)),
            tag => return Err(bad("constant", tag)),
        })
    }
}

ids!(FuncId, GlobalId, LocalId, DataId, ValueId);

impl Encode for Symbol {
    fn encode(&self, w: &mut Writer) {
        match self {
            Symbol::Data(id, offset) => {
                w.tag(0);
                id.encode(w);
                offset.encode(w);
            }
            Symbol::Value(id, index) => {
                w.tag(1);
                id.encode(w);
                index.encode(w);
            }
            Symbol::Func(id) => {
                w.tag(2);
                id.encode(w);
            }
        }
    }
}

impl Decode for Symbol {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Symbol::Data(Decode::decode(r)?, Decode::decode(r)?),
            1 => Symbol::Value(Decode::decode(r)?, Decode::decode(r)?),
            2 => Symbol::Func(Decode::decode(r)?),
            tag => return Err(bad("symbol", tag)),
        })
    }
}

impl Encode for UnOp {
    fn encode(&self, w: &mut Writer) {
        let (tag, ty) = match self {
            UnOp::Eqz => (0, None),
            UnOp::Clz => (1, None),
            UnOp::Ctz => (2, None),
            UnOp::Neg => (3, None),
            UnOp::Extend8S => (4, None),
            UnOp::Extend16S => (5, None),
            UnOp::Wrap => (6, None),
            UnOp::ExtendS => (7, None),
            UnOp::ExtendU => (8, None),
            UnOp::TruncSatS(ty) => (9, Some(ty)),
            UnOp::TruncSatU(ty) => (10, Some(ty)),
            UnOp::ConvertS(ty) => (11, Some(ty)),
            UnOp::ConvertU(ty) => (12, Some(ty)),
            UnOp::Demote => (13, None),
            UnOp::Promote => (14, None),
            UnOp::Reinterpret => (15, None),
        };
        w.tag(tag);
        if let Some(ty) = ty {
            ty.encode(w);
        }
    }
}

impl Decode for UnOp {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => UnOp::Eqz,
            1 => UnOp::Clz,
            2 => UnOp::Ctz,
            3 => UnOp::Neg,
            4 => UnOp::Extend8S,
            5 => UnOp::Extend16S,
            6 => UnOp::Wrap,
            7 => UnOp::ExtendS,
            8 => UnOp::ExtendU,
            9 => UnOp::TruncSatS(Decode::decode(r)?),
            10 => UnOp::TruncSatU(Decode::decode(r)?),
            11 => UnOp::ConvertS(Decode::decode(r)?),
            12 => UnOp::ConvertU(Decode::decode(r)?),
            13 => UnOp::Demote,
            14 => UnOp::Promote,
            15 => UnOp::Reinterpret,
            tag => return Err(bad("unary operator", tag)),
        })
    }
}

impl Encode for BinOp {
    fn encode(&self, w: &mut Writer) {
        let tag = BIN_OPS.iter().position(|op| op == self);
        w.tag(tag.expect("every operator has a tag") as u8);
    }
}

impl Decode for BinOp {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let tag = r.tag()?;
        let op = BIN_OPS.get(tag as usize).copied();
        op.ok_or_else(|| bad("binary operator", tag))
    }
}

impl Encode for LoadOp {
    fn encode(&self, w: &mut Writer) {
        w.tag(match self {
            LoadOp::Load => 0,
            LoadOp::Load8S => 1,
            LoadOp::Load8U => 2,
            LoadOp::Load16S => 3,
            LoadOp::Load16U => 4,
        });
    }
}

impl Decode for LoadOp {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => LoadOp::Load,
            1 => LoadOp::Load8S,
            2 => LoadOp::Load8U,
            3 => LoadOp::Load16S,
            4 => LoadOp::Load16U,
            tag => return Err(bad("load", tag)),
        })
    }
}

impl Encode for StoreOp {
    fn encode(&self, w: &mut Writer) {
        w.tag(match self {
            StoreOp::Store => 0,
            StoreOp::Store8 => 1,
            StoreOp::Store16 => 2,
        });
    }
}

impl Decode for StoreOp {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => StoreOp::Store,
            1 => StoreOp::Store8,
            2 => StoreOp::Store16,
            tag => return Err(bad("store", tag)),
        })
    }
}

impl Encode for FuncType {
    fn encode(&self, w: &mut Writer) {
        self.params.encode(w);
        self.results.encode(w);
    }
}

impl Decode for FuncType {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(FuncType {
            params: Decode::decode(r)?,
            results: Decode::decode(r)?,
        })
    }
}

impl Encode for Stmt {
    fn encode(&self, w: &mut Writer) {
        match self {
            Stmt::SetLocal(local, value) => {
                w.tag(0);
                local.encode(w);
                value.encode(w);
            }
            Stmt::SetGlobal(global, value) => {
                w.tag(1);
                global.encode(w);
                value.encode(w);
            }
            Stmt::Store {
                ty,
                op,
                offset,
                addr,
                value,
            } => {
                w.tag(2);
                ty.encode(w);
                op.encode(w);
                offset.encode(w);
                addr.encode(w);
                value.encode(w);
            }
            Stmt::Drop(value) => {
                w.tag(3);
                value.encode(w);
            }
            Stmt::MemoryFill { dst, value, len } => {
                w.tag(4);
                dst.encode(w);
                value.encode(w);
                len.encode(w);
            }
            Stmt::MemoryCopy { dst, src, len } => {
                w.tag(5);
                dst.encode(w);
                src.encode(w);
                len.encode(w);
            }
            Stmt::Call { func, args, dests } => {
                w.tag(6);
                func.encode(w);
                args.encode(w);
                dests.encode(w);
            }
            Stmt::CallIndirect {
                ty,
                args,
                index,
                dests,
            } => {
                w.tag(7);
                ty.encode(w);
                args.encode(w);
                index.encode(w);
                dests.encode(w);
            }
            Stmt::Block(body) => {
                w.tag(8);
                body.encode(w);
            }
            Stmt::Loop(body) => {
                w.tag(9);
                body.encode(w);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                w.tag(10);
                cond.encode(w);
                then_body.encode(w);
                else_body.encode(w);
            }
            Stmt::Br(depth) => {
                w.tag(11);
                depth.encode(w);
            }
            Stmt::BrIf(depth, cond) => {
                w.tag(12);
                depth.encode(w);
                cond.encode(w);
            }
            Stmt::Return(values) => {
                w.tag(13);
                values.encode(w);
            }
            Stmt::Unreachable => w.tag(14),
        }
    }
}

impl Decode for Stmt {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Stmt::SetLocal(Decode::decode(r)?, Decode::decode(r)?),
            1 => Stmt::SetGlobal(Decode::decode(r)?, Decode::decode(r)?),
            2 => Stmt::Store {
                ty: Decode::decode(r)?,
                op: Decode::decode(r)?,
                offset: Decode::decode(r)?,
                addr: Decode::decode(r)?,
                value: Decode::decode(r)?,
            },
            3 => Stmt::Drop(Decode::decode(r)?),
            4 => Stmt::MemoryFill {
                dst: Decode::decode(r)?,
                value: Decode::decode(r)?,
                len: Decode::decode(r)?,
            },
            5 => Stmt::MemoryCopy {
                dst: Decode::decode(r)?,
                src: Decode::decode(r)?,
                len: Decode::decode(r)?,
            },
            6 => Stmt::Call {
                func: Decode::decode(r)?,
                args: Decode::decode(r)?,
                dests: Decode::decode(r)?,
            },
            7 => Stmt::CallIndirect {
                ty: Decode::decode(r)?,
                args: Decode::decode(r)?,
                index: Decode::decode(r)?,
                dests: Decode::decode(r)?,
            },
            8 => Stmt::Block(Decode::decode(r)?),
            9 => Stmt::Loop(Decode::decode(r)?),
            10 => Stmt::If {
                cond: Decode::decode(r)?,
                then_body: Decode::decode(r)?,
                else_body: Decode::decode(r)?,
            },
            11 => Stmt::Br(Decode::decode(r)?),
            12 => Stmt::BrIf(Decode::decode(r)?, Decode::decode(r)?),
            13 => Stmt::Return(Decode::decode(r)?),
            14 => Stmt::Unreachable,
            tag => return Err(bad("statement", tag)),
        })
    }
}

impl Encode for Expr {
    fn encode(&self, w: &mut Writer) {
        match self {
            Expr::Const(c) => {
                w.tag(0);
                c.encode(w);
            }
            Expr::Local(local) => {
                w.tag(1);
                local.encode(w);
            }
            Expr::Global(global) => {
                w.tag(2);
                global.encode(w);
            }
            Expr::Unary(ty, op, x) => {
                w.tag(3);
                ty.encode(w);
                op.encode(w);
                x.encode(w);
            }
            Expr::Binary(ty, op, a, b) => {
                w.tag(4);
                ty.encode(w);
                op.encode(w);
                a.encode(w);
                b.encode(w);
            }
            Expr::Call(func, args) => {
                w.tag(5);
                func.encode(w);
                args.encode(w);
            }
            Expr::CallIndirect { ty, args, index } => {
                w.tag(6);
                ty.encode(w);
                args.encode(w);
                index.encode(w);
            }
            Expr::Load {
                ty,
                op,
                offset,
                addr,
            } => {
                w.tag(7);
                ty.encode(w);
                op.encode(w);
                offset.encode(w);
                addr.encode(w);
            }
            Expr::MemorySize => w.tag(8),
            Expr::MemoryGrow(pages) => {
                w.tag(9);
                pages.encode(w);
            }
            Expr::If {
                ty,
                cond,
                then_expr,
                else_expr,
            } => {
                w.tag(10);
                ty.encode(w);
                cond.encode(w);
                then_expr.encode(w);
                else_expr.encode(w);
            }
            Expr::Seq(body, value) => {
                w.tag(11);
                body.encode(w);
                value.encode(w);
            }
            Expr::Symbol(ty, symbol) => {
                w.tag(12);
                ty.encode(w);
                symbol.encode(w);
            }
        }
    }
}

impl Decode for Expr {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Expr::Const(Decode::decode(r)?),
            1 => Expr::Local(Decode::decode(r)?),
            2 => Expr::Global(Decode::decode(r)?),
            3 => Expr::Unary(Decode::decode(r)?, Decode::decode(r)?, Decode::decode(r)?),
            4 => Expr::Binary(
                Decode::decode(r)?,
                Decode::decode(r)?,
                Decode::decode(r)?,
                Decode::decode(r)?,
            ),
            5 => Expr::Call(Decode::decode(r)?, Decode::decode(r)?),
            6 => Expr::CallIndirect {
                ty: Decode::decode(r)?,
                args: Decode::decode(r)?,
                index: Decode::decode(r)?,
            },
            7 => Expr::Load {
                ty: Decode::decode(r)?,
                op: Decode::decode(r)?,
                offset: Decode::decode(r)?,
                addr: Decode::decode(r)?,
            },
            8 => Expr::MemorySize,
            9 => Expr::MemoryGrow(Decode::decode(r)?),
            10 => Expr::If {
                ty: Decode::decode(r)?,
                cond: Decode::decode(r)?,
                then_expr: Decode::decode(r)?,
                else_expr: Decode::decode(r)?,
            },
            11 => Expr::Seq(Decode::decode(r)?, Decode::decode(r)?),
            12 => Expr::Symbol(Decode::decode(r)?, Decode::decode(r)?),
            tag => return Err(bad("expression", tag)),
        })
    }
}

impl Encode for ir::Local {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.ty.encode(w);
    }
}

impl Decode for ir::Local {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(ir::Local {
            name: Decode::decode(r)?,
            ty: Decode::decode(r)?,
        })
    }
}

impl Encode for ir::Func {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.exports.encode(w);
        self.params.encode(w);
        self.results.encode(w);
        self.locals.encode(w);
        self.body.encode(w);
    }
}

impl Decode for ir::Func {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(ir::Func {
            name: Decode::decode(r)?,
            exports: Decode::decode(r)?,
            params: Decode::decode(r)?,
            results: Decode::decode(r)?,
            locals: Decode::decode(r)?,
            body: Decode::decode(r)?,
        })
    }
}

impl Encode for ir::Import {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.module.encode(w);
        self.field.encode(w);
        self.params.encode(w);
        self.results.encode(w);
    }
}

impl Decode for ir::Import {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(ir::Import {
            name: Decode::decode(r)?,
            module: Decode::decode(r)?,
            field: Decode::decode(r)?,
            params: Decode::decode(r)?,
            results: Decode::decode(r)?,
        })
    }
}

impl Encode for ir::Global {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.ty.encode(w);
        self.mutable.encode(w);
        self.init.encode(w);
        self.exports.encode(w);
    }
}

impl Decode for ir::Global {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(ir::Global {
            name: Decode::decode(r)?,
            ty: Decode::decode(r)?,
            mutable: Decode::decode(r)?,
            init: Decode::decode(r)?,
            exports: Decode::decode(r)?,
        })
    }
}

impl Encode for Scalar {
    fn encode(&self, w: &mut Writer) {
        match self {
            Scalar::Known(c) => {
                w.tag(0);
                c.encode(w);
            }
            Scalar::Linked(ty, symbol) => {
                w.tag(1);
                ty.encode(w);
                symbol.encode(w);
            }
        }
    }
}

impl Decode for Scalar {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Scalar::Known(Decode::decode(r)?),
            1 => Scalar::Linked(Decode::decode(r)?, Decode::decode(r)?),
            tag => return Err(bad("scalar", tag)),
        })
    }
}

impl Encode for Leaf {
    fn encode(&self, w: &mut Writer) {
        self.index.encode(w);
        self.ty.encode(w);
    }
}

impl Decode for Leaf {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Leaf {
            index: Decode::decode(r)?,
            ty: Decode::decode(r)?,
        })
    }
}

impl Encode for Holds {
    fn encode(&self, w: &mut Writer) {
        self.tag.encode(w);
        self.variant.encode(w);
    }
}

impl Decode for Holds {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Holds {
            tag: Decode::decode(r)?,
            variant: Decode::decode(r)?,
        })
    }
}

impl Encode for Cell {
    fn encode(&self, w: &mut Writer) {
        self.offset.encode(w);
        self.leaf.encode(w);
        self.ty.encode(w);
        self.load.encode(w);
        self.store.encode(w);
        self.bool.encode(w);
        self.when.encode(w);
    }
}

impl Decode for Cell {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Cell {
            offset: Decode::decode(r)?,
            leaf: Decode::decode(r)?,
            ty: Decode::decode(r)?,
            load: Decode::decode(r)?,
            store: Decode::decode(r)?,
            bool: Decode::decode(r)?,
            when: Decode::decode(r)?,
        })
    }
}

impl Encode for Fill {
    fn encode(&self, w: &mut Writer) {
        self.offset.encode(w);
        self.cells.encode(w);
        self.scalars.encode(w);
    }
}

impl Decode for Fill {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Fill {
            offset: Decode::decode(r)?,
            cells: Decode::decode(r)?,
            scalars: Decode::decode(r)?,
        })
    }
}

impl Encode for Placing {
    fn encode(&self, w: &mut Writer) {
        match self {
            Placing::Own => w.tag(0),
            Placing::Copied => w.tag(1),
            Placing::Shared => w.tag(2),
            Placing::Room(size) => {
                w.tag(3);
                size.encode(w);
            }
        }
    }
}

impl Decode for Placing {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Placing::Own,
            1 => Placing::Copied,
            2 => Placing::Shared,
            3 => Placing::Room(Decode::decode(r)?),
            tag => return Err(bad("placing", tag)),
        })
    }
}

impl Encode for DataDef {
    fn encode(&self, w: &mut Writer) {
        self.bytes.encode(w);
        self.fills.encode(w);
        self.align.encode(w);
        self.count.encode(w);
        self.how.encode(w);
    }
}

impl Decode for DataDef {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(DataDef {
            bytes: Decode::decode(r)?,
            fills: Decode::decode(r)?,
            align: Decode::decode(r)?,
            count: Decode::decode(r)?,
            how: Decode::decode(r)?,
        })
    }
}

impl Encode for Prim {
    fn encode(&self, w: &mut Writer) {
        let tag = PRIMS.iter().position(|prim| prim == self);
        w.tag(tag.expect("every primitive has a tag") as u8);
    }
}

impl Decode for Prim {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let tag = r.tag()?;
        PRIMS
            .get(tag as usize)
            .copied()
            .ok_or_else(|| bad("primitive", tag))
    }
}

impl Encode for Finding {
    fn encode(&self, w: &mut Writer) {
        match self {
            Finding::Fold(thunk) => {
                w.tag(0);
                thunk.encode(w);
            }
            Finding::Run { thunk, reached } => {
                w.tag(1);
                thunk.encode(w);
                reached.encode(w);
            }
            Finding::Count { from, prim, member } => {
                w.tag(2);
                from.encode(w);
                prim.encode(w);
                member.encode(w);
            }
        }
    }
}

impl Decode for Finding {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Finding::Fold(Decode::decode(r)?),
            1 => Finding::Run {
                thunk: Decode::decode(r)?,
                reached: Decode::decode(r)?,
            },
            2 => Finding::Count {
                from: Decode::decode(r)?,
                prim: Decode::decode(r)?,
                member: Decode::decode(r)?,
            },
            tag => return Err(bad("finding", tag)),
        })
    }
}

impl Encode for InstanceSite {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.span.encode(w);
    }
}

impl Decode for InstanceSite {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(InstanceSite {
            name: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for ValueDef {
    fn encode(&self, w: &mut Writer) {
        self.how.encode(w);
        self.item.encode(w);
        self.span.encode(w);
        self.instances.encode(w);
        self.funcs.encode(w);
        self.globals.encode(w);
        self.table.encode(w);
    }
}

impl Decode for ValueDef {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(ValueDef {
            how: Decode::decode(r)?,
            item: Decode::decode(r)?,
            span: Decode::decode(r)?,
            instances: Decode::decode(r)?,
            funcs: Decode::decode(r)?,
            globals: Decode::decode(r)?,
            table: Decode::decode(r)?,
            errors: 0,
        })
    }
}

impl Encode for CheckDef {
    fn encode(&self, w: &mut Writer) {
        match &self.check {
            Check::Distinct { members, from } => {
                w.tag(0);
                members.encode(w);
                from.encode(w);
            }
            Check::Empty {
                count,
                default,
                span,
            } => {
                w.tag(1);
                count.encode(w);
                default.encode(w);
                span.encode(w);
            }
        }
    }
}

impl Decode for CheckDef {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        let check = match r.tag()? {
            0 => Check::Distinct {
                members: Decode::decode(r)?,
                from: Decode::decode(r)?,
            },
            1 => Check::Empty {
                count: Decode::decode(r)?,
                default: Decode::decode(r)?,
                span: Decode::decode(r)?,
            },
            tag => return Err(bad("check", tag)),
        };
        Ok(CheckDef { check, errors: 0 })
    }
}

impl Encode for Event {
    fn encode(&self, w: &mut Writer) {
        match self {
            Event::Place(id) => {
                w.tag(0);
                id.encode(w);
            }
            Event::Find(id) => {
                w.tag(1);
                id.encode(w);
            }
            Event::Check(index) => {
                w.tag(2);
                index.encode(w);
            }
        }
    }
}

impl Decode for Event {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Event::Place(Decode::decode(r)?),
            1 => Event::Find(Decode::decode(r)?),
            2 => Event::Check(Decode::decode(r)?),
            tag => return Err(bad("event", tag)),
        })
    }
}

impl Encode for Kind {
    fn encode(&self, w: &mut Writer) {
        w.tag(match self {
            Kind::Import => 0,
            Kind::Func => 1,
            Kind::Global => 2,
            Kind::Data => 3,
            Kind::Value => 4,
            Kind::Item => 5,
        });
    }
}

impl Decode for Kind {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Kind::Import,
            1 => Kind::Func,
            2 => Kind::Global,
            3 => Kind::Data,
            4 => Kind::Value,
            5 => Kind::Item,
            tag => return Err(bad("kind", tag)),
        })
    }
}

impl Encode for Foreign {
    fn encode(&self, w: &mut Writer) {
        self.package.encode(w);
        self.kind.encode(w);
        self.index.encode(w);
    }
}

impl Decode for Foreign {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Foreign {
            package: Decode::decode(r)?,
            kind: Decode::decode(r)?,
            index: Decode::decode(r)?,
        })
    }
}

impl Encode for Foreigns {
    fn encode(&self, w: &mut Writer) {
        self.funcs.encode(w);
        self.globals.encode(w);
        self.data.encode(w);
        self.values.encode(w);
        self.items.encode(w);
    }
}

impl Decode for Foreigns {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Foreigns {
            funcs: Decode::decode(r)?,
            globals: Decode::decode(r)?,
            data: Decode::decode(r)?,
            values: Decode::decode(r)?,
            items: Decode::decode(r)?,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use super::*;
    use crate::load;
    use crate::world::COMMAND;

    /// Files by name, the first the entry point: one named `@name` is the
    /// library of dependency `name`. They are built with the settings, and
    /// a library among them that is compiled already has its artifact.
    struct Files(
        Vec<(&'static str, &'static str)>,
        Settings,
        Vec<(&'static str, Rc<Artifact>)>,
    );

    impl FileManager for Files {
        fn entry_point(&mut self) -> FileId {
            FileId::minted(0)
        }

        fn compiled(&mut self, library: FileId) -> Option<Rc<Artifact>> {
            let name = self.0[library.index()].0;
            let compiled = self.2.iter().find(|(compiled, _)| *compiled == name);
            compiled.map(|(_, artifact)| artifact.clone())
        }

        fn display_name(&mut self, id: FileId) -> String {
            self.0[id.index()].0.to_string()
        }

        fn contents(&mut self, id: FileId) -> String {
            self.0[id.index()].1.to_string()
        }

        fn open(&mut self, _from: FileId, path: &[&str]) -> Option<FileId> {
            self.named(&path.join("."))
        }

        fn open_package(&mut self, _from: FileId, name: &str) -> Option<FileId> {
            self.named(&format!("@{name}"))
        }

        fn settings(&mut self) -> Settings {
            self.1.clone()
        }
    }

    impl Files {
        fn named(&self, name: &str) -> Option<FileId> {
            let index = self.0.iter().position(|f| f.0 == name);
            Some(FileId::minted(index?))
        }
    }

    /// Each error, with the file `file` names its span's in, and the text
    /// it spans there.
    fn shown(errors: &[TypeError], files: &Files, file: impl Fn(FileId) -> String) -> Vec<String> {
        let shown = errors.iter().map(|e| match e.span {
            Some(span) => {
                let name = file(span.file);
                let source = files.0.iter().find(|f| f.0 == name).unwrap().1;
                format!(
                    "{name} {:?}: {}",
                    &source[span.start..span.end],
                    e.message()
                )
            }
            None => e.message(),
        });
        shown.collect()
    }

    /// Each error, in the file of `files` that it is in.
    fn own_errors(errors: &[TypeError], files: &Files) -> Vec<String> {
        shown(errors, files, |id| files.0[id.index()].0.to_string())
    }

    /// The artifacts of `files`, each encoded and decoded.
    fn artifacts_of(files: &mut Files) -> Vec<Artifact> {
        let settings = files.settings();
        let program = load::load(files).unwrap();
        let artifacts = super::super::artifacts(&program, &settings, files);
        let artifacts = artifacts.unwrap_or_else(|e| panic!("{:?}", own_errors(&e, files)));
        let decoded = artifacts.iter().map(|artifact| {
            let bytes = artifact.encode();
            let decoded = Artifact::decode(&bytes).unwrap();
            assert_eq!(&decoded, artifact);
            assert_eq!(decoded.encode(), bytes);
            decoded
        });
        decoded.collect()
    }

    /// The module that checking `files` makes, or its errors: the same as
    /// linking the artifacts of its packages makes, which is asserted.
    fn linked(files: &mut Files) -> Result<ir::Module, Vec<String>> {
        let settings = files.settings();
        let program = load::load(files).unwrap();
        let checked = super::super::check(&program, &settings);
        let checked = checked.map_err(|e| own_errors(&e, files));
        let artifacts = artifacts_of(files);
        let names = Artifact::linked_files(&artifacts);
        let made = link(&artifacts, &settings);
        let made = made.map_err(|e| shown(&e, files, |id| names[id.index()].clone()));
        assert_eq!(made, checked);
        made
    }

    /// A library of no world.
    fn library(files: Vec<(&'static str, &'static str)>) -> Files {
        Files(files, Settings::default(), Vec::new())
    }

    /// A command that runs `main`.
    fn command(files: Vec<(&'static str, &'static str)>) -> Files {
        let settings = Settings {
            world: Some(COMMAND.to_string()),
            start: Some("main".to_string()),
            ..Settings::default()
        };
        Files(files, settings, Vec::new())
    }

    /// The module that compiling `files` package by package makes: each
    /// library alone, and then each package that uses it with the artifact
    /// the library compiled to, in the order they are given. The same as
    /// compiling the whole program at once, which is asserted of the
    /// artifacts and of the module.
    fn separately(files: &mut Files) -> ir::Module {
        let settings = files.settings();
        let whole = artifacts_of(files);
        let mut compiled: Vec<(&'static str, Rc<Artifact>)> = Vec::new();
        for (index, (name, _)) in files.0.iter().enumerate().skip(1).rev() {
            if !name.starts_with('@') {
                continue;
            }
            let mut own = files.0.clone();
            own.swap(0, index);
            let mut alone = Files(own, Settings::default(), compiled.clone());
            let artifact = crate::compile_package(&mut alone);
            let artifact = artifact.unwrap_or_else(|e| panic!("{e:?}"));
            let bytes = artifact.encode();
            let artifact = Artifact::decode(&bytes).unwrap();
            let expected = whole.iter().find(|a| a.name == *name).unwrap();
            // Checking the whole program reaches through the bodies of the
            // functions of other packages, which one compiled alone has
            // nothing of until it is linked: linking reaches through them.
            let unreached = |artifact: &Artifact| {
                let mut artifact = artifact.clone();
                for value in &mut artifact.values {
                    if let Finding::Run { reached, .. } = &mut value.how {
                        reached.clear();
                    }
                }
                artifact
            };
            assert_eq!(
                unreached(&artifact),
                unreached(expected),
                "the artifact of {name} compiled alone"
            );
            compiled.push((name, Rc::new(artifact)));
        }
        let mut with = Files(files.0.clone(), settings.clone(), compiled);
        let module = crate::lower(&mut with).unwrap_or_else(|e| panic!("{e:?}"));
        let program = load::load(files).unwrap();
        assert!(!load::load(&mut with).unwrap().imported.is_empty());
        let checked = super::super::check(&program, &settings).unwrap();
        assert_eq!(module, checked);
        module
    }

    const BASE: &str = "\
pub fn(T) first(a: array(T)) -> T:
    return a[0]
pub enum(i32) Kind:
    small = 1
    big
pub let table = [1, 2, 3]
var calls = 0
pub fn count() -> i32:
    calls += 1
    return calls
pub fn sum(a: array(i32)) -> i32:
    var total = 0
    for x in a:
        total += x
    return total
pub let total = sum(table)
pub let summed: fn(array(i32)) -> i32 = sum
";

    #[test]
    fn linking_the_artifacts_of_a_program_makes_the_module_checking_it_does() {
        let mut files = command(vec![
            (
                "main",
                "\
use base
use text
let counted = base.count() + base.count()
let halves = base.first([2.5])
let both = text.doubled + base.first([1]) + base.Kind.big as i32
pub let seen = base.summed([4, 5]) + text.pick(1) + counted + both
fn main():
    let words = [\"one\", \"two\"]
    base.count()
",
            ),
            ("@base", BASE),
            (
                "@text",
                "\
use base
pub let doubled = base.first([21])
pub fn pick(i: uint) -> i32:
    return base.table[i] + base.count()
",
            ),
        ]);
        let module = linked(&mut files).unwrap();
        assert!(
            module
                .funcs
                .iter()
                .any(|f| f.exports == [crate::world::RUN_EXPORT])
        );
    }

    #[test]
    fn packages_beside_one_another_share_what_they_make_of_one_they_both_use() {
        // Both make the one instance of `first`, and `right` names the one
        // `left` made, though it doesn't depend on it.
        let mut files = library(vec![
            (
                "main",
                "use left\nuse right\npub let x = left.a + right.b\n",
            ),
            ("@base", BASE),
            (
                "@left",
                "use base\npub let a = base.first([3])\npub fn f() -> i32:\n    return base.first([4])\n",
            ),
            (
                "@right",
                "\
use base
extern:
    fn now() -> i64
pub let b = base.first([5]) + base.total
pub fn g() -> i64:
    return now() + base.first([6]) as i64
pub let late: fn() -> i64 = g
",
            ),
        ]);
        linked(&mut files).unwrap();
        let artifacts = artifacts_of(&mut files);
        let names: Vec<_> = artifacts.iter().map(|a| a.name.as_str()).collect();
        assert_eq!(names, ["@base", "@left", "@right", "main"]);
        let mut uses = artifacts[2].uses().to_vec();
        uses.sort();
        assert_eq!(uses, ["@base", "@left"]);
    }

    #[test]
    fn what_fails_of_linking_is_reported_where_checking_reports_it() {
        let mut files = library(vec![
            ("main", "use base\nlet fine = 1\nlet bad = base.at(7)\n"),
            (
                "@base",
                "pub fn at(i: uint) -> i32:\n    let a = [1, 2]\n    return a[i]\npub let ok = at(1)\n",
            ),
        ]);
        let errors = linked(&mut files).unwrap_err();
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(errors[0].starts_with("main \"base.at(7)\""), "{errors:?}");
    }

    #[test]
    fn a_package_is_compiled_against_the_artifacts_of_those_it_uses() {
        let main = "\
use base
pub fn main():
    let first = base.first(base.table)
    let k = base.Kind.big
    let n = base.count() + first + k as i32
    let _ = n
";
        separately(&mut command(vec![("main", main), ("@base", BASE)]));
    }

    #[test]
    fn packages_are_compiled_alone_along_a_chain() {
        let geo = "\
pub struct Point:
    pub x: i32
    pub y: i32 = 10
pub struct(T) Box:
    pub value: T
    pub tag: u8 = 7
pub enum(u8) Kind:
    small = 1
    big
pub fn scale(p: Point, by: i32 = 2) -> Point:
    return Point(x: p.x * by, y: p.y * by)
pub fn(T) wrap(x: T) -> Box(T):
    return Box(T)(value: x)
pub fn origin() -> opaque(Point):
    return Point(x: 0)
pub fn adder(n: i32) -> opaque(fn(i32) -> i32):
    fn add(x: i32) -> i32:
        return x + n
    return add
pub let unit = Point(x: 1)
pub var calls = 0
pub fn count() -> i32:
    calls += 1
    return calls
";
        let shapes = "\
use geo
pub use geo.Point
pub enum(u8) Size:
    use geo.Kind
    huge
pub let base = geo.scale(geo.unit)
pub let boxed = geo.wrap(3)
pub fn area(p: geo.Point) -> i32:
    return p.x * p.y
pub fn(F: fn(i32) -> i32) pick(f: F) -> i32:
    return f(1)
pub fn twice() -> i32:
    return pick(geo.adder(2)) + geo.count()
";
        let main = "\
use shapes
use geo
pub fn main():
    let p = shapes.Point(x: 2)
    let a = shapes.area(p) + shapes.area(shapes.base)
    let b = shapes.boxed.value + geo.wrap(true).tag as i32
    let k = shapes.Size.huge as i32 + geo.Kind.big as i32
    let o = geo.origin()
    let add = geo.adder(5)
    let c = add(a) + shapes.twice() + shapes.pick(add) + (o as geo.Point).y
    let _ = (b, k, c)
";
        let files = vec![("main", main), ("@shapes", shapes), ("@geo", geo)];
        separately(&mut command(files));
    }

    #[test]
    fn an_artifact_is_linked_after_those_of_the_packages_it_uses() {
        let mut files = library(vec![
            ("main", "use base\npub let x = base.total\n"),
            ("@base", BASE),
        ]);
        let mut artifacts = artifacts_of(&mut files);
        let errors = link(&artifacts[1..], &files.settings()).unwrap_err();
        let unlinked = TypeErrorKind::Unlinked {
            artifact: "main".to_string(),
            package: "@base".to_string(),
        };
        assert_eq!(errors, [TypeError::nowhere(unlinked.clone())]);
        artifacts.reverse();
        assert_eq!(
            link(&artifacts, &files.settings()).unwrap_err(),
            [TypeError::nowhere(unlinked)]
        );
    }

    #[test]
    fn bytes_that_are_no_artifact_are_not_read_as_one() {
        let mut files = library(vec![("main", BASE)]);
        let bytes = artifacts_of(&mut files)[0].encode();
        assert!(Artifact::decode(&bytes[..bytes.len() - 1]).is_err());
        assert!(Artifact::decode(&[bytes.clone(), vec![0]].concat()).is_err());
        assert!(Artifact::decode(b"not an artifact").is_err());
        let mut later = bytes.clone();
        later[MAGIC.len()] = VERSION as u8 + 1;
        let error = Artifact::decode(&later).unwrap_err();
        assert!(error.to_string().contains("version"), "{error}");
    }
}

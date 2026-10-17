//! Linking: placing the literals of a lowered program in memory, and
//! running the constants that are only known by running them, so that each
//! [`Symbol`] its code holds is the constant it stands for.
//!
//! Lowering does neither. It makes each literal a [`DataDef`] and each such
//! constant a [`ValueDef`], and [`Event`]s record the order it asks for
//! them in: the order they would be placed and run in if each were done as
//! it is asked for. Linking does them in that order, so a constant runs on
//! memory as it would be there: with every literal placed before it, as the
//! runs before it left it. A literal goes past the pages a run grew memory
//! by, and over what code run for a constant wrote where it goes.
//!
//! What fails of linking is reported among the errors of checking, where
//! it was asked for: a run that traps is reported as if it had trapped
//! where its constant is checked.

use std::collections::{HashMap, HashSet};
use std::mem;

use crate::eval::{self, Evaluator, Failure, FailureKind};
use crate::file::Settings;
use crate::ir::{self, Const, DataId, Expr, FuncId, Stmt, Symbol, UnOp, ValType, ValueId};
use crate::lex::Span;
use crate::load::Program;

use super::enums::{const_bits, const_int, int_const};
use super::{
    Cell, Checker, Fold, InstanceSite, MEMORY_EXPORT, PAGE_SIZE, Prim, Scalar, TABLE_EXPORT, TEMP,
    TypeError, TypeErrorKind, fn_ptr, fold, zero,
};

/// The most pages that the code constants run may grow memory to, whatever
/// the settings let it grow to: 32 MiB. The literals take what they take,
/// and only the pages they leave are the code's. So the memory that
/// compiling takes is bounded by what the program is, wherever it is
/// compiled.
const MAX_CONSTANT_PAGES: u64 = 512;

/// The most functions an error names of those that were running.
const MAX_STACK: usize = 8;

/// What lowering leaves to linking, and what linking makes of it.
#[derive(Default)]
pub(super) struct Linking {
    /// What the program places in memory, by [`DataId`].
    pub(super) data: Vec<DataDef>,
    /// The constants that are only known by running them, by [`ValueId`].
    pub(super) values: Vec<ValueDef>,
    /// What is checked of them once they are known.
    pub(super) checks: Vec<CheckDef>,
    /// The order lowering asked for each to be placed, found or checked in.
    pub(super) events: Vec<Event>,
    /// The most pages memory may grow to, unless it may grow without
    /// limit.
    max_pages: Option<u64>,
    /// The address literals must end by.
    data_limit: u64,
    /// The fuel the constants of one item run on.
    fuel_limit: u64,
    /// Where each data is placed, once it is.
    addrs: Vec<Option<u64>>,
    /// The scalars of each value, once it is found.
    found: Vec<Option<Vec<Const>>>,
    /// The contents of literals, in the order they are placed.
    placed: Vec<ir::Data>,
    /// The first address after the last literal, or the address the settings
    /// place them from if there is none. The pages up to it are the
    /// literals', and those that code run for a constant grows memory by are
    /// not. Data that doesn't fit may end past every address.
    data_end: u128,
    /// The address of each constant that functions only read, by its bytes,
    /// what they are aligned to and how many copies there are.
    shared: HashMap<(Vec<u8>, u32, u64), u64>,
    /// The state that the code constants run leaves, which the module
    /// starts with. `None` until one runs any.
    eval: Option<Evaluator>,
    /// How many of `placed` are in the memory of `eval`.
    synced: usize,
    /// The addresses of literals that are all zeros, which aren't in
    /// `placed`, and how many bytes each is: those placed since `eval` was
    /// last given them.
    zeroed: Vec<(u64, u64)>,
    /// Whether code run for a constant failed. None is run after that, as
    /// it left the state half made.
    failed: bool,
    /// What is left of the fuel of each item whose constants ran, by the
    /// item: none runs outside an item, which has none.
    fuel: HashMap<Option<usize>, u64>,
    /// The errors of linking, each with how many errors checking had
    /// reported where it was asked for.
    errors: Vec<(usize, TypeError)>,
}

/// What the program places in memory: a literal, or room for what is
/// written there.
pub(super) struct DataDef {
    /// The bytes, of each copy if there are copies, as far as checking
    /// knows them.
    pub(super) bytes: Vec<u8>,
    /// What only linking knows of the bytes: values to write to cells, at
    /// offsets into them.
    pub(super) fills: Vec<Fill>,
    pub(super) align: u32,
    /// How many copies there are, of those that are copied.
    pub(super) count: Scalar,
    pub(super) how: Placing,
}

/// A value written into a literal's bytes where it is placed, as storing it
/// to its cells would.
pub(super) struct Fill {
    pub(super) offset: usize,
    pub(super) cells: Vec<Cell>,
    pub(super) scalars: Vec<Scalar>,
}

/// How a [`DataDef`] is placed.
pub(super) enum Placing {
    /// Its bytes, wherever they fit, as a literal of an initializer is.
    Own,
    /// Its copies, written out unless they are zeros.
    Copied,
    /// Its copies, at the address of the same bytes copied as often if they
    /// were placed so: as a literal is that functions only read.
    Shared,
    /// Room for this many bytes, which nothing is written to.
    Room(u128),
}

/// A constant that is only known by running it, or by folding what only
/// linking knows of.
pub(super) struct ValueDef {
    pub(super) how: Finding,
    /// The item whose constants it is among, whose fuel it runs on.
    pub(super) item: Option<usize>,
    /// Where it is, for an error to say, with the instances of generic
    /// functions that led to it.
    pub(super) span: Span,
    pub(super) instances: Vec<InstanceSite>,
    /// How much of the program there was when it was asked for: how many
    /// functions there were, the imported among them, how many globals and
    /// how many functions the table held. Those are what a run reaches.
    pub(super) funcs: usize,
    pub(super) globals: usize,
    pub(super) table: usize,
    /// How many errors checking had reported by then.
    pub(super) errors: usize,
}

/// How a [`ValueDef`] is found.
pub(super) enum Finding {
    /// By folding `thunk`, a function that takes nothing and returns the
    /// scalars, which are made of constants alone.
    Fold(ir::Func),
    /// By running `thunk`, which may call the functions of `reached`.
    Run {
        thunk: ir::Func,
        reached: HashSet<FuncId>,
    },
    /// As the integer of type `prim` after `from`, as an enum's member
    /// `member` counts up from the one before. One past the type is an
    /// error.
    Count {
        from: Scalar,
        prim: Prim,
        member: String,
    },
}

/// What is checked of constants once linking knows them, as checking would
/// if it knew them.
pub(super) struct CheckDef {
    pub(super) check: Check,
    /// How many errors checking had reported where it would check it.
    pub(super) errors: usize,
}

pub(super) enum Check {
    /// That no two members of an enum have one value, by each one's name,
    /// where it is, and its value. One from `from` on that has the value of
    /// one before it is reported: checking has compared those before.
    Distinct {
        members: Vec<(String, Span, Vec<Scalar>)>,
        from: usize,
    },
    /// That a literal holds no elements, there being `count`, or else
    /// `kind` at `span`.
    Empty {
        count: Scalar,
        kind: TypeErrorKind,
        span: Span,
    },
}

/// What lowering asked of linking.
#[derive(Clone, Copy)]
pub(super) enum Event {
    Place(DataId),
    Find(ValueId),
    Check(usize),
}

impl Linking {
    /// Nothing to link yet, of a program that `settings` say how to build,
    /// whose literals end by `data_limit` and whose items' constants each
    /// run on `fuel_limit`.
    pub(super) fn new(settings: &Settings, data_limit: u64, fuel_limit: u64) -> Self {
        Self {
            max_pages: settings.max_pages,
            data_limit,
            data_end: settings.static_start.into(),
            fuel_limit,
            ..Self::default()
        }
    }

    /// Records `def`, which is placed where it is in the order of events.
    /// Returns the symbol of its address.
    pub(super) fn place(&mut self, def: DataDef) -> Symbol {
        let id = DataId(self.data.len() as u32);
        self.data.push(def);
        self.events.push(Event::Place(id));
        Symbol::Data(id, 0)
    }

    /// Records `def`, which is found where it is in the order of events.
    pub(super) fn find(&mut self, def: ValueDef) -> ValueId {
        let id = ValueId(self.values.len() as u32);
        self.values.push(def);
        self.events.push(Event::Find(id));
        id
    }

    /// Records `def`, which is checked where it is in the order of events.
    pub(super) fn check(&mut self, def: CheckDef) {
        self.events.push(Event::Check(self.checks.len()));
        self.checks.push(def);
    }

    /// The constant `symbol` stands for, held as a `ty`, if it is known:
    /// an address once its data is placed, and a scalar once its value is
    /// found. One of another type is held as a wider leaf or a float's bits
    /// hold it.
    pub(super) fn resolve(&self, ty: ValType, symbol: Symbol) -> Option<Const> {
        let c = match symbol {
            Symbol::Data(id, offset) => {
                let addr = (*self.addrs.get(id.0 as usize)?)?;
                Const::I32((addr as i64).wrapping_add(offset) as i32)
            }
            Symbol::Value(id, index) => {
                let found = self.found.get(id.0 as usize)?.as_ref()?;
                *found.get(index as usize)?
            }
        };
        held(c, ty)
    }

    /// The constant `scalar` is, if it is known.
    pub(super) fn known(&self, scalar: Scalar) -> Option<Const> {
        match scalar {
            Scalar::Known(c) => Some(c),
            Scalar::Linked(ty, symbol) => self.resolve(ty, symbol),
        }
    }

    /// Makes each symbol in `body` the constant it stands for. Returns
    /// whether each is known.
    pub(super) fn resolve_stmts(&self, body: &mut [Stmt]) -> bool {
        let mut known = true;
        walk_stmts(body, &mut |expr| {
            if let Expr::Symbol(ty, symbol) = *expr {
                match self.resolve(ty, symbol) {
                    Some(c) => *expr = Expr::Const(c),
                    None => known = false,
                }
            }
        });
        known
    }

    /// The pages memory has: the fewest that hold the literals, or as many
    /// as the code constants ran grew it to, if those are more.
    pub(super) fn pages(&self) -> u64 {
        let literals = self.data_end.div_ceil(PAGE_SIZE.into());
        let grown = self.eval.as_ref().map_or(0, Evaluator::pages);
        u64::try_from(literals).unwrap_or(u64::MAX).max(grown)
    }

    /// Whether every literal placed so far is within the pages memory may
    /// grow to.
    pub(super) fn data_fits(&self) -> bool {
        self.data_end <= self.data_limit.into()
    }

    /// Reports `kind` at `span` among the errors of checking, after the
    /// first `errors` of them.
    fn error(
        &mut self,
        errors: usize,
        kind: TypeErrorKind,
        span: Span,
        instances: &[InstanceSite],
    ) {
        self.errors.push((
            errors,
            TypeError {
                kind,
                span: Some(span),
                instances: instances.to_vec(),
                similar: None,
            },
        ));
    }

    /// Makes room in memory for `size` bytes at the next multiple of `align`,
    /// or right at the end if there are none. Returns their address, which
    /// is only meaningful while the data fits.
    ///
    /// Bytes that the literals' last page has no room for go in the pages
    /// after it, unless code run for a constant grew memory since: those
    /// pages are its own, as any are that `module.grow` gives, so the bytes
    /// go in pages past them.
    fn reserve(&mut self, size: u128, align: u32) -> u64 {
        let mut offset = self.data_end;
        if size > 0 {
            offset = offset.next_multiple_of(align.into());
            let page = u128::from(PAGE_SIZE);
            let owned = self.data_end.next_multiple_of(page);
            let grown = self.eval.as_ref().map_or(0, Evaluator::pages);
            let top = u128::from(grown) * page;
            if offset + size > owned && top > owned {
                offset = top;
            }
            self.data_end = offset + size;
        }
        offset as u64
    }

    /// Places `count` copies of `bytes` in memory at the next multiple of
    /// `align`. Returns the address of the first.
    fn copy(&mut self, bytes: &[u8], align: u32, count: u64) -> u64 {
        let size = bytes.len() as u64;
        let offset = self.reserve(u128::from(size) * u128::from(count), align);
        // Memory starts out zeroed, and data that doesn't fit is an error, so
        // neither is written out.
        let zeroed = count == 0 || bytes.iter().all(|&byte| byte == 0);
        if !zeroed && self.data_fits() {
            let bytes = bytes.repeat(count as usize);
            self.placed.push(ir::Data { offset, bytes });
        } else if self.eval.is_some() && self.data_fits() {
            // Code that has run may have written there.
            self.zeroed.push((offset, size * count));
        }
        offset
    }

    /// Checks what check `index` is of, now that it is known: what isn't,
    /// as a constant that failed or didn't run isn't, is not checked.
    fn run_check(&mut self, index: usize) {
        let def = &self.checks[index];
        let errors = def.errors;
        match &def.check {
            Check::Distinct { members, from } => {
                let mut bits: Vec<Option<Vec<u64>>> = Vec::new();
                let mut duplicates = Vec::new();
                for (i, (name, span, value)) in members.iter().enumerate() {
                    // One that failed to check has none.
                    let consts: Option<Vec<_>> = value.iter().map(|s| self.known(*s)).collect();
                    let consts = consts.filter(|_| !value.is_empty());
                    let value_bits = consts.map(|v| v.into_iter().map(const_bits).collect());
                    let same = value_bits
                        .as_ref()
                        .filter(|_| i >= *from)
                        .and_then(|b| bits.iter().position(|prev| prev.as_ref() == Some(b)));
                    if let Some(same) = same {
                        let kind = TypeErrorKind::DuplicateValue {
                            member: name.clone(),
                            same_as: members[same].0.clone(),
                        };
                        duplicates.push((kind, *span));
                    }
                    bits.push(value_bits);
                }
                for (kind, span) in duplicates {
                    self.error(errors, kind, span, &[]);
                }
            }
            Check::Empty { count, kind, span } => {
                let (kind, span) = (kind.clone(), *span);
                if self
                    .known(*count)
                    .is_some_and(|count| const_count(count) > 0)
                {
                    self.error(errors, kind, span, &[]);
                }
            }
        }
    }

    /// Places data `id`, as its [`Placing`] says. Nothing is placed of one
    /// whose bytes or count are made of a value that isn't found, which a
    /// constant that failed or didn't run is: an error is reported.
    fn place_data(&mut self, ck: &Checker, id: DataId) {
        let def = &self.data[id.0 as usize];
        let (align, how) = (def.align, &def.how);
        let Some(count) = self.known(def.count).map(const_count) else {
            return;
        };
        let mut bytes = def.bytes.clone();
        for fill in &def.fills {
            let consts: Option<Vec<_>> = fill.scalars.iter().map(|s| self.known(*s)).collect();
            let Some(consts) = consts else {
                return;
            };
            ck.write_consts(&mut bytes[fill.offset..], &fill.cells, &consts);
        }
        let addr = match how {
            Placing::Own => {
                let offset = self.reserve(bytes.len() as u128, align);
                if !bytes.is_empty() {
                    self.placed.push(ir::Data { offset, bytes });
                }
                offset
            }
            Placing::Copied => self.copy(&bytes, align, count),
            // One that is empty takes no memory to share.
            Placing::Shared if bytes.is_empty() || count == 0 => self.reserve(0, align),
            Placing::Shared => {
                let key = (bytes, align, count);
                match self.shared.get(&key) {
                    Some(placed) => *placed,
                    None => {
                        let offset = self.copy(&key.0, align, count);
                        self.shared.insert(key, offset);
                        offset
                    }
                }
            }
            Placing::Room(size) => self.reserve(*size, align),
        };
        let addrs = &mut self.addrs;
        addrs.resize(addrs.len().max(id.0 as usize + 1), None);
        addrs[id.0 as usize] = Some(addr);
    }
}

impl Checker {
    /// Places the literals of the program and finds the constants that are
    /// only known by running them, in the order lowering asked for them,
    /// with `funcs`, every function the program defines, for constants to
    /// call. What fails of them is reported among the errors of checking,
    /// where each was asked for.
    pub(super) fn link_constants(&mut self, program: &Program, funcs: &[ir::Func]) {
        let mut link = mem::take(&mut self.link);
        let imports = self.lower_imports(program);
        for event in mem::take(&mut link.events) {
            match event {
                Event::Place(id) => link.place_data(self, id),
                Event::Find(id) => self.find_value(&mut link, &imports, funcs, id),
                Event::Check(index) => link.run_check(index),
            }
        }
        // Each is reported after those of checking before it, and before
        // those after it.
        let mut errors = mem::take(&mut self.errors);
        for (inserted, (at, error)) in mem::take(&mut link.errors).into_iter().enumerate() {
            errors.insert((at + inserted).min(errors.len()), error);
        }
        self.errors = errors;
        self.link = link;
    }

    /// Finds value `id`: folds it, or runs it, unless a run failed before
    /// it or an error was reported before it, or the literals don't fit, as
    /// what is left lowered may not be valid then. A run is only asked for
    /// where checking has reported no error.
    fn find_value(
        &mut self,
        link: &mut Linking,
        imports: &[ir::Import],
        funcs: &[ir::Func],
        id: ValueId,
    ) {
        let found = match &link.values[id.0 as usize].how {
            Finding::Fold(_) => fold_found(link, id),
            Finding::Count { .. } => count_found(link, id),
            Finding::Run { .. } if link.failed || !link.errors.is_empty() => None,
            Finding::Run { .. } if !link.data_fits() => None,
            Finding::Run { .. } => self.run_found(link, imports, funcs, id),
        };
        let found_list = &mut link.found;
        found_list.resize(found_list.len().max(id.0 as usize + 1), None);
        found_list[id.0 as usize] = found;
    }

    /// Runs value `id` with the state of the program so far, which is made
    /// first if none has run yet. `None` after reporting why it has no
    /// value.
    fn run_found(
        &mut self,
        link: &mut Linking,
        imports: &[ir::Import],
        funcs: &[ir::Func],
        id: ValueId,
    ) -> Option<Vec<Const>> {
        let def = &link.values[id.0 as usize];
        let (span, errors, instances) = (def.span, def.errors, def.instances.clone());
        let (item, globals) = (def.item, def.globals);
        let module = match self.hosted(link, imports, funcs, def) {
            Ok(module) => module,
            Err(why) => {
                link.failed = true;
                link.error(errors, TypeErrorKind::ConstNotRun(why), span, &instances);
                return None;
            }
        };
        let full = match item {
            Some(_) => link.fuel_limit,
            None => 0,
        };
        let fuel = *link.fuel.entry(item).or_insert(full);
        let results = match self.sync(link, globals) {
            Ok(eval) => {
                let (results, left) = eval.run(&module, fuel);
                link.fuel.insert(item, left);
                results
            }
            Err(failure) => Err(failure),
        };
        match results {
            Ok(consts) => Some(consts),
            Err(failure) => {
                link.failed = true;
                let Finding::Run { reached, .. } = &link.values[id.0 as usize].how else {
                    unreachable!("what is run is found by running it");
                };
                let kind = self.failure_kind(link.fuel_limit, &module, reached, failure);
                link.error(errors, kind, span, &instances);
                None
            }
        }
    }

    /// The module that runs the code of `def` with the state of the program
    /// so far. It has every function there was then, each where the program
    /// has it, so that what is lowered calls what it names, but only those
    /// it may reach have their bodies: the others are never reached. Each
    /// symbol is what it stands for, or else it can't be run.
    fn hosted(
        &self,
        link: &Linking,
        imports: &[ir::Import],
        funcs: &[ir::Func],
        def: &ValueDef,
    ) -> Result<ir::Module, String> {
        let unknown = || "it uses what isn't known yet".to_string();
        let Finding::Run { thunk, reached } = &def.how else {
            unreachable!("what is run is found by running it");
        };
        let ids = (self.import_count..def.funcs as u32).map(FuncId);
        let mut hosted = Vec::new();
        for id in ids {
            let func = &funcs[(id.0 - self.import_count) as usize];
            hosted.push(match reached.contains(&id) {
                true => {
                    let mut func = ir::Func {
                        exports: Vec::new(),
                        ..func.clone()
                    };
                    if !link.resolve_stmts(&mut func.body) {
                        return Err(unknown());
                    }
                    func
                }
                false => stub(func),
            });
        }
        let mut thunk = thunk.clone();
        if !link.resolve_stmts(&mut thunk.body) {
            return Err(unknown());
        }
        hosted.push(thunk);
        let globals = self.ir_globals[..def.globals].iter().zip(&self.ir_inits);
        let globals: Option<Vec<_>> = globals
            .map(|(global, init)| {
                let init = link.known(*init)?;
                Some(ir::Global {
                    init,
                    ..global.clone()
                })
            })
            .collect();
        Ok(ir::Module {
            // The memory is the evaluator's, whatever size it is.
            memory: ir::Memory {
                min_pages: 0,
                max_pages: None,
                export: MEMORY_EXPORT.to_string(),
            },
            data: Vec::new(),
            table: Some(ir::Table {
                export: Some(TABLE_EXPORT.to_string()),
                funcs: self.table[..def.table].to_vec(),
            }),
            globals: globals.ok_or_else(unknown)?,
            imports: imports.to_vec(),
            funcs: hosted,
        })
    }

    /// The state that the code constants run leaves, made if none has run
    /// yet, with the literals placed and the first `globals` globals defined
    /// since it was last asked for. An error if memory can't hold them.
    fn sync<'l>(
        &self,
        link: &'l mut Linking,
        globals: usize,
    ) -> Result<&'l mut Evaluator, Failure> {
        let max = link.max_pages.unwrap_or(u64::MAX);
        let end = u64::try_from(link.data_end).unwrap_or(u64::MAX);
        let defined = link.eval.as_ref().map_or(0, Evaluator::global_count);
        let added: Vec<_> = (defined..globals)
            .map(|index| {
                let global = &self.ir_globals[index];
                let init = link.known(self.ir_inits[index]).unwrap_or(zero(global.ty));
                ir::Global {
                    init,
                    ..global.clone()
                }
            })
            .collect();
        let eval = link
            .eval
            .get_or_insert_with(|| Evaluator::new(max, MAX_CONSTANT_PAGES));
        if !eval.cover(end) {
            let why = "memory can't grow to hold the literals".to_string();
            return Err(Failure {
                kind: FailureKind::Invalid(why),
                stack: Vec::new(),
            });
        }
        for (offset, len) in link.zeroed.drain(..) {
            eval.zero(offset, len);
        }
        for data in &link.placed[link.synced..] {
            eval.write(data.offset, &data.bytes);
        }
        link.synced = link.placed.len();
        for global in &added {
            eval.add_global(global);
        }
        Ok(eval)
    }

    /// Gives the state that the code constants ran left, if any ran, the
    /// literals placed since the last of it did. Reports memory that can't
    /// hold them.
    pub(super) fn place_late_literals(&mut self) {
        if self.link.eval.is_none() || !self.errors.is_empty() {
            return;
        }
        let mut link = mem::take(&mut self.link);
        let globals = self.ir_globals.len();
        if let Err(failure) = self.sync(&mut link, globals) {
            let FailureKind::Invalid(why) = failure.kind else {
                unreachable!("nothing is run");
            };
            self.error_nowhere(TypeErrorKind::ConstNotRun(why));
        }
        self.link = link;
    }

    /// Checks that the literals end within the pages memory may grow to.
    pub(super) fn check_data_fits(&mut self) {
        if self.link.data_fits() {
            return;
        }
        let end = self.link.data_end;
        let within = |max_pages: &u64| end <= u128::from(*max_pages) * u128::from(PAGE_SIZE);
        let kind = match self.link.max_pages.filter(|max_pages| !within(max_pages)) {
            Some(max_pages) => TypeErrorKind::DataPastMax { end, max_pages },
            None => TypeErrorKind::DataTooLarge { end },
        };
        self.errors.push(TypeError {
            kind,
            span: None,
            instances: Vec::new(),
            similar: None,
        });
    }

    /// What an error says of `failure`, which stopped `module`. It has the
    /// bodies of the functions of `reached`.
    fn failure_kind(
        &self,
        fuel_limit: u64,
        module: &ir::Module,
        reached: &HashSet<FuncId>,
        failure: Failure,
    ) -> TypeErrorKind {
        let imports = module.imports.len();
        let name = |index: &u32| match (*index as usize).checked_sub(imports) {
            Some(defined) => module.funcs[defined].name.clone(),
            None => module.imports[*index as usize].name.clone(),
        };
        // The constant itself is the last of them.
        let thunk = (imports + module.funcs.len() - 1) as u32;
        let frames = failure.stack.iter().filter(|index| **index != thunk);
        // A function that calls itself is named once.
        let mut stack: Vec<_> = frames.map(name).collect();
        stack.dedup();
        stack.truncate(MAX_STACK);
        let innermost = failure.stack.first().copied();
        let unnamed = innermost.filter(|index| {
            *index != thunk && *index >= self.import_count && !reached.contains(&FuncId(*index))
        });
        match failure.kind {
            // One of those given no body.
            FailureKind::Unreachable if unnamed.is_some() => TypeErrorKind::ConstCallsUnnamed {
                name: stack[0].clone(),
                stack: stack[1..].to_vec(),
            },
            FailureKind::Unreachable => TypeErrorKind::ConstTraps {
                trap: "unreachable code is reached".to_string(),
                stack,
            },
            FailureKind::Trap(trap) => TypeErrorKind::ConstTraps { trap, stack },
            FailureKind::OutOfFuel => TypeErrorKind::ConstOutOfFuel {
                fuel: fuel_limit,
                stack,
            },
            FailureKind::Imported(index) => TypeErrorKind::ConstCallsExtern {
                name: name(&index),
                stack,
            },
            FailureKind::Invalid(why) => TypeErrorKind::ConstNotRun(why),
        }
    }

    /// The module of `imports` and `funcs`, which are all that is lowered
    /// of a program without errors, linked: with the memory `settings`
    /// describe, as the code its constants ran left it, and each symbol
    /// what it stands for.
    pub(super) fn module(
        mut self,
        imports: Vec<ir::Import>,
        mut funcs: Vec<ir::Func>,
        settings: &Settings,
    ) -> ir::Module {
        let link = &self.link;
        let min_pages = link.pages();
        for func in &mut funcs {
            let known = link.resolve_stmts(&mut func.body);
            assert!(known, "a program without errors links");
        }
        let mut bodies = funcs.iter().map(|func| &func.body);
        let called = bodies.any(|body| fn_ptr::calls_through_table(body));
        let mut globals = mem::take(&mut self.ir_globals);
        for (global, init) in globals.iter_mut().zip(&self.ir_inits) {
            global.init = link.known(*init).expect("a program without errors links");
        }
        let data = match &link.eval {
            Some(eval) => {
                for (index, global) in globals.iter_mut().enumerate() {
                    if global.mutable {
                        global.init = eval.global(index);
                    }
                }
                eval.data()
            }
            None => mem::take(&mut self.link.placed),
        };
        ir::Module {
            memory: ir::Memory {
                min_pages,
                max_pages: settings.max_pages,
                export: MEMORY_EXPORT.to_string(),
            },
            data,
            // A pointer that no function is taken as is still called
            // through the table, where nothing is: the call traps.
            table: (!self.table.is_empty() || called).then(|| ir::Table {
                export: self.world.is_library().then(|| TABLE_EXPORT.to_string()),
                funcs: self.table,
            }),
            globals,
            imports,
            funcs,
        }
    }
}

/// The scalars of value `id`, which are made of constants alone, once
/// what only linking knows of them is known. `None` after reporting a
/// trap, or if what it is made of isn't known.
fn fold_found(link: &mut Linking, id: ValueId) -> Option<Vec<Const>> {
    let def = &link.values[id.0 as usize];
    let Finding::Fold(thunk) = &def.how else {
        unreachable!("what is folded is found by folding it");
    };
    let mut body = thunk.body.clone();
    if !link.resolve_stmts(&mut body) {
        return None;
    }
    let Some(Stmt::Return(scalars)) = body.last() else {
        unreachable!("what is folded returns its scalars");
    };
    let mut consts = Vec::new();
    for scalar in scalars {
        match fold(scalar) {
            Ok(Scalar::Known(c)) => consts.push(c),
            Err(Fold::Trap) => {
                let (errors, span, instances) = (def.errors, def.span, def.instances.clone());
                link.error(errors, TypeErrorKind::ConstTrap, span, &instances);
                return None;
            }
            _ => unreachable!("what only linking knew of is known"),
        }
    }
    Some(consts)
}

/// The integer that value `id` counts up to, once what it counts from is
/// known. `None` after reporting one past its type.
fn count_found(link: &mut Linking, id: ValueId) -> Option<Vec<Const>> {
    let def = &link.values[id.0 as usize];
    let Finding::Count { from, prim, member } = &def.how else {
        unreachable!("what is counted is found by counting");
    };
    let n = const_int(*prim, link.known(*from)?) + 1;
    if n > prim.range().1 {
        let kind = TypeErrorKind::MemberOutOfRange {
            member: member.clone(),
            ty: prim.name().to_string(),
        };
        let (errors, span, instances) = (def.errors, def.span, def.instances.clone());
        link.error(errors, kind, span, &instances);
        return None;
    }
    Some(vec![int_const(*prim, n)])
}

/// A function with the wasm type of `func` that traps.
fn stub(func: &ir::Func) -> ir::Func {
    let local = |ty: &ValType| ir::Local {
        name: TEMP.to_string(),
        ty: *ty,
    };
    ir::Func {
        name: func.name.clone(),
        exports: Vec::new(),
        params: func.params.clone(),
        results: func.results.clone(),
        locals: func.params.iter().map(local).collect(),
        body: vec![Stmt::Unreachable],
    }
}

/// `c` as a `ty` holds it: itself, widened to a wider leaf, or as the bits
/// of a float or the float of bits, as [`super::unions::widen`] has it.
fn held(c: Const, ty: ValType) -> Option<Const> {
    use ValType::*;
    let reinterpret = |c| eval::fold_unary(eval::type_of(c), UnOp::Reinterpret, c);
    let extend = |c| eval::fold_unary(I32, UnOp::ExtendU, c);
    match (eval::type_of(c), ty) {
        (from, to) if from == to => Some(c),
        (I32, F32) | (I64, F64) | (F32, I32) | (F64, I64) => reinterpret(c),
        (I32, I64) => extend(c),
        (F32, I64) => extend(reinterpret(c)?),
        _ => None,
    }
}

/// The count of copies `c` is, which is an address-wide integer.
fn const_count(c: Const) -> u64 {
    match c {
        Const::I32(count) => (count as u32).into(),
        Const::I64(count) => count as u64,
        _ => unreachable!("a count is an integer"),
    }
}

/// Calls `f` on each expression in `body`, outermost first.
fn walk_stmts(body: &mut [Stmt], f: &mut impl FnMut(&mut Expr)) {
    for stmt in body {
        match stmt {
            Stmt::SetLocal(_, value) | Stmt::SetGlobal(_, value) | Stmt::Drop(value) => {
                walk_expr(value, f);
            }
            Stmt::Store { addr, value, .. } => {
                walk_expr(addr, f);
                walk_expr(value, f);
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
            } => [a, b, c].into_iter().for_each(|e| walk_expr(e, f)),
            Stmt::Call { args, .. } => args.iter_mut().for_each(|arg| walk_expr(arg, f)),
            Stmt::CallIndirect { args, index, .. } => {
                args.iter_mut().for_each(|arg| walk_expr(arg, f));
                walk_expr(index, f);
            }
            Stmt::Block(body) | Stmt::Loop(body) => walk_stmts(body, f),
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                walk_expr(cond, f);
                walk_stmts(then_body, f);
                walk_stmts(else_body, f);
            }
            Stmt::BrIf(_, cond) => walk_expr(cond, f),
            Stmt::Return(values) => values.iter_mut().for_each(|e| walk_expr(e, f)),
            Stmt::Br(_) | Stmt::Unreachable => {}
        }
    }
}

/// Calls `f` on `expr` and then on each expression within it.
fn walk_expr(expr: &mut Expr, f: &mut impl FnMut(&mut Expr)) {
    f(expr);
    match expr {
        Expr::Const(_) | Expr::Local(_) | Expr::Global(_) | Expr::MemorySize | Expr::Symbol(..) => {
        }
        Expr::Unary(_, _, x) | Expr::Load { addr: x, .. } | Expr::MemoryGrow(x) => walk_expr(x, f),
        Expr::Binary(_, _, a, b) => {
            walk_expr(a, f);
            walk_expr(b, f);
        }
        Expr::Call(_, args) => args.iter_mut().for_each(|arg| walk_expr(arg, f)),
        Expr::CallIndirect { args, index, .. } => {
            args.iter_mut().for_each(|arg| walk_expr(arg, f));
            walk_expr(index, f);
        }
        Expr::If {
            cond,
            then_expr,
            else_expr,
            ..
        } => [cond, then_expr, else_expr]
            .into_iter()
            .for_each(|e| walk_expr(e, f)),
        Expr::Seq(body, value) => {
            walk_stmts(body, f);
            walk_expr(value, f);
        }
    }
}

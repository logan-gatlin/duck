//! Running lowered code while the program that holds it is compiled.
//!
//! An [`Evaluator`] is the state of the module being compiled, as its code
//! has left it so far: its memory, its table and its globals. Each
//! [`Evaluator::run`] is given a module of [`crate::emit::emit_hosted`],
//! which imports that state, and calls the function it exports as
//! [`ENTRY`]. What the calls leave behind is what the compiled module starts
//! with.
//!
//! The code is sandboxed: it reaches nothing but the state, a call of an
//! imported function fails, and fuel bounds how long it runs. Running it
//! gives the same results on every machine.

use std::fmt;
use std::sync::OnceLock;

use wasmtime::{
    Config, Engine, Extern, Func, FuncType, Global, GlobalType, Instance, Memory, MemoryType,
    Module, Mutability, Ref, RefType, Store, Table, TableType, Trap, Val, WasmBacktrace,
};

use crate::emit;
use crate::ir::{self, Const, ValType};

/// The name a module exports the function to run as.
pub(crate) const ENTRY: &str = "run";

/// The bytes in a wasm page.
const PAGE_SIZE: u64 = 64 * 1024;

/// The most zero bytes that two runs of others are kept in one segment
/// across, as a segment of its own costs about as many.
const MAX_GAP: usize = 8;

/// How much of memory is searched at once for a byte that isn't zero.
const BLOCK: usize = 4096;

/// The state of a module being compiled, which the code it runs shares.
pub(crate) struct Evaluator {
    store: Store<()>,
    memory: Memory,
    table: Table,
    /// The module's globals, in [`ir::Module::globals`] order.
    globals: Vec<Global>,
}

/// Why a run stopped short of its results.
#[derive(Debug, Clone, PartialEq)]
pub(crate) struct Failure {
    pub(crate) kind: FailureKind,
    /// The index of each function that was running, innermost first.
    pub(crate) stack: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) enum FailureKind {
    /// A trap, as wasm describes it.
    Trap(String),
    /// An `unreachable` that was reached.
    Unreachable,
    /// The fuel ran out.
    OutOfFuel,
    /// A call of the imported function of this index.
    Imported(u32),
    /// The module, or the state, is not one that can be run. A bug in the
    /// compiler, or a memory the machine can't hold.
    Invalid(String),
}

/// The error a call of an imported function fails with.
#[derive(Debug)]
struct Imported(u32);

impl fmt::Display for Imported {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "call of imported function {}", self.0)
    }
}

impl std::error::Error for Imported {}

impl Evaluator {
    /// A zeroed memory of `min_pages` pages that may grow to `max_pages`,
    /// addressed with an `i64` if it's a `memory64` and an `i32` otherwise,
    /// an empty table and no globals.
    pub(crate) fn new(memory64: bool, min_pages: u64, max_pages: u64) -> Result<Self, Failure> {
        let mut store = Store::new(engine(), ());
        let (memory, table) = match memory64 {
            true => (
                MemoryType::new64(min_pages, Some(max_pages)),
                TableType::new64(RefType::FUNCREF, 1, None),
            ),
            false => (
                MemoryType::new(min_pages as u32, Some(max_pages as u32)),
                TableType::new(RefType::FUNCREF, 1, None),
            ),
        };
        let memory = Memory::new(&mut store, memory).map_err(invalid)?;
        let table = Table::new(&mut store, table, Ref::Func(None)).map_err(invalid)?;
        Ok(Self {
            store,
            memory,
            table,
            globals: Vec::new(),
        })
    }

    /// The size of memory, in pages.
    pub(crate) fn pages(&self) -> u64 {
        self.memory.size(&self.store)
    }

    /// Grows memory to hold the address before `end`, unless it does.
    /// Returns whether it then does.
    pub(crate) fn cover(&mut self, end: u64) -> bool {
        let pages = end.div_ceil(PAGE_SIZE);
        let size = self.pages();
        pages <= size || self.memory.grow(&mut self.store, pages - size).is_ok()
    }

    /// Copies `bytes` to memory at `offset`, which holds them.
    pub(crate) fn write(&mut self, offset: u64, bytes: &[u8]) {
        let data = self.memory.data_mut(&mut self.store);
        data[offset as usize..][..bytes.len()].copy_from_slice(bytes);
    }

    /// Zeroes the `len` bytes of memory at `offset`, which holds them.
    pub(crate) fn zero(&mut self, offset: u64, len: u64) {
        let data = self.memory.data_mut(&mut self.store);
        data[offset as usize..][..len as usize].fill(0);
    }

    /// How many globals there are.
    pub(crate) fn global_count(&self) -> usize {
        self.globals.len()
    }

    /// Adds `global` after the others, as its initializer leaves it.
    pub(crate) fn add_global(&mut self, global: &ir::Global) {
        let mutability = match global.mutable {
            true => Mutability::Var,
            false => Mutability::Const,
        };
        let ty = GlobalType::new(val_type(global.ty), mutability);
        let global = Global::new(&mut self.store, ty, val(global.init));
        self.globals
            .push(global.expect("a constant has the type of its global"));
    }

    /// What global `index` holds.
    pub(crate) fn global(&mut self, index: usize) -> Const {
        konst(&self.globals[index].get(&mut self.store))
    }

    /// Calls the function that `module` exports as [`ENTRY`], which takes
    /// nothing, with `fuel` to run on. `module` has the globals that were
    /// added, in order, and its table is given the functions it holds.
    /// Returns the results, or why there are none, and the fuel left over.
    pub(crate) fn run(
        &mut self,
        module: &ir::Module,
        fuel: u64,
    ) -> (Result<Vec<Const>, Failure>, u64) {
        let results = self.call(module, fuel);
        // No fuel is given back by a module that never ran.
        (results, self.store.get_fuel().unwrap_or(0))
    }

    fn call(&mut self, module: &ir::Module, fuel: u64) -> Result<Vec<Const>, Failure> {
        let engine = engine();
        let compiled = Module::new(engine, emit::emit_hosted(module)).map_err(invalid)?;
        let mut imports = Vec::new();
        for (index, import) in module.imports.iter().enumerate() {
            let params = import.params.iter().map(|ty| val_type(*ty));
            let results = import.results.iter().map(|ty| val_type(*ty));
            let ty = FuncType::new(engine, params, results);
            let fail = move |_: wasmtime::Caller<'_, ()>, _: &[Val], _: &mut [Val]| {
                Err(wasmtime::Error::new(Imported(index as u32)))
            };
            imports.push(Extern::Func(Func::new(&mut self.store, ty, fail)));
        }
        let funcs = module.table.as_ref().map_or(0, |table| table.funcs.len());
        let size = self.table.size(&self.store);
        if let Some(more) = (funcs as u64 + 1)
            .checked_sub(size)
            .filter(|more| *more > 0)
        {
            let grown = self.table.grow(&mut self.store, more, Ref::Func(None));
            grown.map_err(invalid)?;
        }
        imports.push(Extern::Memory(self.memory));
        imports.push(Extern::Table(self.table));
        imports.extend(self.globals.iter().map(|global| Extern::Global(*global)));

        self.store.set_fuel(fuel).map_err(invalid)?;
        let instance = Instance::new(&mut self.store, &compiled, &imports).map_err(failure)?;
        let entry = instance.get_func(&mut self.store, ENTRY);
        let entry = entry.ok_or_else(|| invalid(format!("no function `{ENTRY}`")))?;
        let count = entry.ty(&self.store).results().len();
        let mut results = vec![Val::I32(0); count];
        entry
            .call(&mut self.store, &[], &mut results)
            .map_err(failure)?;
        Ok(results.iter().map(konst).collect())
    }

    /// What memory holds, as the fewest segments in address order that
    /// leave out most of its zeros: a module's memory starts zeroed.
    pub(crate) fn data(&self) -> Vec<ir::Data> {
        let memory = self.memory.data(&self.store);
        // Each run of bytes that aren't zero, and those within `MAX_GAP` of
        // one another.
        let mut runs: Vec<(usize, usize)> = Vec::new();
        for (index, block) in memory.chunks(BLOCK).enumerate() {
            if *block == [0; BLOCK][..block.len()] {
                continue;
            }
            for (i, _) in block.iter().enumerate().filter(|(_, byte)| **byte != 0) {
                let at = index * BLOCK + i;
                match runs.last_mut() {
                    Some((_, end)) if at - *end <= MAX_GAP => *end = at + 1,
                    _ => runs.push((at, at + 1)),
                }
            }
        }
        let segment = |(start, end): (usize, usize)| ir::Data {
            offset: start as u64,
            bytes: memory[start..end].to_vec(),
        };
        runs.into_iter().map(segment).collect()
    }
}

/// The engine every evaluator runs on, which is made once.
fn engine() -> &'static Engine {
    static ENGINE: OnceLock<Engine> = OnceLock::new();
    ENGINE.get_or_init(|| {
        let mut config = Config::new();
        config.consume_fuel(true);
        config.wasm_memory64(true);
        // A NaN has the same bits on every machine.
        config.cranelift_nan_canonicalization(true);
        Engine::new(&config).expect("the configuration is supported")
    })
}

/// A failure that isn't the running code's doing.
fn invalid(error: impl fmt::Display) -> Failure {
    Failure {
        kind: FailureKind::Invalid(format!("{error:#}")),
        stack: Vec::new(),
    }
}

/// Why running wasm stopped with `error`.
fn failure(error: wasmtime::Error) -> Failure {
    let kind = if let Some(Imported(index)) = error.downcast_ref() {
        FailureKind::Imported(*index)
    } else {
        match error.downcast_ref() {
            Some(Trap::OutOfFuel) => FailureKind::OutOfFuel,
            Some(Trap::UnreachableCodeReached) => FailureKind::Unreachable,
            Some(trap) => {
                let message = trap.to_string();
                let message = message.strip_prefix("wasm trap: ").unwrap_or(&message);
                FailureKind::Trap(message.to_string())
            }
            None => return invalid(error),
        }
    };
    let backtrace = error.downcast_ref::<WasmBacktrace>();
    let frames = backtrace.map_or(&[][..], WasmBacktrace::frames);
    Failure {
        kind,
        stack: frames.iter().map(|frame| frame.func_index()).collect(),
    }
}

fn val_type(ty: ValType) -> wasmtime::ValType {
    match ty {
        ValType::I32 => wasmtime::ValType::I32,
        ValType::I64 => wasmtime::ValType::I64,
        ValType::F32 => wasmtime::ValType::F32,
        ValType::F64 => wasmtime::ValType::F64,
        ValType::ExternRef => wasmtime::ValType::EXTERNREF,
    }
}

fn val(c: Const) -> Val {
    match c {
        Const::I32(x) => Val::I32(x),
        Const::I64(x) => Val::I64(x),
        Const::F32(x) => Val::F32(x.to_bits()),
        Const::F64(x) => Val::F64(x.to_bits()),
        Const::Null => Val::ExternRef(None),
    }
}

/// The constant `val` is. Only the host makes a reference that isn't null,
/// and it is never called.
fn konst(val: &Val) -> Const {
    match val {
        Val::I32(x) => Const::I32(*x),
        Val::I64(x) => Const::I64(*x),
        Val::F32(bits) => Const::F32(f32::from_bits(*bits)),
        Val::F64(bits) => Const::F64(f64::from_bits(*bits)),
        _ => Const::Null,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{BinOp, Expr, FuncId, GlobalId, LoadOp, LocalId, Stmt, StoreOp};

    /// A module of the functions `funcs`, the last of which is run, with a
    /// 32-bit memory and nothing else.
    fn module(funcs: Vec<ir::Func>) -> ir::Module {
        ir::Module {
            memory: ir::Memory {
                min_pages: 0,
                max_pages: None,
                memory64: false,
                export: "memory".to_string(),
            },
            data: Vec::new(),
            table: None,
            globals: Vec::new(),
            imports: Vec::new(),
            funcs,
            start: None,
        }
    }

    /// A function that takes nothing, returns `results` and runs `body`.
    fn func(name: &str, results: Vec<ValType>, body: Vec<Stmt>) -> ir::Func {
        ir::Func {
            name: name.to_string(),
            export: None,
            params: Vec::new(),
            results,
            locals: Vec::new(),
            body,
        }
    }

    /// The function a module runs, which returns `results` and runs `body`.
    fn entry(results: Vec<ValType>, body: Vec<Stmt>) -> ir::Func {
        ir::Func {
            export: Some(ENTRY.to_string()),
            ..func("entry", results, body)
        }
    }

    fn i32(x: i32) -> Expr {
        Expr::Const(Const::I32(x))
    }

    fn evaluator() -> Evaluator {
        Evaluator::new(false, 1, 4).unwrap()
    }

    fn store(addr: i32, value: Expr) -> Stmt {
        Stmt::Store {
            ty: ValType::I32,
            op: StoreOp::Store,
            offset: 0,
            addr: i32(addr),
            value,
        }
    }

    fn load(addr: i32) -> Expr {
        Expr::Load {
            ty: ValType::I32,
            op: LoadOp::Load,
            offset: 0,
            addr: Box::new(i32(addr)),
        }
    }

    #[test]
    fn runs_return_every_result() {
        let add = Expr::Binary(ValType::I32, BinOp::Add, Box::new(i32(2)), Box::new(i32(3)));
        let results = vec![add, Expr::Const(Const::F64(1.5)), Expr::Const(Const::Null)];
        let types = vec![ValType::I32, ValType::F64, ValType::ExternRef];
        let module = module(vec![entry(types, vec![Stmt::Return(results)])]);
        let (results, _) = evaluator().run(&module, 1000);
        assert_eq!(
            results,
            Ok(vec![Const::I32(5), Const::F64(1.5), Const::Null])
        );
    }

    #[test]
    fn runs_share_memory_globals_and_the_table() {
        let mut eval = evaluator();
        eval.add_global(&ir::Global {
            name: "count".to_string(),
            ty: ValType::I32,
            mutable: true,
            init: Const::I32(40),
            export: None,
        });
        eval.write(8, &[1, 0, 0, 0]);

        // Adds what memory holds to the global, and leaves a pointer to
        // `seven` in memory.
        let seven = func(
            "seven",
            vec![ValType::I32],
            vec![Stmt::Return(vec![i32(7)])],
        );
        let sum = Expr::Binary(
            ValType::I32,
            BinOp::Add,
            Box::new(Expr::Global(GlobalId(0))),
            Box::new(load(8)),
        );
        let first = entry(
            Vec::new(),
            vec![Stmt::SetGlobal(GlobalId(0), sum), store(16, i32(1))],
        );
        let mut first = module(vec![seven.clone(), first]);
        first.globals = vec![ir::Global {
            name: "count".to_string(),
            ty: ValType::I32,
            mutable: true,
            init: Const::I32(0),
            export: None,
        }];
        first.table = Some(ir::Table {
            table64: false,
            export: "table".to_string(),
            funcs: vec![FuncId(0)],
        });
        assert_eq!(eval.run(&first, 1000).0, Ok(Vec::new()));
        assert_eq!(eval.global(0), Const::I32(41));

        // Calls through the pointer that the first run left.
        let call = Expr::CallIndirect {
            ty: ir::FuncType {
                params: Vec::new(),
                results: vec![ValType::I32],
            },
            args: Vec::new(),
            index: Box::new(load(16)),
        };
        let second = entry(vec![ValType::I32], vec![Stmt::Return(vec![call])]);
        let mut second = module(vec![seven, second]);
        second.globals = first.globals.clone();
        second.table = first.table.clone();
        assert_eq!(eval.run(&second, 1000).0, Ok(vec![Const::I32(7)]));
    }

    #[test]
    fn memory_is_read_back_without_its_zeros() {
        let mut eval = evaluator();
        eval.write(4, &[1, 2]);
        // Within `MAX_GAP` of the bytes before it, and far from those after.
        eval.write(10, &[3]);
        assert!(eval.cover(70_000));
        eval.write(69_999, &[9]);
        let data = eval.data();
        let expected = [(4, vec![1, 2, 0, 0, 0, 0, 3]), (69_999, vec![9])];
        let expected = expected.map(|(offset, bytes)| ir::Data { offset, bytes });
        assert_eq!(data, expected);
        assert_eq!(eval.pages(), 2);
        eval.zero(4, 7);
        assert_eq!(eval.data().len(), 1);
    }

    #[test]
    fn memory_grows_no_further_than_its_limit() {
        let mut eval = evaluator();
        assert!(eval.cover(4 * PAGE_SIZE));
        assert!(!eval.cover(4 * PAGE_SIZE + 1));
        assert_eq!(eval.pages(), 4);
        let grow = Expr::MemoryGrow(Box::new(i32(1)));
        let module = module(vec![entry(
            vec![ValType::I32],
            vec![Stmt::Return(vec![grow])],
        )]);
        assert_eq!(eval.run(&module, 1000).0, Ok(vec![Const::I32(-1)]));
    }

    #[test]
    fn failures_name_the_functions_that_were_running() {
        let zero = Expr::Binary(
            ValType::I32,
            BinOp::DivS,
            Box::new(i32(1)),
            Box::new(i32(0)),
        );
        let divide = func("divide", vec![ValType::I32], vec![Stmt::Return(vec![zero])]);
        let call = Expr::Call(FuncId(0), Vec::new());
        let module = module(vec![
            divide,
            entry(vec![ValType::I32], vec![Stmt::Return(vec![call])]),
        ]);
        let (results, _) = evaluator().run(&module, 1000);
        let failure = results.unwrap_err();
        assert_eq!(
            failure.kind,
            FailureKind::Trap("integer divide by zero".to_string())
        );
        assert_eq!(failure.stack, [0, 1]);
    }

    #[test]
    fn unreachable_code_is_told_from_other_traps() {
        let module = module(vec![entry(Vec::new(), vec![Stmt::Unreachable])]);
        let (results, _) = evaluator().run(&module, 1000);
        assert_eq!(results.unwrap_err().kind, FailureKind::Unreachable);
    }

    #[test]
    fn fuel_bounds_a_run() {
        let spin = Stmt::Loop(vec![Stmt::Br(0)]);
        let endless = module(vec![entry(Vec::new(), vec![spin])]);
        let (results, left) = evaluator().run(&endless, 10_000);
        assert_eq!(results.unwrap_err().kind, FailureKind::OutOfFuel);
        assert_eq!(left, 0);

        // What a run leaves is given back.
        let set = Stmt::SetLocal(LocalId(0), i32(1));
        let mut cheap = entry(Vec::new(), vec![set]);
        cheap.locals = vec![ir::Local {
            name: "x".to_string(),
            ty: ValType::I32,
        }];
        let (results, left) = evaluator().run(&module(vec![cheap]), 10_000);
        assert_eq!(results, Ok(Vec::new()));
        assert!(left > 9_000 && left < 10_000, "{left}");
    }

    #[test]
    fn imported_functions_are_never_called() {
        let mut module = module(vec![entry(
            Vec::new(),
            vec![Stmt::Drop(Expr::Call(FuncId(1), vec![i32(1)]))],
        )]);
        let import = |name: &str| ir::Import {
            name: name.to_string(),
            module: "env".to_string(),
            field: name.to_string(),
            params: vec![ValType::I32],
            results: vec![ValType::I32],
        };
        module.imports = vec![import("first"), import("second")];
        let (results, _) = evaluator().run(&module, 1000);
        let failure = results.unwrap_err();
        assert_eq!(failure.kind, FailureKind::Imported(1));
        assert_eq!(failure.stack, [2]);
    }

    #[test]
    fn memories_and_tables_are_as_wide_as_addresses() {
        let mut eval = Evaluator::new(true, 1, 4).unwrap();
        let addr = Expr::Const(Const::I64(8));
        let write = Stmt::Store {
            ty: ValType::I64,
            op: StoreOp::Store,
            offset: 0,
            addr,
            value: Expr::MemorySize,
        };
        let mut module = module(vec![entry(Vec::new(), vec![write])]);
        module.memory.memory64 = true;
        assert_eq!(eval.run(&module, 1000).0, Ok(Vec::new()));
        assert_eq!(eval.data()[0].offset, 8);
    }
}

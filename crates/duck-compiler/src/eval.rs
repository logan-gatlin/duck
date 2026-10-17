//! Running lowered code while the program that holds it is compiled.
//!
//! An [`Evaluator`] is the state of the module being compiled, as its code
//! has left it so far: its memory, its table and its globals. Each
//! [`Evaluator::run`] is given a module that shares that state, as one that
//! [`crate::emit::emit_hosted`] encodes imports it, and calls the function it
//! exports as [`ENTRY`]. What the calls leave behind is what the compiled
//! module starts with.
//!
//! The code is interpreted, as wasm runs it: each function it calls is made
//! into a list of [`Step`]s the first time it is, which run on one stack of
//! values. Nothing is compiled for the machine, so it runs wherever the
//! compiler does, on a host that compiles no code as on any other.
//!
//! The code is sandboxed: it reaches nothing but the state, a call of an
//! imported function fails, fuel bounds how long it runs, and how deep it
//! calls is bounded too. Running it gives the same results on every machine:
//! a NaN that arithmetic makes is always the one NaN, and fuel is counted
//! by what the code is, never by how a machine runs it.

use std::mem;
use std::rc::Rc;

use crate::ir::{self, BinOp, Const, Expr, LoadOp, Stmt, StoreOp, UnOp, ValType};

/// The name a module exports the function to run as.
pub(crate) const ENTRY: &str = "run";

/// The bytes in a wasm page.
const PAGE_SIZE: u64 = 64 * 1024;

/// The most pages a 32-bit memory has.
const MAX_PAGES: u64 = 1 << 16;

/// The most calls that may be running at once, each within the one before.
const MAX_FRAMES: usize = 10_000;

/// The most values the stack holds, the locals of every call among them.
const MAX_VALUES: usize = 1 << 20;

/// The fuel that going into a function costs, beyond that of the step that
/// calls it: that of an instruction.
const ENTER_COST: u64 = 1;

/// The most of the functions that were running that a failure names,
/// innermost first: those of a call stack that is used up are many.
const MAX_FAILED_FRAMES: usize = 1000;

/// The NaN that arithmetic gives, whatever NaN it is given: a quiet one with
/// no sign and no payload.
const NAN32: u32 = 0x7fc0_0000;
const NAN64: u64 = 0x7ff8_0000_0000_0000;

/// The state of a module being compiled, which the code it runs shares.
pub(crate) struct Evaluator {
    /// Every byte of memory: as many as its pages have.
    memory: Vec<u8>,
    /// The most pages memory may grow to.
    max_pages: u64,
    /// The most pages the code it runs may grow memory to, with
    /// `memory.grow`: what is written into it may take it past them.
    grown_pages: u64,
    /// How many places the table has. Each run gives the places from 1 the
    /// functions its module's table holds, and nothing is at the others.
    table_size: u64,
    /// The module's globals, in [`ir::Module::globals`] order.
    globals: Vec<Const>,
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
    /// compiler.
    Invalid(String),
}

/// A function of the module being run, made into the steps it runs.
struct Code {
    steps: Vec<Step>,
    params: usize,
    /// How many locals it has after its parameters, which start as zeros.
    locals: usize,
    results: usize,
}

/// What a function does, one wasm instruction at a time, on the stack of
/// values. A value is held as its bits: those of an `i32` or an `f32` in the
/// low half, with zeros above them.
///
/// Each step costs the fuel of the wasm instruction it is: one, but for
/// those that only say where code goes and `drop`, which cost none. See
/// [`Step::cost`]. Going into a function costs one more, as does the call of
/// the entry that starts a run. `memory.fill` and `memory.copy` cost one more
/// for each byte they write, and `memory.grow` one more for each page it is
/// asked for, whether or not memory grows: so fuel bounds how long a run
/// takes, whatever it does.
#[derive(Debug, Clone, Copy)]
enum Step {
    Const(u64),
    LocalGet(u32),
    LocalSet(u32),
    GlobalGet(u32),
    GlobalSet(u32),
    Unary(ValType, UnOp),
    Binary(ValType, BinOp),
    Load(ValType, LoadOp, u32),
    Store(ValType, StoreOp, u32),
    MemorySize,
    MemoryGrow,
    MemoryFill,
    MemoryCopy,
    /// Calls the function of this index in the module.
    Call(u32),
    /// Calls the function at the place of the table that the value on top
    /// gives, which is of the type of this index in [`Run::types`].
    CallIndirect(u32),
    Drop,
    /// `br`: goes on at step `to`, with `keep` values on the stack above the
    /// locals, which is how many there were where its label is.
    Br {
        to: u32,
        keep: u32,
    },
    /// `br_if`: a [`Step::Br`] if the value on top isn't zero.
    BrIf {
        to: u32,
        keep: u32,
    },
    /// `if`: goes on at step `to`, past what runs if it holds, unless the
    /// value on top isn't zero.
    If(u32),
    /// `else`: the end of what runs if an `if` holds, which goes on past
    /// what runs if it doesn't, at step `to`.
    Else(u32),
    Return,
    Unreachable,
    /// The end of a function that has results, which every way through it
    /// returns before: no other reaches it.
    End,
}

/// A label that steps branch to, while a function is made into its steps.
struct Label {
    target: Target,
    /// How many values are on the stack above the locals where it is.
    height: u32,
}

enum Target {
    /// A `loop`, which a branch goes back to the start of, at this step.
    Start(u32),
    /// A `block` or an `if`, which a branch goes past the end of. Each of
    /// these steps is a branch to it, which is told where that is once it
    /// is known.
    End(Vec<usize>),
    /// An `if` that has a value, which no branch goes to: one takes no
    /// value with it.
    Valued,
}

/// Makes one function of a module into the steps it runs, and checks that
/// each step has the values it takes, as wasm is validated.
struct Compiler<'m> {
    module: &'m ir::Module,
    func: &'m ir::Func,
    types: &'m mut Vec<ir::FuncType>,
    steps: Vec<Step>,
    labels: Vec<Label>,
    /// How many values are on the stack above the locals.
    height: u32,
}

/// A call that is running.
struct Frame {
    /// Its function's index in the module.
    func: u32,
    code: Rc<Code>,
    /// The step it runs next.
    pc: usize,
    /// Where on the stack its locals start.
    base: usize,
}

/// One run of a module on an evaluator.
struct Run<'r> {
    module: &'r ir::Module,
    eval: &'r mut Evaluator,
    /// Each function the module defines, once a call has made it into steps.
    codes: Vec<Option<Rc<Code>>>,
    /// The types that `call_indirect`s ask the functions they call to have.
    types: Vec<ir::FuncType>,
    values: Vec<u64>,
    /// The calls that wait on the innermost, which isn't among them: but
    /// for after a failure, which leaves every call that was running here.
    frames: Vec<Frame>,
    fuel: u64,
}

/// What a run does after a step.
enum Flow {
    /// Runs the next step of the same call.
    Next,
    /// Calls the function of this index in the module, with its arguments on
    /// top of the stack.
    Call(u32),
    /// Returns from the innermost call, with its results where its locals
    /// started.
    Return,
}

/// Why a run stopped, before the functions that were running are known.
enum Stop {
    Trap(&'static str),
    Unreachable,
    OutOfFuel,
    Imported(u32),
    Invalid(String),
}

impl Evaluator {
    /// A memory of no pages that may grow to `max_pages`, and that the code
    /// run on it may grow to `grown_pages`, a table of one place and no
    /// globals.
    pub(crate) fn new(max_pages: u64, grown_pages: u64) -> Self {
        let max_pages = max_pages.min(MAX_PAGES);
        Self {
            memory: Vec::new(),
            max_pages,
            grown_pages: grown_pages.min(max_pages),
            table_size: 1,
            globals: Vec::new(),
        }
    }

    /// The size of memory, in pages.
    pub(crate) fn pages(&self) -> u64 {
        self.memory.len() as u64 / PAGE_SIZE
    }

    /// Grows memory to hold the address before `end`, unless it does.
    /// Returns whether it then does.
    pub(crate) fn cover(&mut self, end: u64) -> bool {
        let pages = end.div_ceil(PAGE_SIZE);
        pages <= self.pages() || self.grow(pages - self.pages(), self.max_pages).is_some()
    }

    /// Copies `bytes` to memory at `offset`, which holds them.
    pub(crate) fn write(&mut self, offset: u64, bytes: &[u8]) {
        self.memory[offset as usize..][..bytes.len()].copy_from_slice(bytes);
    }

    /// Zeroes the `len` bytes of memory at `offset`, which holds them.
    pub(crate) fn zero(&mut self, offset: u64, len: u64) {
        self.memory[offset as usize..][..len as usize].fill(0);
    }

    /// How many globals there are.
    pub(crate) fn global_count(&self) -> usize {
        self.globals.len()
    }

    /// Adds `global` after the others, as its initializer leaves it.
    pub(crate) fn add_global(&mut self, global: &ir::Global) {
        debug_assert_eq!(type_of(global.init), global.ty);
        self.globals.push(global.init);
    }

    /// What global `index` holds.
    pub(crate) fn global(&self, index: usize) -> Const {
        self.globals[index]
    }

    /// Calls the function that `module` exports as [`ENTRY`], which takes
    /// nothing, with `fuel` to run on. `module` has the globals that were
    /// added, in order, and its table is given the functions it holds.
    /// Returns the results, or why there are none, and the fuel left over:
    /// none once it ran out.
    pub(crate) fn run(
        &mut self,
        module: &ir::Module,
        fuel: u64,
    ) -> (Result<Vec<Const>, Failure>, u64) {
        let mut run = Run {
            module,
            eval: self,
            codes: vec![None; module.funcs.len()],
            types: Vec::new(),
            values: Vec::new(),
            frames: Vec::new(),
            fuel,
        };
        let results = run.start().map_err(|stop| run.failure(stop));
        let left = match &results {
            Err(Failure {
                kind: FailureKind::OutOfFuel,
                ..
            }) => 0,
            _ => run.fuel,
        };
        (results, left)
    }

    /// What memory holds, as one segment from the first of its bytes that
    /// isn't zero to the last: a module's memory starts zeroed.
    pub(crate) fn data(&self) -> Vec<ir::Data> {
        let Some(start) = self.memory.iter().position(|byte| *byte != 0) else {
            return Vec::new();
        };
        let end = self.memory.iter().rposition(|byte| *byte != 0).unwrap() + 1;
        vec![ir::Data {
            offset: start as u64,
            bytes: self.memory[start..end].to_vec(),
        }]
    }

    /// Adds `pages` to memory, as `memory.grow` does, unless that takes it
    /// past `limit` pages: none are added to memory that is past them
    /// already. Returns the size it had, if it grows.
    fn grow(&mut self, pages: u64, limit: u64) -> Option<u64> {
        let old = self.pages();
        let new = old
            .checked_add(pages)
            .filter(|new| *new <= limit.max(old))?;
        self.memory.resize((new * PAGE_SIZE) as usize, 0);
        Some(old)
    }

    /// Where in memory the `len` bytes at `addr + offset` start, if memory
    /// holds them all.
    fn at(&self, addr: u64, offset: u32, len: u64) -> Result<usize, Stop> {
        let start = (addr as u32 as u64) + u64::from(offset);
        match start + len <= self.memory.len() as u64 {
            true => Ok(start as usize),
            false => Err(Stop::Trap("out of bounds memory access")),
        }
    }

    fn load(&self, ty: ValType, op: LoadOp, offset: u32, addr: u64) -> Result<u64, Stop> {
        let len = match op {
            LoadOp::Load => width(ty),
            LoadOp::Load8S | LoadOp::Load8U => 1,
            LoadOp::Load16S | LoadOp::Load16U => 2,
        };
        let start = self.at(addr, offset, len)?;
        let mut bytes = [0; 8];
        bytes[..len as usize].copy_from_slice(&self.memory[start..][..len as usize]);
        let bits = u64::from_le_bytes(bytes);
        let wide = ty == ValType::I64;
        Ok(match op {
            LoadOp::Load | LoadOp::Load8U | LoadOp::Load16U => bits,
            LoadOp::Load8S => extend(bits as i8 as i64, wide),
            LoadOp::Load16S => extend(bits as i16 as i64, wide),
        })
    }

    fn store(
        &mut self,
        ty: ValType,
        op: StoreOp,
        offset: u32,
        addr: u64,
        value: u64,
    ) -> Result<(), Stop> {
        let len = match op {
            StoreOp::Store => width(ty),
            StoreOp::Store8 => 1,
            StoreOp::Store16 => 2,
        };
        let start = self.at(addr, offset, len)?;
        self.memory[start..][..len as usize].copy_from_slice(&value.to_le_bytes()[..len as usize]);
        Ok(())
    }
}

impl Step {
    /// The fuel the step costs, which is that of the wasm instruction it is:
    /// `block`, `loop`, `else`, `end`, `return`, `unreachable` and `drop`
    /// cost none, and every other instruction one.
    fn cost(self) -> u64 {
        match self {
            Self::Drop | Self::Else(_) | Self::Return | Self::Unreachable | Self::End => 0,
            _ => 1,
        }
    }
}

impl<'m> Compiler<'m> {
    /// The steps of function `func` of `module`, or why it can't be run.
    /// The types its `call_indirect`s ask for are added to `types`.
    fn compile(
        module: &'m ir::Module,
        func: &'m ir::Func,
        types: &'m mut Vec<ir::FuncType>,
    ) -> Result<Code, String> {
        let locals = func.locals.iter().map(|local| local.ty);
        if !locals
            .take(func.params.len())
            .eq(func.params.iter().copied())
        {
            return Err(format!(
                "`{}` has locals that aren't its parameters",
                func.name
            ));
        }
        let mut compiler = Self {
            module,
            func,
            types,
            steps: Vec::new(),
            labels: Vec::new(),
            height: 0,
        };
        compiler.stmts(&func.body)?;
        let end = match func.results.is_empty() {
            true => Step::Return,
            false => Step::End,
        };
        compiler.steps.push(end);
        Ok(Code {
            steps: compiler.steps,
            params: func.params.len(),
            locals: func.locals.len() - func.params.len(),
            results: func.results.len(),
        })
    }

    fn stmts(&mut self, body: &[Stmt]) -> Result<(), String> {
        body.iter().try_for_each(|stmt| self.stmt(stmt))
    }

    fn stmt(&mut self, stmt: &Stmt) -> Result<(), String> {
        match stmt {
            Stmt::SetLocal(local, value) => {
                let ty = self.local(local.0)?;
                self.expect(value, ty)?;
                self.step(Step::LocalSet(local.0), 1, 0);
            }
            Stmt::SetGlobal(global, value) => {
                let Some(def) = self.module.globals.get(global.0 as usize) else {
                    return Err(format!("no global {}", global.0));
                };
                if !def.mutable {
                    return Err(format!("global `{}` is immutable", def.name));
                }
                self.expect(value, def.ty)?;
                self.step(Step::GlobalSet(global.0), 1, 0);
            }
            Stmt::Store {
                ty,
                op,
                offset,
                addr,
                value,
            } => {
                if *op != StoreOp::Store && !is_int(*ty) {
                    return Err(format!("no store {ty:?}.{op:?}"));
                }
                self.expect(addr, ValType::I32)?;
                self.expect(value, *ty)?;
                self.step(Step::Store(*ty, *op, *offset), 2, 0);
            }
            Stmt::Drop(value) => {
                self.expr(value)?;
                self.step(Step::Drop, 1, 0);
            }
            Stmt::MemoryFill { dst, value, len } => {
                for operand in [dst, value, len] {
                    self.expect(operand, ValType::I32)?;
                }
                self.step(Step::MemoryFill, 3, 0);
            }
            Stmt::MemoryCopy { dst, src, len } => {
                for operand in [dst, src, len] {
                    self.expect(operand, ValType::I32)?;
                }
                self.step(Step::MemoryCopy, 3, 0);
            }
            Stmt::Call { func, args, dests } => {
                let ty = self.func_type(func.0)?;
                self.call_args(args, &ty.params)?;
                self.step(
                    Step::Call(func.0),
                    ty.params.len() as u32,
                    ty.results.len() as u32,
                );
                self.dests(dests, &ty.results)?;
            }
            Stmt::CallIndirect {
                ty,
                args,
                index,
                dests,
            } => {
                self.call_args(args, &ty.params)?;
                self.expect(index, ValType::I32)?;
                let id = self.type_id(ty);
                self.step(
                    Step::CallIndirect(id),
                    ty.params.len() as u32 + 1,
                    ty.results.len() as u32,
                );
                self.dests(dests, &ty.results)?;
            }
            Stmt::Block(body) => {
                self.open(Target::End(Vec::new()));
                self.stmts(body)?;
                self.close();
            }
            Stmt::Loop(body) => {
                self.open(Target::Start(self.steps.len() as u32));
                self.stmts(body)?;
                self.close();
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.expect(cond, ValType::I32)?;
                let test = self.steps.len();
                self.step(Step::If(0), 1, 0);
                self.open(Target::End(Vec::new()));
                self.stmts(then_body)?;
                match else_body.is_empty() {
                    true => self.mark_end(test),
                    false => {
                        let skip = self.steps.len();
                        self.steps.push(Step::Else(0));
                        self.mark_end(skip);
                        self.patch(test, self.steps.len());
                        self.stmts(else_body)?;
                    }
                }
                self.close();
            }
            Stmt::Br(depth) => {
                let step = self.branch(*depth, |to, keep| Step::Br { to, keep })?;
                self.steps.push(step);
            }
            Stmt::BrIf(depth, cond) => {
                self.expect(cond, ValType::I32)?;
                self.height -= 1;
                let step = self.branch(*depth, |to, keep| Step::BrIf { to, keep })?;
                self.steps.push(step);
            }
            Stmt::Return(values) => {
                let results = &self.func.results;
                if values.len() != results.len() {
                    return Err(format!("`{}` returns the wrong count", self.func.name));
                }
                for (value, ty) in values.iter().zip(results.clone()) {
                    self.expect(value, ty)?;
                }
                self.step(Step::Return, values.len() as u32, 0);
            }
            Stmt::Unreachable => self.steps.push(Step::Unreachable),
        }
        Ok(())
    }

    /// Makes `expr` into steps, which leave its value on the stack. Returns
    /// its type.
    fn expr(&mut self, expr: &Expr) -> Result<ValType, String> {
        let ty = match expr {
            Expr::Const(c) => {
                self.step(Step::Const(bits(*c)), 0, 1);
                type_of(*c)
            }
            Expr::Local(local) => {
                let ty = self.local(local.0)?;
                self.step(Step::LocalGet(local.0), 0, 1);
                ty
            }
            Expr::Global(global) => {
                let Some(def) = self.module.globals.get(global.0 as usize) else {
                    return Err(format!("no global {}", global.0));
                };
                self.step(Step::GlobalGet(global.0), 0, 1);
                def.ty
            }
            Expr::Unary(ty, op, x) => {
                self.expect(x, *ty)?;
                let result =
                    unary_type(*ty, *op).ok_or_else(|| format!("no instruction {ty:?}.{op:?}"))?;
                self.step(Step::Unary(*ty, *op), 1, 1);
                result
            }
            Expr::Binary(ty, op, a, b) => {
                self.expect(a, *ty)?;
                self.expect(b, *ty)?;
                let result =
                    binary_type(*ty, *op).ok_or_else(|| format!("no instruction {ty:?}.{op:?}"))?;
                self.step(Step::Binary(*ty, *op), 2, 1);
                result
            }
            Expr::Call(func, args) => {
                let ty = self.func_type(func.0)?;
                let [result] = ty.results[..] else {
                    return Err(format!("function {} has no one result", func.0));
                };
                self.call_args(args, &ty.params)?;
                self.step(Step::Call(func.0), ty.params.len() as u32, 1);
                result
            }
            Expr::CallIndirect { ty, args, index } => {
                let [result] = ty.results[..] else {
                    return Err("an indirect call has no one result".to_string());
                };
                self.call_args(args, &ty.params)?;
                self.expect(index, ValType::I32)?;
                let id = self.type_id(ty);
                self.step(Step::CallIndirect(id), ty.params.len() as u32 + 1, 1);
                result
            }
            Expr::Load {
                ty,
                op,
                offset,
                addr,
            } => {
                if *op != LoadOp::Load && !is_int(*ty) {
                    return Err(format!("no load {ty:?}.{op:?}"));
                }
                self.expect(addr, ValType::I32)?;
                self.step(Step::Load(*ty, *op, *offset), 1, 1);
                *ty
            }
            Expr::MemorySize => {
                self.step(Step::MemorySize, 0, 1);
                ValType::I32
            }
            Expr::MemoryGrow(pages) => {
                self.expect(pages, ValType::I32)?;
                self.step(Step::MemoryGrow, 1, 1);
                ValType::I32
            }
            Expr::If {
                ty,
                cond,
                then_expr,
                else_expr,
            } => {
                self.expect(cond, ValType::I32)?;
                let test = self.steps.len();
                self.step(Step::If(0), 1, 0);
                self.open(Target::Valued);
                self.expect(then_expr, *ty)?;
                let skip = self.steps.len();
                self.steps.push(Step::Else(0));
                // What runs if the test doesn't hold has the stack as it
                // was before the other's value.
                self.height -= 1;
                self.patch(test, self.steps.len());
                self.expect(else_expr, *ty)?;
                self.close();
                self.patch(skip, self.steps.len());
                *ty
            }
            Expr::Seq(body, value) => {
                self.stmts(body)?;
                self.expr(value)?
            }
            Expr::Symbol(..) => return Err("a module that isn't linked".to_string()),
        };
        Ok(ty)
    }

    /// Makes `expr` into steps, as [`Self::expr`] does, and checks that it
    /// is of type `ty`.
    fn expect(&mut self, expr: &Expr, ty: ValType) -> Result<(), String> {
        match self.expr(expr)? {
            found if found == ty => Ok(()),
            found => Err(format!("a {found:?} where a {ty:?} is expected")),
        }
    }

    fn call_args(&mut self, args: &[Expr], params: &[ValType]) -> Result<(), String> {
        if args.len() != params.len() {
            return Err(format!(
                "a call with {} arguments of {}",
                args.len(),
                params.len()
            ));
        }
        args.iter()
            .zip(params)
            .try_for_each(|(arg, ty)| self.expect(arg, *ty))
    }

    /// Stores the results of a call, the last of which is on top, to
    /// `dests` in order.
    fn dests(&mut self, dests: &[ir::LocalId], results: &[ValType]) -> Result<(), String> {
        if dests.len() != results.len() {
            return Err(format!(
                "a call of {} results stored to {}",
                results.len(),
                dests.len()
            ));
        }
        for (dest, ty) in dests.iter().zip(results).rev() {
            if self.local(dest.0)? != *ty {
                return Err(format!("a {ty:?} stored to a local of another type"));
            }
            self.step(Step::LocalSet(dest.0), 1, 0);
        }
        Ok(())
    }

    fn local(&self, index: u32) -> Result<ValType, String> {
        match self.func.locals.get(index as usize) {
            Some(local) => Ok(local.ty),
            None => Err(format!("`{}` has no local {index}", self.func.name)),
        }
    }

    /// The type of function `index` of the module, imported or not.
    fn func_type(&self, index: u32) -> Result<ir::FuncType, String> {
        match signature(self.module, index) {
            Some((params, results)) => Ok(ir::FuncType {
                params: params.to_vec(),
                results: results.to_vec(),
            }),
            None => Err(format!("no function {index}")),
        }
    }

    fn type_id(&mut self, ty: &ir::FuncType) -> u32 {
        match self.types.iter().position(|known| known == ty) {
            Some(id) => id as u32,
            None => {
                self.types.push(ty.clone());
                self.types.len() as u32 - 1
            }
        }
    }

    /// Adds `step`, which takes `pops` values off the stack and leaves
    /// `pushes`.
    fn step(&mut self, step: Step, pops: u32, pushes: u32) {
        self.height = self.height - pops + pushes;
        self.steps.push(step);
    }

    fn open(&mut self, target: Target) {
        self.labels.push(Label {
            target,
            height: self.height,
        });
    }

    /// Ends the innermost label, which every branch to its end now goes
    /// to.
    fn close(&mut self) {
        let label = self
            .labels
            .pop()
            .expect("every label that is closed was opened");
        if let Target::End(branches) = label.target {
            let end = self.steps.len();
            for branch in branches {
                self.patch(branch, end);
            }
        }
    }

    /// Has the branch at step `at` go to the end of the innermost label.
    fn mark_end(&mut self, at: usize) {
        match &mut self.labels.last_mut().expect("an `if` is a label").target {
            Target::End(branches) => branches.push(at),
            _ => unreachable!("an `if` without a value ends"),
        }
    }

    /// Has the branch at step `at` go to step `to`.
    fn patch(&mut self, at: usize, to: usize) {
        let to = to as u32;
        match &mut self.steps[at] {
            Step::Br { to: target, .. }
            | Step::BrIf { to: target, .. }
            | Step::If(target)
            | Step::Else(target) => *target = to,
            step => unreachable!("{step:?} is no branch"),
        }
    }

    /// A branch to the label `depth` out from the innermost, which `make`
    /// makes of where it goes and what it keeps on the stack.
    fn branch(&mut self, depth: u32, make: impl Fn(u32, u32) -> Step) -> Result<Step, String> {
        let at = self.steps.len();
        let Some(index) = self.labels.len().checked_sub(depth as usize + 1) else {
            return Err(format!("a branch out of {depth} labels of fewer"));
        };
        let label = &mut self.labels[index];
        let keep = label.height;
        match &mut label.target {
            Target::Start(start) => Ok(make(*start, keep)),
            Target::End(branches) => {
                branches.push(at);
                Ok(make(0, keep))
            }
            Target::Valued => Err("a branch to a label that has a value".to_string()),
        }
    }
}

impl Run<'_> {
    /// Checks that the module shares the state, and runs its entry.
    fn start(&mut self) -> Result<Vec<Const>, Stop> {
        let module = self.module;
        let globals = module.globals.iter().map(|global| global.ty);
        if !globals.eq(self.eval.globals.iter().map(|global| type_of(*global))) {
            return Err(Stop::Invalid("the globals are not the state's".to_string()));
        }
        let exported = |func: &ir::Func| func.exports.iter().any(|name| name == ENTRY);
        let Some(entry) = module.funcs.iter().position(exported) else {
            return Err(Stop::Invalid(format!("no function `{ENTRY}`")));
        };
        let func = &module.funcs[entry];
        if !func.params.is_empty() {
            return Err(Stop::Invalid(format!("`{ENTRY}` takes arguments")));
        }
        let funcs = module.table.as_ref().map_or(0, |table| table.funcs.len());
        self.eval.table_size = self.eval.table_size.max(funcs as u64 + 1);
        // The host calls the entry, which costs what a `call` does.
        self.burn(Step::Call(0).cost())?;
        let results = self.call((module.imports.len() + entry) as u32)?;
        let consts = results.into_iter().zip(&func.results);
        Ok(consts.map(|(bits, ty)| konst(bits, *ty)).collect())
    }

    /// The failure that `stop` is, with the functions that were running.
    fn failure(&self, stop: Stop) -> Failure {
        let kind = match stop {
            Stop::Trap(trap) => FailureKind::Trap(trap.to_string()),
            Stop::Unreachable => FailureKind::Unreachable,
            Stop::OutOfFuel => FailureKind::OutOfFuel,
            Stop::Imported(index) => FailureKind::Imported(index),
            Stop::Invalid(why) => FailureKind::Invalid(why),
        };
        let frames = self.frames.iter().rev().take(MAX_FAILED_FRAMES);
        Failure {
            kind,
            stack: frames.map(|frame| frame.func).collect(),
        }
    }

    /// Calls function `index` of the module, which takes nothing, and runs
    /// until it returns. Returns its results. If it fails, the functions
    /// that were running are left in [`Self::frames`].
    fn call(&mut self, index: u32) -> Result<Vec<u64>, Stop> {
        let mut frame = self.frame(index)?;
        loop {
            let done = self.step(&mut frame);
            match done {
                Ok(Flow::Next) => {}
                Ok(Flow::Call(callee)) => match self.frame(callee) {
                    Ok(callee) => self.frames.push(mem::replace(&mut frame, callee)),
                    Err(stop) => {
                        self.frames.push(frame);
                        return Err(stop);
                    }
                },
                Ok(Flow::Return) => match self.frames.pop() {
                    Some(caller) => frame = caller,
                    None => return Ok(mem::take(&mut self.values)),
                },
                Err(stop) => {
                    self.frames.push(frame);
                    return Err(stop);
                }
            }
        }
    }

    /// Runs the next step of `frame`, the innermost call.
    fn step(&mut self, frame: &mut Frame) -> Result<Flow, Stop> {
        let step = frame.code.steps[frame.pc];
        self.burn(step.cost())?;
        frame.pc += 1;
        match step {
            Step::Const(bits) => self.values.push(bits),
            Step::LocalGet(local) => self.values.push(self.values[frame.base + local as usize]),
            Step::LocalSet(local) => {
                let value = self.pop();
                self.values[frame.base + local as usize] = value;
            }
            Step::GlobalGet(global) => self.values.push(bits(self.eval.globals[global as usize])),
            Step::GlobalSet(global) => {
                let value = self.pop();
                let held = &mut self.eval.globals[global as usize];
                *held = konst(value, type_of(*held));
            }
            Step::Unary(ty, op) => {
                let x = self.top();
                *x = unary(ty, op, *x);
            }
            Step::Binary(ty, op) => {
                let b = self.pop();
                let a = self.top();
                *a = binary(ty, op, *a, b)?;
            }
            Step::Load(ty, op, offset) => {
                let addr = self.pop();
                let value = self.eval.load(ty, op, offset, addr)?;
                self.values.push(value);
            }
            Step::Store(ty, op, offset) => {
                let value = self.pop();
                let addr = self.pop();
                self.eval.store(ty, op, offset, addr, value)?;
            }
            Step::MemorySize => self.values.push(self.eval.pages()),
            Step::MemoryGrow => {
                let pages = self.pop() as u32;
                self.burn(u64::from(pages))?;
                let old = self.eval.grow(u64::from(pages), self.eval.grown_pages);
                self.values.push(old.unwrap_or(u64::from(u32::MAX)));
            }
            Step::MemoryFill => {
                let len = self.pop() as u32;
                let value = self.pop() as u8;
                let dst = self.pop();
                self.burn(u64::from(len))?;
                let start = self.eval.at(dst, 0, u64::from(len))?;
                self.eval.memory[start..][..len as usize].fill(value);
            }
            Step::MemoryCopy => {
                let len = self.pop() as u32;
                let src = self.pop();
                let dst = self.pop();
                self.burn(u64::from(len))?;
                let from = self.eval.at(src, 0, u64::from(len))?;
                let to = self.eval.at(dst, 0, u64::from(len))?;
                self.eval.memory.copy_within(from..from + len as usize, to);
            }
            Step::Call(callee) => return Ok(Flow::Call(callee)),
            Step::CallIndirect(ty) => {
                let place = self.pop() as u32;
                return Ok(Flow::Call(self.callee(place, ty)?));
            }
            Step::Drop => {
                self.pop();
            }
            Step::Br { to, keep } => self.branch(frame, to, keep),
            Step::BrIf { to, keep } => {
                if self.pop() as u32 != 0 {
                    self.branch(frame, to, keep);
                }
            }
            Step::If(to) => {
                if self.pop() as u32 == 0 {
                    frame.pc = to as usize;
                }
            }
            Step::Else(to) => frame.pc = to as usize,
            Step::Return => {
                let results = frame.code.results;
                let from = self.values.len() - results;
                self.values.copy_within(from.., frame.base);
                self.values.truncate(frame.base + results);
                return Ok(Flow::Return);
            }
            Step::Unreachable => return Err(Stop::Unreachable),
            Step::End => {
                let why = format!("function {} ends without its results", frame.func);
                return Err(Stop::Invalid(why));
            }
        }
        Ok(Flow::Next)
    }

    /// Goes on at step `to` of `frame`, with `keep` values on the stack
    /// above its locals.
    fn branch(&mut self, frame: &mut Frame, to: u32, keep: u32) {
        let floor = frame.base + frame.code.params + frame.code.locals;
        self.values.truncate(floor + keep as usize);
        frame.pc = to as usize;
    }

    /// The frame of a call of function `index` of the module, with its
    /// arguments on top of the stack and zeros for its other locals pushed
    /// after them, unless the function is imported or the stack is full.
    fn frame(&mut self, index: u32) -> Result<Frame, Stop> {
        if (index as usize) < self.module.imports.len() {
            return Err(Stop::Imported(index));
        }
        self.burn(ENTER_COST)?;
        let code = self.code(index)?;
        // The frame of the innermost call isn't among them.
        let full = self.frames.len() + 2 > MAX_FRAMES;
        if full || self.values.len() + code.locals > MAX_VALUES {
            return Err(Stop::Trap("call stack exhausted"));
        }
        let base = self.values.len() - code.params;
        self.values.resize(self.values.len() + code.locals, 0);
        Ok(Frame {
            func: index,
            code,
            pc: 0,
            base,
        })
    }

    /// The steps of function `index` of the module, which it defines.
    fn code(&mut self, index: u32) -> Result<Rc<Code>, Stop> {
        let defined = index as usize - self.module.imports.len();
        if let Some(code) = &self.codes[defined] {
            return Ok(code.clone());
        }
        let func = &self.module.funcs[defined];
        let code = Compiler::compile(self.module, func, &mut self.types).map_err(Stop::Invalid)?;
        let code = Rc::new(code);
        self.codes[defined] = Some(code.clone());
        Ok(code)
    }

    /// The function at `place` in the table, which is to be of type `ty`.
    fn callee(&self, place: u32, ty: u32) -> Result<u32, Stop> {
        if u64::from(place) >= self.eval.table_size {
            return Err(Stop::Trap("undefined element: out of bounds table access"));
        }
        let funcs = self
            .module
            .table
            .as_ref()
            .map_or(&[][..], |table| &table.funcs[..]);
        let Some(callee) = (place as usize).checked_sub(1).and_then(|i| funcs.get(i)) else {
            return Err(Stop::Trap("uninitialized element"));
        };
        let ty = &self.types[ty as usize];
        match signature(self.module, callee.0) {
            Some((params, results)) if params == ty.params && results == ty.results => Ok(callee.0),
            Some(_) => Err(Stop::Trap("indirect call type mismatch")),
            None => Err(Stop::Invalid(format!(
                "the table has no function {}",
                callee.0
            ))),
        }
    }

    /// Uses `fuel` of what is left, if that much is.
    fn burn(&mut self, fuel: u64) -> Result<(), Stop> {
        self.fuel = self.fuel.checked_sub(fuel).ok_or(Stop::OutOfFuel)?;
        Ok(())
    }

    fn pop(&mut self) -> u64 {
        self.values.pop().expect("a step has the values it takes")
    }

    fn top(&mut self) -> &mut u64 {
        self.values
            .last_mut()
            .expect("a step has the values it takes")
    }
}

/// What function `index` of `module` takes and what it returns, imported
/// or not, if there is that function.
fn signature(module: &ir::Module, index: u32) -> Option<(&[ValType], &[ValType])> {
    let index = index as usize;
    match index.checked_sub(module.imports.len()) {
        None => {
            let import = &module.imports[index];
            Some((&import.params, &import.results))
        }
        Some(defined) => {
            let func = module.funcs.get(defined)?;
            Some((&func.params, &func.results))
        }
    }
}

fn is_int(ty: ValType) -> bool {
    matches!(ty, ValType::I32 | ValType::I64)
}

/// The bytes of a value of type `ty`.
fn width(ty: ValType) -> u64 {
    match ty {
        ValType::I32 | ValType::F32 => 4,
        ValType::I64 | ValType::F64 => 8,
    }
}

/// The bits of `x`, which is extended to 64 bits, as an `i64` if `wide` and
/// as an `i32` otherwise.
fn extend(x: i64, wide: bool) -> u64 {
    match wide {
        true => x as u64,
        false => x as i32 as u32 as u64,
    }
}

/// The type of the constant `c`.
pub(crate) fn type_of(c: Const) -> ValType {
    match c {
        Const::I32(_) => ValType::I32,
        Const::I64(_) => ValType::I64,
        Const::F32(_) => ValType::F32,
        Const::F64(_) => ValType::F64,
    }
}

/// The bits a value of `c` is held as.
fn bits(c: Const) -> u64 {
    match c {
        Const::I32(x) => x as u32 as u64,
        Const::I64(x) => x as u64,
        Const::F32(x) => x.to_bits() as u64,
        Const::F64(x) => x.to_bits(),
    }
}

/// The constant of type `ty` that is held as `bits`.
fn konst(bits: u64, ty: ValType) -> Const {
    match ty {
        ValType::I32 => Const::I32(bits as u32 as i32),
        ValType::I64 => Const::I64(bits as i64),
        ValType::F32 => Const::F32(f32::from_bits(bits as u32)),
        ValType::F64 => Const::F64(f64::from_bits(bits)),
    }
}

/// What `<ty>.<op>` gives of the constant `x`, as a run does, if there is
/// that instruction: so a constant that is folded is what running it makes,
/// to its last bit, wherever it is folded.
pub(crate) fn fold_unary(ty: ValType, op: UnOp, x: Const) -> Option<Const> {
    let result = unary_type(ty, op).filter(|_| type_of(x) == ty)?;
    Some(konst(unary(ty, op, bits(x)), result))
}

/// What `<ty>.<op>` gives of the constants `a` and `b`, as a run does, if
/// there is that instruction. `Err` if it traps.
pub(crate) fn fold_binary(ty: ValType, op: BinOp, a: Const, b: Const) -> Option<Result<Const, ()>> {
    let typed = type_of(a) == ty && type_of(b) == ty;
    let result = binary_type(ty, op).filter(|_| typed)?;
    let value = binary(ty, op, bits(a), bits(b));
    Some(value.map(|bits| konst(bits, result)).map_err(|_| ()))
}

/// The type of `<ty>.<op>`, if there is that instruction.
pub(crate) fn unary_type(ty: ValType, op: UnOp) -> Option<ValType> {
    use UnOp::*;
    use ValType::*;
    Some(match (ty, op) {
        (I32 | I64, Eqz) => I32,
        (I32 | I64, Clz | Ctz | Extend8S | Extend16S) => ty,
        (F32 | F64, Neg) => ty,
        (I64, Wrap) => I32,
        (I32, ExtendS | ExtendU) => I64,
        (F32 | F64, TruncSatS(to @ (I32 | I64)) | TruncSatU(to @ (I32 | I64))) => to,
        (I32 | I64, ConvertS(to @ (F32 | F64)) | ConvertU(to @ (F32 | F64))) => to,
        (F64, Demote) => F32,
        (F32, Promote) => F64,
        (I32, Reinterpret) => F32,
        (I64, Reinterpret) => F64,
        (F32, Reinterpret) => I32,
        (F64, Reinterpret) => I64,
        _ => return None,
    })
}

/// The type of `<ty>.<op>`, if there is that instruction.
fn binary_type(ty: ValType, op: BinOp) -> Option<ValType> {
    use BinOp::*;
    use ValType::*;
    let int = matches!(ty, I32 | I64);
    Some(match op {
        Add | Sub | Mul => ty,
        DivS | DivU | RemS | RemU | And | Or | Xor | Shl | ShrS | ShrU if int => ty,
        Div | Min | Max if !int => ty,
        Eq | Ne => I32,
        LtS | LtU | LeS | LeU | GtS | GtU | GeS | GeU if int => I32,
        Lt | Le | Gt | Ge if !int => I32,
        _ => return None,
    })
}

/// `<ty>.<op>` of the value held as `x`.
fn unary(ty: ValType, op: UnOp, x: u64) -> u64 {
    use UnOp::*;
    use ValType::*;
    let (i32, i64) = (x as u32 as i32, x as i64);
    let (f32, f64) = (f32::from_bits(x as u32), f64::from_bits(x));
    match (ty, op) {
        (I32, Eqz) => (i32 == 0) as u64,
        (I64, Eqz) => (i64 == 0) as u64,
        (I32, Clz) => u64::from(i32.leading_zeros()),
        (I64, Clz) => u64::from(i64.leading_zeros()),
        (I32, Ctz) => u64::from(i32.trailing_zeros()),
        (I64, Ctz) => u64::from(i64.trailing_zeros()),
        // Only the sign is changed, of a NaN as of any other.
        (F32, Neg) => u64::from(x as u32 ^ 1 << 31),
        (F64, Neg) => x ^ 1 << 63,
        (I32, Extend8S) => extend(i32 as i8 as i64, false),
        (I32, Extend16S) => extend(i32 as i16 as i64, false),
        (I64, Extend8S) => i64 as i8 as i64 as u64,
        (I64, Extend16S) => i64 as i16 as i64 as u64,
        (I64, Wrap) => x as u32 as u64,
        (I32, ExtendS) => i32 as i64 as u64,
        (I32, ExtendU) => x as u32 as u64,
        // A conversion with `as` saturates, and takes NaN to zero, as
        // `trunc_sat` does.
        (F32, TruncSatS(I32)) => extend(f32 as i32 as i64, false),
        (F32, TruncSatU(I32)) => u64::from(f32 as u32),
        (F64, TruncSatS(I32)) => extend(f64 as i32 as i64, false),
        (F64, TruncSatU(I32)) => u64::from(f64 as u32),
        (F32, TruncSatS(I64)) => f32 as i64 as u64,
        (F32, TruncSatU(I64)) => f32 as u64,
        (F64, TruncSatS(I64)) => f64 as i64 as u64,
        (F64, TruncSatU(I64)) => f64 as u64,
        // One with `as` rounds to the nearest, and to even between two.
        (I32, ConvertS(F32)) => f32_bits(i32 as f32),
        (I32, ConvertU(F32)) => f32_bits(i32 as u32 as f32),
        (I64, ConvertS(F32)) => f32_bits(i64 as f32),
        (I64, ConvertU(F32)) => f32_bits(i64 as u64 as f32),
        (I32, ConvertS(F64)) => (i32 as f64).to_bits(),
        (I32, ConvertU(F64)) => (i32 as u32 as f64).to_bits(),
        (I64, ConvertS(F64)) => (i64 as f64).to_bits(),
        (I64, ConvertU(F64)) => (i64 as u64 as f64).to_bits(),
        (F64, Demote) => f32_bits(f64 as f32),
        (F32, Promote) => f64_bits(f32 as f64),
        // The bits are the same, whichever type holds them.
        (I32 | I64 | F32 | F64, Reinterpret) => x,
        _ => unreachable!("validated"),
    }
}

/// `<ty>.<op>` of the values held as `a` and `b`, or the trap it is.
fn binary(ty: ValType, op: BinOp, a: u64, b: u64) -> Result<u64, Stop> {
    use BinOp::*;
    use ValType::*;
    const ZERO: Stop = Stop::Trap("integer divide by zero");
    const OVERFLOW: Stop = Stop::Trap("integer overflow");
    let bool = |x: bool| x as u64;
    Ok(match ty {
        I32 => {
            let (a, b) = (a as u32 as i32, b as u32 as i32);
            let (ua, ub) = (a as u32, b as u32);
            let int = |x: i32| x as u32 as u64;
            match op {
                Add => int(a.wrapping_add(b)),
                Sub => int(a.wrapping_sub(b)),
                Mul => int(a.wrapping_mul(b)),
                DivS if b == 0 => return Err(ZERO),
                DivS => int(a.checked_div(b).ok_or(OVERFLOW)?),
                DivU => u64::from(ua.checked_div(ub).ok_or(ZERO)?),
                RemS if b == 0 => return Err(ZERO),
                RemS => int(a.wrapping_rem(b)),
                RemU => u64::from(ua.checked_rem(ub).ok_or(ZERO)?),
                And => int(a & b),
                Or => int(a | b),
                Xor => int(a ^ b),
                Shl => int(a.wrapping_shl(ub)),
                ShrS => int(a.wrapping_shr(ub)),
                ShrU => u64::from(ua.wrapping_shr(ub)),
                Eq => bool(a == b),
                Ne => bool(a != b),
                LtS => bool(a < b),
                LtU => bool(ua < ub),
                LeS => bool(a <= b),
                LeU => bool(ua <= ub),
                GtS => bool(a > b),
                GtU => bool(ua > ub),
                GeS => bool(a >= b),
                GeU => bool(ua >= ub),
                _ => unreachable!("validated"),
            }
        }
        I64 => {
            let (a, b) = (a as i64, b as i64);
            let (ua, ub) = (a as u64, b as u64);
            let int = |x: i64| x as u64;
            match op {
                Add => int(a.wrapping_add(b)),
                Sub => int(a.wrapping_sub(b)),
                Mul => int(a.wrapping_mul(b)),
                DivS if b == 0 => return Err(ZERO),
                DivS => int(a.checked_div(b).ok_or(OVERFLOW)?),
                DivU => ua.checked_div(ub).ok_or(ZERO)?,
                RemS if b == 0 => return Err(ZERO),
                RemS => int(a.wrapping_rem(b)),
                RemU => ua.checked_rem(ub).ok_or(ZERO)?,
                And => int(a & b),
                Or => int(a | b),
                Xor => int(a ^ b),
                Shl => int(a.wrapping_shl(ub as u32)),
                ShrS => int(a.wrapping_shr(ub as u32)),
                ShrU => ua.wrapping_shr(ub as u32),
                Eq => bool(a == b),
                Ne => bool(a != b),
                LtS => bool(a < b),
                LtU => bool(ua < ub),
                LeS => bool(a <= b),
                LeU => bool(ua <= ub),
                GtS => bool(a > b),
                GtU => bool(ua > ub),
                GeS => bool(a >= b),
                GeU => bool(ua >= ub),
                _ => unreachable!("validated"),
            }
        }
        F32 => {
            let (a, b) = (f32::from_bits(a as u32), f32::from_bits(b as u32));
            match op {
                Add => f32_bits(a + b),
                Sub => f32_bits(a - b),
                Mul => f32_bits(a * b),
                Div => f32_bits(a / b),
                Min => f32_bits(min(a.into(), b.into()) as f32),
                Max => f32_bits(max(a.into(), b.into()) as f32),
                Eq => bool(a == b),
                Ne => bool(a != b),
                Lt => bool(a < b),
                Le => bool(a <= b),
                Gt => bool(a > b),
                Ge => bool(a >= b),
                _ => unreachable!("validated"),
            }
        }
        F64 => {
            let (a, b) = (f64::from_bits(a), f64::from_bits(b));
            match op {
                Add => f64_bits(a + b),
                Sub => f64_bits(a - b),
                Mul => f64_bits(a * b),
                Div => f64_bits(a / b),
                Min => f64_bits(min(a, b)),
                Max => f64_bits(max(a, b)),
                Eq => bool(a == b),
                Ne => bool(a != b),
                Lt => bool(a < b),
                Le => bool(a <= b),
                Gt => bool(a > b),
                Ge => bool(a >= b),
                _ => unreachable!("validated"),
            }
        }
    })
}

/// The bits of `x`, or of the one NaN if it is one.
fn f32_bits(x: f32) -> u64 {
    match x.is_nan() {
        true => u64::from(NAN32),
        false => u64::from(x.to_bits()),
    }
}

/// The bits of `x`, or of the one NaN if it is one.
fn f64_bits(x: f64) -> u64 {
    match x.is_nan() {
        true => NAN64,
        false => x.to_bits(),
    }
}

/// `min`, as wasm has it: NaN if either is, and `-0` below `0`. An `f32`
/// is exactly an `f64`, so is compared as one.
fn min(a: f64, b: f64) -> f64 {
    match () {
        _ if a.is_nan() || b.is_nan() => f64::NAN,
        _ if a == b => f64::from_bits(a.to_bits() | b.to_bits()),
        _ => a.min(b),
    }
}

/// `max`, as wasm has it: NaN if either is, and `0` above `-0`.
fn max(a: f64, b: f64) -> f64 {
    match () {
        _ if a.is_nan() || b.is_nan() => f64::NAN,
        _ if a == b => f64::from_bits(a.to_bits() & b.to_bits()),
        _ => a.max(b),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{FuncId, GlobalId, LocalId};

    /// A module of the functions `funcs`, the last of which is run, with a
    /// 32-bit memory and nothing else.
    fn module(funcs: Vec<ir::Func>) -> ir::Module {
        ir::Module {
            memory: ir::Memory {
                min_pages: 0,
                max_pages: None,
                export: "memory".to_string(),
            },
            data: Vec::new(),
            table: None,
            globals: Vec::new(),
            imports: Vec::new(),
            funcs,
        }
    }

    /// A function that takes nothing, returns `results` and runs `body`.
    fn func(name: &str, results: Vec<ValType>, body: Vec<Stmt>) -> ir::Func {
        ir::Func {
            name: name.to_string(),
            exports: Vec::new(),
            params: Vec::new(),
            results,
            locals: Vec::new(),
            body,
        }
    }

    /// The function a module runs, which returns `results` and runs `body`.
    fn entry(results: Vec<ValType>, body: Vec<Stmt>) -> ir::Func {
        ir::Func {
            exports: vec![ENTRY.to_string()],
            ..func("entry", results, body)
        }
    }

    fn i32(x: i32) -> Expr {
        Expr::Const(Const::I32(x))
    }

    /// An evaluator whose memory has one page and may grow to four.
    fn evaluator() -> Evaluator {
        let mut eval = Evaluator::new(4, 4);
        assert!(eval.cover(PAGE_SIZE));
        eval
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
        let results = vec![add, Expr::Const(Const::F64(1.5))];
        let types = vec![ValType::I32, ValType::F64];
        let module = module(vec![entry(types, vec![Stmt::Return(results)])]);
        let (results, _) = evaluator().run(&module, 1000);
        assert_eq!(results, Ok(vec![Const::I32(5), Const::F64(1.5)]));
    }

    #[test]
    fn runs_share_memory_globals_and_the_table() {
        let mut eval = evaluator();
        eval.add_global(&ir::Global {
            name: "count".to_string(),
            ty: ValType::I32,
            mutable: true,
            init: Const::I32(40),
            exports: Vec::new(),
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
            exports: Vec::new(),
        }];
        first.table = Some(ir::Table {
            export: Some("table".to_string()),
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
    fn memory_is_read_back_as_one_segment_without_the_zeros_around_it() {
        let mut eval = evaluator();
        assert_eq!(eval.data(), []);
        eval.write(4, &[1, 2]);
        assert!(eval.cover(70_000));
        eval.write(69_999, &[9]);
        let data = eval.data();
        assert_eq!(data.len(), 1);
        assert_eq!((data[0].offset, data[0].bytes.len()), (4, 69_996));
        assert_eq!(
            (&data[0].bytes[..3], &data[0].bytes[69_995..]),
            (&[1, 2, 0][..], &[9][..])
        );
        assert_eq!(eval.pages(), 2);
        eval.zero(69_999, 1);
        let expected = ir::Data {
            offset: 4,
            bytes: vec![1, 2],
        };
        assert_eq!(eval.data(), [expected]);
    }

    #[test]
    fn code_grows_memory_no_further_than_its_own_limit() {
        // Two pages may be written, and the code takes no third.
        let mut eval = Evaluator::new(4, 2);
        assert!(eval.cover(PAGE_SIZE));
        let grow = |pages| {
            let grow = Expr::MemoryGrow(Box::new(i32(pages)));
            module(vec![entry(
                vec![ValType::I32],
                vec![Stmt::Return(vec![grow])],
            )])
        };
        assert_eq!(eval.run(&grow(2), 1000).0, Ok(vec![Const::I32(-1)]));
        assert_eq!(eval.run(&grow(1), 1000).0, Ok(vec![Const::I32(1)]));
        assert_eq!(eval.run(&grow(1), 1000).0, Ok(vec![Const::I32(-1)]));
        // What is written goes past them, to the limit of memory.
        assert!(eval.cover(4 * PAGE_SIZE));
        assert_eq!(eval.run(&grow(0), 1000).0, Ok(vec![Const::I32(4)]));
        assert!(!eval.cover(4 * PAGE_SIZE + 1));
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
}

/// The evaluator checked against Wasmtime, a wasm engine that compiles what
/// it runs for the machine, as the evaluator once was: the two are to run
/// every module alike, to each bit of what they leave, each step of the fuel
/// and each function that was running where one failed.
#[cfg(test)]
mod against_wasmtime {
    use wasmtime::{
        Config, Engine, Extern, Func, GlobalType, Instance, Memory, MemoryType, Module, Mutability,
        Ref, RefType, Store, Table, TableType, Trap, Val, WasmBacktrace,
    };

    use super::*;
    use crate::emit;
    use crate::ir::{FuncId, FuncType, GlobalId, LocalId};

    /// The evaluator as it was: the state of the module, held by Wasmtime.
    struct Reference {
        store: Store<()>,
        memory: Memory,
        table: Table,
        globals: Vec<wasmtime::Global>,
    }

    /// The error a call of an imported function fails with.
    #[derive(Debug)]
    struct Imported(u32);

    /// Values of each type that operators treat apart from others, as bits.
    struct Edges;

    /// A small, seeded source of choices.
    struct Rng(u64);

    /// Makes modules of what the evaluator runs, at random, that end: a
    /// loop runs a few times, and a function calls none after it.
    struct Gen {
        rng: Rng,
        /// The types of the functions made so far, of which those a call may
        /// make are those before the one being made.
        sigs: Vec<FuncType>,
        /// The locals of the function being made.
        locals: Vec<ValType>,
        params: usize,
        results: Vec<ValType>,
        /// Whether each label around what is being made is one that a branch
        /// may go to: a `block` or an `if`, and no `loop`, which would run
        /// again, or `if` that has a value.
        labels: Vec<bool>,
        /// How deep what is being made is.
        depth: u32,
    }

    impl std::fmt::Display for Imported {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "call of imported function {}", self.0)
        }
    }

    impl std::error::Error for Imported {}

    impl Reference {
        fn new(max_pages: u64) -> Self {
            let mut store = Store::new(engine(), ());
            let memory = MemoryType::new(0, Some(max_pages as u32));
            let table = TableType::new(RefType::FUNCREF, 1, None);
            let memory = Memory::new(&mut store, memory).unwrap();
            let table = Table::new(&mut store, table, Ref::Func(None)).unwrap();
            Self {
                store,
                memory,
                table,
                globals: Vec::new(),
            }
        }

        fn cover(&mut self, end: u64) -> bool {
            let pages = end.div_ceil(PAGE_SIZE);
            let size = self.memory.size(&self.store);
            pages <= size || self.memory.grow(&mut self.store, pages - size).is_ok()
        }

        fn write(&mut self, offset: u64, bytes: &[u8]) {
            let data = self.memory.data_mut(&mut self.store);
            data[offset as usize..][..bytes.len()].copy_from_slice(bytes);
        }

        fn add_global(&mut self, global: &ir::Global) {
            let mutability = match global.mutable {
                true => Mutability::Var,
                false => Mutability::Const,
            };
            let ty = GlobalType::new(val_type(global.ty), mutability);
            let global = wasmtime::Global::new(&mut self.store, ty, val(global.init));
            self.globals.push(global.unwrap());
        }

        fn global(&mut self, index: usize) -> Const {
            from_val(&self.globals[index].get(&mut self.store))
        }

        fn run(&mut self, module: &ir::Module, fuel: u64) -> (Result<Vec<Const>, Failure>, u64) {
            let results = self.call(module, fuel);
            (results, self.store.get_fuel().unwrap_or(0))
        }

        fn call(&mut self, module: &ir::Module, fuel: u64) -> Result<Vec<Const>, Failure> {
            let engine = engine();
            let compiled = Module::new(engine, emit::emit_hosted(module)).unwrap();
            let mut imports = Vec::new();
            for (index, import) in module.imports.iter().enumerate() {
                let params = import.params.iter().map(|ty| val_type(*ty));
                let results = import.results.iter().map(|ty| val_type(*ty));
                let ty = wasmtime::FuncType::new(engine, params, results);
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
                self.table
                    .grow(&mut self.store, more, Ref::Func(None))
                    .unwrap();
            }
            imports.push(Extern::Memory(self.memory));
            imports.push(Extern::Table(self.table));
            imports.extend(self.globals.iter().map(|global| Extern::Global(*global)));
            self.store.set_fuel(fuel).unwrap();
            let instance = Instance::new(&mut self.store, &compiled, &imports).map_err(failure)?;
            let entry = instance.get_func(&mut self.store, ENTRY).unwrap();
            let count = entry.ty(&self.store).results().len();
            let mut results = vec![Val::I32(0); count];
            entry
                .call(&mut self.store, &[], &mut results)
                .map_err(failure)?;
            Ok(results.iter().map(from_val).collect())
        }

        fn data(&self) -> Vec<ir::Data> {
            let memory = self.memory.data(&self.store);
            let Some(start) = memory.iter().position(|byte| *byte != 0) else {
                return Vec::new();
            };
            let end = memory.iter().rposition(|byte| *byte != 0).unwrap() + 1;
            vec![ir::Data {
                offset: start as u64,
                bytes: memory[start..end].to_vec(),
            }]
        }
    }

    impl Edges {
        fn of(ty: ValType) -> Vec<u64> {
            match ty {
                ValType::I32 => [
                    0,
                    1,
                    -1,
                    2,
                    7,
                    31,
                    32,
                    33,
                    0x7f,
                    0x80,
                    0xff,
                    0x7fff,
                    0x8000,
                    0xffff,
                    i32::MAX,
                    i32::MIN,
                    0x1234_5678,
                    -0x1234_5678,
                ]
                .map(|x: i32| x as u32 as u64)
                .to_vec(),
                ValType::I64 => [
                    0,
                    1,
                    -1,
                    2,
                    31,
                    32,
                    63,
                    64,
                    65,
                    0xff,
                    0xffff_ffff,
                    0x1_0000_0000,
                    i64::MAX,
                    i64::MIN,
                    0x0123_4567_89ab_cdef,
                    i32::MIN as i64,
                    i32::MAX as i64,
                ]
                .map(|x: i64| x as u64)
                .to_vec(),
                ValType::F32 => {
                    let floats = [
                        0.0,
                        -0.0,
                        1.0,
                        -1.0,
                        0.5,
                        -0.5,
                        1.5,
                        2.5,
                        -2.5,
                        1e10,
                        -1e10,
                        2147483520.0,
                        2147483648.0,
                        -2147483648.0,
                        4294967040.0,
                        4294967296.0,
                        9.223372e18,
                        1.8446744e19,
                        f32::MAX,
                        f32::MIN_POSITIVE,
                        1e-45,
                        f32::INFINITY,
                        f32::NEG_INFINITY,
                    ];
                    let nans = [0x7fc0_0000, 0xffc0_0000, 0x7fa0_0001, 0xff80_0001];
                    let floats = floats.map(|x: f32| x.to_bits());
                    floats.into_iter().chain(nans).map(u64::from).collect()
                }
                ValType::F64 => {
                    let floats = [
                        0.0,
                        -0.0,
                        1.0,
                        -1.0,
                        0.5,
                        -2.5,
                        0.1,
                        1.000_000_000_000_000_2,
                        16_777_217.0,
                        2147483647.0,
                        2147483648.0,
                        -2147483649.0,
                        4294967295.0,
                        4294967296.0,
                        9223372036854774784.0,
                        9223372036854775808.0,
                        -9223372036854775808.0,
                        18446744073709551616.0,
                        1e300,
                        1e-300,
                        f64::MAX,
                        f64::MIN_POSITIVE,
                        5e-324,
                        f64::INFINITY,
                        f64::NEG_INFINITY,
                    ];
                    let nans = [
                        0x7ff8_0000_0000_0000,
                        0xfff8_0000_0000_0000,
                        0x7ff4_0000_0000_0001,
                        0xfff0_0000_0000_0001,
                    ];
                    floats.map(f64::to_bits).into_iter().chain(nans).collect()
                }
            }
        }
    }

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        /// A number below `n`.
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }

        /// Whether a choice of one in `n` is made.
        fn one_in(&mut self, n: usize) -> bool {
            self.below(n) == 0
        }

        fn pick<T: Copy>(&mut self, of: &[T]) -> T {
            of[self.below(of.len())]
        }
    }

    impl Gen {
        const TYPES: [ValType; 4] = [ValType::I32, ValType::I64, ValType::F32, ValType::F64];

        /// A module of a few functions that the last calls, which is run,
        /// with the globals of [`globals`] and a table of them all.
        fn module(seed: u64) -> ir::Module {
            let mut maker = Self {
                rng: Rng(seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1),
                sigs: vec![FuncType {
                    params: vec![ValType::I32],
                    results: vec![ValType::I32],
                }],
                locals: Vec::new(),
                params: 0,
                results: Vec::new(),
                labels: Vec::new(),
                depth: 0,
            };
            let mut funcs = Vec::new();
            for i in 0..4 {
                let entry = i == 3;
                let params = match entry {
                    true => Vec::new(),
                    false => (0..maker.rng.below(3)).map(|_| maker.ty()).collect(),
                };
                let results = (0..maker.rng.below(3)).map(|_| maker.ty()).collect();
                let func = maker.func(i, params, results, entry);
                maker.sigs.push(FuncType {
                    params: func.params.clone(),
                    results: func.results.clone(),
                });
                funcs.push(func);
            }
            ir::Module {
                memory: ir::Memory {
                    min_pages: 0,
                    max_pages: None,
                    export: "memory".to_string(),
                },
                data: Vec::new(),
                table: Some(ir::Table {
                    export: Some("table".to_string()),
                    funcs: (0..5).map(FuncId).collect(),
                }),
                globals: globals(),
                imports: vec![ir::Import {
                    name: "ext".to_string(),
                    module: "env".to_string(),
                    field: "ext".to_string(),
                    params: vec![ValType::I32],
                    results: vec![ValType::I32],
                }],
                funcs,
            }
        }

        fn func(
            &mut self,
            i: usize,
            params: Vec<ValType>,
            results: Vec<ValType>,
            entry: bool,
        ) -> ir::Func {
            self.params = params.len();
            self.locals = params.clone();
            // One to count each loop with, of those that may be within
            // another, and a few of each type.
            self.locals.extend([ValType::I32; 4]);
            self.locals.extend(Self::TYPES);
            self.locals.extend(Self::TYPES);
            self.results = results.clone();
            let mut body = self.stmts(4);
            let values = results.iter().map(|ty| self.expr(*ty)).collect();
            body.push(Stmt::Return(values));
            let locals = self.locals.iter().map(|ty| ir::Local {
                name: format!("l{}", ty_name(*ty)),
                ty: *ty,
            });
            ir::Func {
                name: format!("f{i}"),
                exports: match entry {
                    true => vec![ENTRY.to_string()],
                    false => Vec::new(),
                },
                params,
                results,
                locals: locals.collect(),
                body,
            }
        }

        fn ty(&mut self) -> ValType {
            self.rng.pick(&Self::TYPES)
        }

        /// A local of type `ty`, which isn't one that counts a loop.
        fn local(&mut self, ty: ValType) -> LocalId {
            let counters = self.params..self.params + 4;
            let of: Vec<_> = (0..self.locals.len())
                .filter(|i| self.locals[*i] == ty && !counters.contains(i))
                .collect();
            LocalId(self.rng.pick(&of) as u32)
        }

        fn stmts(&mut self, most: usize) -> Vec<Stmt> {
            (0..self.rng.below(most + 1)).map(|_| self.stmt()).collect()
        }

        fn stmt(&mut self) -> Stmt {
            self.depth += 1;
            let deep = self.depth > 4;
            let stmt = match self.rng.below(if deep { 5 } else { 13 }) {
                0 => {
                    let ty = self.ty();
                    Stmt::SetLocal(self.local(ty), self.expr(ty))
                }
                1 => {
                    let (global, ty) =
                        self.rng
                            .pick(&[(0, ValType::I32), (1, ValType::I64), (2, ValType::F32)]);
                    Stmt::SetGlobal(GlobalId(global), self.expr(ty))
                }
                2 => {
                    let ty = self.ty();
                    let op = match ty {
                        ValType::I32 | ValType::I64 => {
                            self.rng
                                .pick(&[StoreOp::Store, StoreOp::Store8, StoreOp::Store16])
                        }
                        _ => StoreOp::Store,
                    };
                    Stmt::Store {
                        ty,
                        op,
                        offset: self.rng.pick(&[0, 1, 8, 200]),
                        addr: self.addr(),
                        value: self.expr(ty),
                    }
                }
                3 => {
                    let ty = self.ty();
                    Stmt::Drop(self.expr(ty))
                }
                4 => self.branch(),
                5 => {
                    self.labels.push(true);
                    let body = self.stmts(3);
                    self.labels.pop();
                    Stmt::Block(body)
                }
                6 => self.counted_loop(),
                7 => {
                    let cond = self.expr(ValType::I32);
                    self.labels.push(true);
                    let then_body = self.stmts(3);
                    let else_body = self.stmts(2);
                    self.labels.pop();
                    Stmt::If {
                        cond,
                        then_body,
                        else_body,
                    }
                }
                8 => {
                    let (func, ty) = self.callee();
                    let args = ty.params.iter().map(|ty| self.expr(*ty)).collect();
                    let dests = ty.results.iter().map(|ty| self.local(*ty)).collect();
                    Stmt::Call { func, args, dests }
                }
                9 => {
                    let (place, ty) = self.place();
                    let args = ty.params.iter().map(|ty| self.expr(*ty)).collect();
                    let dests = ty.results.iter().map(|ty| self.local(*ty)).collect();
                    Stmt::CallIndirect {
                        ty,
                        args,
                        index: Expr::Const(Const::I32(place)),
                        dests,
                    }
                }
                10 => Stmt::MemoryFill {
                    dst: self.addr(),
                    value: self.expr(ValType::I32),
                    len: self.small(300),
                },
                11 => Stmt::MemoryCopy {
                    dst: self.addr(),
                    src: self.addr(),
                    len: self.small(300),
                },
                _ if self.rng.one_in(4) => {
                    let results = self.results.clone();
                    Stmt::Return(results.iter().map(|ty| self.expr(*ty)).collect())
                }
                _ if self.rng.one_in(20) => Stmt::Unreachable,
                _ => Stmt::Drop(Expr::MemoryGrow(Box::new(self.small(2)))),
            };
            self.depth -= 1;
            stmt
        }

        /// A `br` or a `br_if` to a label that may be gone to, or else a
        /// statement that does nothing.
        fn branch(&mut self) -> Stmt {
            let depths: Vec<_> = (0..self.labels.len())
                .filter(|depth| self.labels[self.labels.len() - 1 - depth])
                .collect();
            if depths.is_empty() {
                return Stmt::Drop(Expr::MemorySize);
            }
            let depth = self.rng.pick(&depths) as u32;
            match self.rng.one_in(2) {
                true => Stmt::Br(depth),
                false => Stmt::BrIf(depth, self.expr(ValType::I32)),
            }
        }

        /// A loop that runs from one to three times, counted by a local of
        /// its own.
        fn counted_loop(&mut self) -> Stmt {
            let loops = self.labels.iter().filter(|label| !**label).count();
            if loops == 4 {
                return Stmt::Drop(Expr::MemorySize);
            }
            let counter = LocalId((self.params + loops) as u32);
            let count = Expr::Const(Const::I32(1 + self.rng.below(3) as i32));
            self.labels.push(false);
            let mut body = self.stmts(3);
            self.labels.pop();
            let less = Expr::Binary(
                ValType::I32,
                BinOp::Sub,
                Box::new(Expr::Local(counter)),
                Box::new(Expr::Const(Const::I32(1))),
            );
            body.push(Stmt::SetLocal(counter, less));
            let more = Expr::Binary(
                ValType::I32,
                BinOp::Ne,
                Box::new(Expr::Local(counter)),
                Box::new(Expr::Const(Const::I32(0))),
            );
            body.push(Stmt::BrIf(0, more));
            Stmt::Block(vec![Stmt::SetLocal(counter, count), Stmt::Loop(body)])
        }

        /// A function that may be called by name: the import, or one made
        /// before this, each by its index.
        fn callee(&mut self) -> (FuncId, FuncType) {
            let index = self.rng.below(self.sigs.len());
            (FuncId(index as u32), self.sigs[index].clone())
        }

        /// A place in the table to call, and the type it is called as: mostly
        /// that of what is there, a function that may be called by name, and
        /// otherwise a place that is empty or out of the table, or of a
        /// function of another type.
        fn place(&mut self) -> (i32, FuncType) {
            // Each is at the place after its index.
            let index = self.rng.below(self.sigs.len());
            let at = index as i32 + 1;
            match self.rng.below(6) {
                0 => (0, self.sigs[index].clone()),
                1 => (99, self.sigs[index].clone()),
                2 => (at, self.sigs[self.rng.below(self.sigs.len())].clone()),
                _ => (at, self.sigs[index].clone()),
            }
        }

        /// An address in the first page or near it, mostly.
        fn addr(&mut self) -> Expr {
            match self.rng.below(8) {
                0 => Expr::Const(Const::I32(self.rng.pick(&[65530, 65536, 131_070, -1, -8]))),
                _ => Expr::Binary(
                    ValType::I32,
                    BinOp::And,
                    Box::new(self.expr(ValType::I32)),
                    Box::new(Expr::Const(Const::I32(0x3ff))),
                ),
            }
        }

        fn small(&mut self, most: i32) -> Expr {
            Expr::Const(Const::I32(self.rng.below(most as usize + 1) as i32))
        }

        fn expr(&mut self, ty: ValType) -> Expr {
            self.depth += 1;
            let expr = match self.rng.below(if self.depth > 6 { 3 } else { 12 }) {
                0 => Expr::Const(konst(self.rng.pick(&Edges::of(ty)), ty)),
                1 => Expr::Local(self.local(ty)),
                2 if ty == ValType::F64 => Expr::Global(GlobalId(3)),
                2 => {
                    let index = Self::TYPES.iter().position(|t| *t == ty).unwrap();
                    Expr::Global(GlobalId(index as u32))
                }
                3 | 4 => self.unary(ty),
                5 | 6 => self.binary(ty),
                7 => {
                    let op = match ty {
                        ValType::I32 | ValType::I64 => self.rng.pick(&[
                            LoadOp::Load,
                            LoadOp::Load8S,
                            LoadOp::Load8U,
                            LoadOp::Load16S,
                            LoadOp::Load16U,
                        ]),
                        _ => LoadOp::Load,
                    };
                    Expr::Load {
                        ty,
                        op,
                        offset: self.rng.pick(&[0, 3, 64]),
                        addr: Box::new(self.addr()),
                    }
                }
                8 => {
                    let cond = Box::new(self.expr(ValType::I32));
                    self.labels.push(false);
                    let then_expr = Box::new(self.expr(ty));
                    let else_expr = Box::new(self.expr(ty));
                    self.labels.pop();
                    Expr::If {
                        ty,
                        cond,
                        then_expr,
                        else_expr,
                    }
                }
                9 => {
                    let body = self.stmts(2);
                    Expr::Seq(body, Box::new(self.expr(ty)))
                }
                10 => {
                    let (func, sig) = self.callee();
                    match sig.results[..] {
                        [result] if result == ty => {
                            let args = sig.params.iter().map(|ty| self.expr(*ty)).collect();
                            Expr::Call(func, args)
                        }
                        _ => Expr::Local(self.local(ty)),
                    }
                }
                _ => {
                    let (place, sig) = self.place();
                    match sig.results[..] {
                        [result] if result == ty => {
                            let args = sig.params.iter().map(|ty| self.expr(*ty)).collect();
                            let index = Box::new(Expr::Const(Const::I32(place)));
                            Expr::CallIndirect {
                                ty: sig,
                                args,
                                index,
                            }
                        }
                        _ if ty == ValType::I32 => Expr::MemorySize,
                        _ => Expr::Local(self.local(ty)),
                    }
                }
            };
            self.depth -= 1;
            expr
        }

        fn unary(&mut self, ty: ValType) -> Expr {
            let ops: Vec<_> = Self::TYPES
                .into_iter()
                .flat_map(|from| unary_ops().into_iter().map(move |op| (from, op)))
                .filter(|(from, op)| unary_type(*from, *op) == Some(ty))
                .collect();
            let (from, op) = self.rng.pick(&ops);
            Expr::Unary(from, op, Box::new(self.expr(from)))
        }

        fn binary(&mut self, ty: ValType) -> Expr {
            let ops: Vec<_> = Self::TYPES
                .into_iter()
                .flat_map(|from| binary_ops().into_iter().map(move |op| (from, op)))
                .filter(|(from, op)| binary_type(*from, *op) == Some(ty))
                .collect();
            let (from, op) = self.rng.pick(&ops);
            let a = self.expr(from);
            Expr::Binary(from, op, Box::new(a), Box::new(self.expr(from)))
        }
    }

    /// The engine the reference runs on, which is configured as the
    /// evaluator's once was.
    fn engine() -> &'static Engine {
        static ENGINE: std::sync::OnceLock<Engine> = std::sync::OnceLock::new();
        ENGINE.get_or_init(|| {
            let mut config = Config::new();
            config.consume_fuel(true);
            config.cranelift_nan_canonicalization(true);
            Engine::new(&config).unwrap()
        })
    }

    fn failure(error: wasmtime::Error) -> Failure {
        let kind = if let Some(Imported(index)) = error.downcast_ref() {
            FailureKind::Imported(*index)
        } else {
            match error.downcast_ref() {
                Some(Trap::OutOfFuel) => FailureKind::OutOfFuel,
                Some(Trap::UnreachableCodeReached) => FailureKind::Unreachable,
                Some(trap) => FailureKind::Trap(trap_message(trap)),
                None => FailureKind::Invalid(format!("{error:#}")),
            }
        };
        let backtrace = error.downcast_ref::<WasmBacktrace>();
        let frames = backtrace.map_or(&[][..], WasmBacktrace::frames);
        Failure {
            kind,
            stack: frames.iter().map(|frame| frame.func_index()).collect(),
        }
    }

    fn trap_message(trap: &Trap) -> String {
        let message = trap.to_string();
        message
            .strip_prefix("wasm trap: ")
            .unwrap_or(&message)
            .to_string()
    }

    fn val_type(ty: ValType) -> wasmtime::ValType {
        match ty {
            ValType::I32 => wasmtime::ValType::I32,
            ValType::I64 => wasmtime::ValType::I64,
            ValType::F32 => wasmtime::ValType::F32,
            ValType::F64 => wasmtime::ValType::F64,
        }
    }

    fn val(c: Const) -> Val {
        match c {
            Const::I32(x) => Val::I32(x),
            Const::I64(x) => Val::I64(x),
            Const::F32(x) => Val::F32(x.to_bits()),
            Const::F64(x) => Val::F64(x.to_bits()),
        }
    }

    fn from_val(val: &Val) -> Const {
        match val {
            Val::I32(x) => Const::I32(*x),
            Val::I64(x) => Const::I64(*x),
            Val::F32(bits) => Const::F32(f32::from_bits(*bits)),
            Val::F64(bits) => Const::F64(f64::from_bits(*bits)),
            _ => unreachable!("only numbers are results"),
        }
    }

    fn ty_name(ty: ValType) -> &'static str {
        match ty {
            ValType::I32 => "i32",
            ValType::I64 => "i64",
            ValType::F32 => "f32",
            ValType::F64 => "f64",
        }
    }

    fn unary_ops() -> Vec<UnOp> {
        use UnOp::*;
        let mut ops = vec![
            Eqz,
            Clz,
            Ctz,
            Neg,
            Extend8S,
            Extend16S,
            Wrap,
            ExtendS,
            ExtendU,
            Demote,
            Promote,
            Reinterpret,
        ];
        for ty in Gen::TYPES {
            ops.extend([TruncSatS(ty), TruncSatU(ty), ConvertS(ty), ConvertU(ty)]);
        }
        ops
    }

    fn binary_ops() -> Vec<BinOp> {
        use BinOp::*;
        vec![
            Add, Sub, Mul, Div, DivS, DivU, RemS, RemU, And, Or, Xor, Shl, ShrS, ShrU, Min, Max,
            Eq, Ne, Lt, LtS, LtU, Le, LeS, LeU, Gt, GtS, GtU, Ge, GeS, GeU,
        ]
    }

    /// The globals of each module [`Gen`] makes: one `var` of each type but
    /// `f64`, and a `let` of that.
    fn globals() -> Vec<ir::Global> {
        let global = |ty, mutable, init| ir::Global {
            name: format!("g{}", ty_name(ty)),
            ty,
            mutable,
            init,
            exports: Vec::new(),
        };
        vec![
            global(ValType::I32, true, Const::I32(7)),
            global(ValType::I64, true, Const::I64(-3)),
            global(ValType::F32, true, Const::F32(0.25)),
            global(ValType::F64, false, Const::F64(1e-3)),
        ]
    }

    /// A module that exports `body` as `f`, which takes `params` and returns
    /// one value of type `result`, and has a page of memory.
    fn exported(params: Vec<ValType>, result: ValType, body: Vec<Stmt>) -> Vec<u8> {
        let locals = params.iter().map(|ty| ir::Local {
            name: "x".to_string(),
            ty: *ty,
        });
        let func = ir::Func {
            name: "f".to_string(),
            exports: vec!["f".to_string()],
            locals: locals.collect(),
            params,
            results: vec![result],
            body,
        };
        emit::emit(&ir::Module {
            memory: ir::Memory {
                min_pages: 1,
                max_pages: Some(1),
                export: "memory".to_string(),
            },
            data: Vec::new(),
            table: None,
            globals: Vec::new(),
            imports: Vec::new(),
            funcs: vec![func],
        })
    }

    /// Calls `f` of `wasm` with the values `args` holds, typed `params`.
    /// Returns the bits of its result, or the trap it is.
    fn call_f(
        store: &mut Store<()>,
        instance: Instance,
        params: &[ValType],
        args: &[u64],
        result: ValType,
    ) -> Result<u64, String> {
        let f = instance.get_func(&mut *store, "f").unwrap();
        let args: Vec<_> = args
            .iter()
            .zip(params)
            .map(|(bits, ty)| val_bits(*bits, *ty))
            .collect();
        let mut results = [val_bits(0, result)];
        match f.call(&mut *store, &args, &mut results) {
            Ok(()) => Ok(bits_of(&results[0])),
            Err(error) => Err(trap_message(error.downcast_ref::<Trap>().unwrap())),
        }
    }

    fn val_bits(bits: u64, ty: ValType) -> Val {
        match ty {
            ValType::I32 => Val::I32(bits as u32 as i32),
            ValType::I64 => Val::I64(bits as i64),
            ValType::F32 => Val::F32(bits as u32),
            ValType::F64 => Val::F64(bits),
        }
    }

    fn bits_of(val: &Val) -> u64 {
        match val {
            Val::I32(x) => *x as u32 as u64,
            Val::I64(x) => *x as u64,
            Val::F32(bits) => u64::from(*bits),
            Val::F64(bits) => *bits,
            _ => unreachable!("only numbers are results"),
        }
    }

    fn instantiate(wasm: &[u8]) -> (Store<()>, Instance) {
        let mut store = Store::new(engine(), ());
        store.set_fuel(u64::MAX).unwrap();
        let module = Module::new(engine(), wasm).unwrap();
        let instance = Instance::new(&mut store, &module, &[]).unwrap();
        (store, instance)
    }

    fn stopped(stop: Stop) -> String {
        match stop {
            Stop::Trap(trap) => trap.to_string(),
            _ => panic!("an operator only traps"),
        }
    }

    #[test]
    fn unary_operators_are_those_of_wasm() {
        let mut checked = 0;
        for ty in Gen::TYPES {
            for op in unary_ops() {
                let Some(result) = unary_type(ty, op) else {
                    continue;
                };
                let x = Box::new(Expr::Local(LocalId(0)));
                let body = vec![Stmt::Return(vec![Expr::Unary(ty, op, x)])];
                let (mut store, instance) = instantiate(&exported(vec![ty], result, body));
                for x in Edges::of(ty) {
                    let wasm = call_f(&mut store, instance, &[ty], &[x], result);
                    let ours = unary(ty, op, x);
                    assert_eq!(Ok(ours), wasm, "{ty:?}.{op:?} of {x:#x}");
                    checked += 1;
                }
            }
        }
        assert!(checked > 400, "{checked}");
    }

    #[test]
    fn binary_operators_are_those_of_wasm() {
        let mut checked = 0;
        for ty in Gen::TYPES {
            for op in binary_ops() {
                let Some(result) = binary_type(ty, op) else {
                    continue;
                };
                let (a, b) = (Expr::Local(LocalId(0)), Expr::Local(LocalId(1)));
                let value = Expr::Binary(ty, op, Box::new(a), Box::new(b));
                let body = vec![Stmt::Return(vec![value])];
                let (mut store, instance) = instantiate(&exported(vec![ty, ty], result, body));
                for a in Edges::of(ty) {
                    for b in Edges::of(ty) {
                        let wasm = call_f(&mut store, instance, &[ty, ty], &[a, b], result);
                        let ours = binary(ty, op, a, b).map_err(stopped);
                        assert_eq!(ours, wasm, "{ty:?}.{op:?} of {a:#x} and {b:#x}");
                        checked += 1;
                    }
                }
            }
        }
        assert!(checked > 20_000, "{checked}");
    }

    #[test]
    fn loads_and_stores_are_those_of_wasm() {
        let pattern: Vec<u8> = (0..PAGE_SIZE).map(|i| (i * 37 % 251) as u8).collect();
        let addrs: [i32; 11] = [0, 1, 7, 65528, 65529, 65532, 65534, 65535, 65536, -16, -1];
        let ops = [
            (ValType::I32, LoadOp::Load, StoreOp::Store),
            (ValType::I64, LoadOp::Load, StoreOp::Store),
            (ValType::F32, LoadOp::Load, StoreOp::Store),
            (ValType::F64, LoadOp::Load, StoreOp::Store),
            (ValType::I32, LoadOp::Load8S, StoreOp::Store8),
            (ValType::I32, LoadOp::Load8U, StoreOp::Store16),
            (ValType::I32, LoadOp::Load16S, StoreOp::Store8),
            (ValType::I32, LoadOp::Load16U, StoreOp::Store16),
            (ValType::I64, LoadOp::Load8S, StoreOp::Store8),
            (ValType::I64, LoadOp::Load8U, StoreOp::Store16),
            (ValType::I64, LoadOp::Load16S, StoreOp::Store8),
            (ValType::I64, LoadOp::Load16U, StoreOp::Store16),
        ];
        for (ty, load, store) in ops {
            for offset in [0, 3, 65535] {
                let addr = Box::new(Expr::Local(LocalId(0)));
                let read = Expr::Load {
                    ty,
                    op: load,
                    offset,
                    addr,
                };
                let body = vec![Stmt::Return(vec![read])];
                let (mut wasm_store, instance) =
                    instantiate(&exported(vec![ValType::I32], ty, body));
                let memory = instance.get_memory(&mut wasm_store, "memory").unwrap();
                memory.data_mut(&mut wasm_store).copy_from_slice(&pattern);
                let mut eval = Evaluator::new(1, 1);
                assert!(eval.cover(PAGE_SIZE));
                eval.write(0, &pattern);
                for addr in addrs {
                    let at = addr as u32 as u64;
                    let wasm = call_f(&mut wasm_store, instance, &[ValType::I32], &[at], ty);
                    let ours = eval.load(ty, load, offset, at).map_err(stopped);
                    assert_eq!(ours, wasm, "{ty:?}.{load:?} offset={offset} at {addr}");
                }

                // A store, which then reads back the eight bytes it was
                // given.
                let written = Stmt::Store {
                    ty,
                    op: store,
                    offset,
                    addr: Expr::Local(LocalId(0)),
                    value: Expr::Const(konst(0x8899_aabb_ccdd_eeff, ty)),
                };
                let read = Expr::Load {
                    ty: ValType::I64,
                    op: LoadOp::Load,
                    offset: 0,
                    addr: Box::new(Expr::Const(Const::I32(0))),
                };
                let body = vec![written, Stmt::Return(vec![read])];
                let wasm = exported(vec![ValType::I32], ValType::I64, body);
                for addr in addrs {
                    let (mut wasm_store, instance) = instantiate(&wasm);
                    let memory = instance.get_memory(&mut wasm_store, "memory").unwrap();
                    memory.data_mut(&mut wasm_store).copy_from_slice(&pattern);
                    let at = addr as u32 as u64;
                    let stored = call_f(
                        &mut wasm_store,
                        instance,
                        &[ValType::I32],
                        &[at],
                        ValType::I64,
                    );
                    let mut eval = Evaluator::new(1, 1);
                    assert!(eval.cover(PAGE_SIZE));
                    eval.write(0, &pattern);
                    let value = bits(konst(0x8899_aabb_ccdd_eeff, ty));
                    let ours = eval.store(ty, store, offset, at, value).map_err(stopped);
                    assert_eq!(ours.is_ok(), stored.is_ok(), "{ty:?}.{store:?} at {addr}");
                    if let Err(trap) = stored {
                        assert_eq!(ours, Err(trap));
                    }
                    let theirs = memory.data(&wasm_store);
                    assert!(
                        eval.memory == theirs,
                        "{ty:?}.{store:?} offset={offset} at {addr}"
                    );
                }
            }
        }
    }

    /// `module` written compactly, for a failure to show.
    fn show(module: &ir::Module) -> String {
        fn e(x: &Expr) -> String {
            match x {
                Expr::Const(c) => format!("{c:?}"),
                Expr::Local(l) => format!("l{}", l.0),
                Expr::Global(g) => format!("g{}", g.0),
                Expr::Unary(t, o, a) => format!("{t:?}.{o:?}({})", e(a)),
                Expr::Binary(t, o, a, b) => format!("{t:?}.{o:?}({}, {})", e(a), e(b)),
                Expr::Call(f, args) => format!(
                    "call{}({})",
                    f.0,
                    args.iter().map(e).collect::<Vec<_>>().join(", ")
                ),
                Expr::CallIndirect { args, index, .. } => format!(
                    "call_indirect[{}]({})",
                    e(index),
                    args.iter().map(e).collect::<Vec<_>>().join(", ")
                ),
                Expr::Load {
                    ty,
                    op,
                    offset,
                    addr,
                } => format!("{ty:?}.{op:?}+{offset}({})", e(addr)),
                Expr::MemorySize => "size".into(),
                Expr::MemoryGrow(a) => format!("grow({})", e(a)),
                Expr::If {
                    cond,
                    then_expr,
                    else_expr,
                    ..
                } => format!(
                    "if({}) {{{}}} else {{{}}}",
                    e(cond),
                    e(then_expr),
                    e(else_expr)
                ),
                Expr::Seq(b, v) => format!("seq{{{}; {}}}", ss(b, 0).trim(), e(v)),
                Expr::Symbol(_, symbol) => format!("{symbol:?}"),
            }
        }
        fn ss(b: &[Stmt], d: usize) -> String {
            b.iter().map(|x| st(x, d)).collect()
        }
        fn st(x: &Stmt, d: usize) -> String {
            let pad = "  ".repeat(d);
            match x {
                Stmt::Block(b) => format!("{pad}block\n{}", ss(b, d + 1)),
                Stmt::Loop(b) => format!("{pad}loop\n{}", ss(b, d + 1)),
                Stmt::If {
                    cond,
                    then_body,
                    else_body,
                } => format!(
                    "{pad}if {}\n{}{pad}else\n{}",
                    e(cond),
                    ss(then_body, d + 1),
                    ss(else_body, d + 1)
                ),
                Stmt::SetLocal(l, v) => format!("{pad}l{} = {}\n", l.0, e(v)),
                Stmt::SetGlobal(g, v) => format!("{pad}g{} = {}\n", g.0, e(v)),
                Stmt::Store {
                    ty,
                    op,
                    offset,
                    addr,
                    value,
                } => format!("{pad}{ty:?}.{op:?}+{offset}({}) = {}\n", e(addr), e(value)),
                Stmt::Drop(v) => format!("{pad}drop {}\n", e(v)),
                Stmt::MemoryFill { dst, value, len } => {
                    format!("{pad}fill({}, {}, {})\n", e(dst), e(value), e(len))
                }
                Stmt::MemoryCopy { dst, src, len } => {
                    format!("{pad}copy({}, {}, {})\n", e(dst), e(src), e(len))
                }
                Stmt::Call { func, args, dests } => format!(
                    "{pad}{dests:?} = call{}({})\n",
                    func.0,
                    args.iter().map(e).collect::<Vec<_>>().join(", ")
                ),
                Stmt::CallIndirect {
                    args, index, dests, ..
                } => format!(
                    "{pad}{dests:?} = call_indirect[{}]({})\n",
                    e(index),
                    args.iter().map(e).collect::<Vec<_>>().join(", ")
                ),
                Stmt::Br(n) => format!("{pad}br {n}\n"),
                Stmt::BrIf(n, c) => format!("{pad}br_if {n} {}\n", e(c)),
                Stmt::Return(v) => format!(
                    "{pad}return {}\n",
                    v.iter().map(e).collect::<Vec<_>>().join(", ")
                ),
                Stmt::Unreachable => format!("{pad}unreachable\n"),
            }
        }
        let mut out = String::new();
        for (i, f) in module.funcs.iter().enumerate() {
            out += &format!(
                "func {} ({:?}) -> {:?}\n{}",
                i + module.imports.len(),
                f.params,
                f.results,
                ss(&f.body, 1)
            );
        }
        out
    }

    /// Runs the module that `seed` makes on the evaluator and on the
    /// reference, twice on each, and checks that they run it alike.
    fn compare(seed: u64) -> Option<String> {
        let module = Gen::module(seed);
        let mut ours = Evaluator::new(4, 4);
        let mut theirs = Reference::new(4);
        assert!(ours.cover(PAGE_SIZE));
        assert!(theirs.cover(PAGE_SIZE));
        let pattern: Vec<u8> = (0..256).map(|i| (i * 13 + 5) as u8).collect();
        ours.write(0, &pattern);
        theirs.write(0, &pattern);
        for global in &module.globals {
            ours.add_global(global);
            theirs.add_global(global);
        }
        let mut outcome = None;
        for run in 0..2 {
            let (a, a_left) = ours.run(&module, 1_000_000);
            let (b, b_left) = theirs.run(&module, 1_000_000);
            let same = match (&a, &b) {
                (Ok(a), Ok(b)) => {
                    a.iter().map(|c| bits(*c)).eq(b.iter().map(|c| bits(*c))) && a_left == b_left
                }
                (Err(a), Err(b)) => a == b,
                _ => false,
            };
            let state = ours.data() == theirs.data()
                && (0..module.globals.len())
                    .all(|i| bits(ours.global(i)) == bits(theirs.global(i)));
            assert!(
                same && state,
                "seed {seed}, run {run}: ours {a:?} with {a_left} left, wasmtime's {b:?} \
                 with {b_left} left\n{}",
                show(&module)
            );
            outcome = Some(match a {
                Ok(_) => "returned".to_string(),
                Err(failure) => format!("{:?}", failure.kind),
            });
        }
        outcome
    }

    #[test]
    fn fuel_is_used_as_wasmtime_uses_it() {
        let i = |x| Expr::Const(Const::I32(x));
        let call = |func| Stmt::Call {
            func: FuncId(func),
            args: Vec::new(),
            dests: Vec::new(),
        };
        let indirect = |place| Stmt::CallIndirect {
            ty: FuncType {
                params: Vec::new(),
                results: Vec::new(),
            },
            args: Vec::new(),
            index: i(place),
            dests: Vec::new(),
        };
        let fill = |len| Stmt::MemoryFill {
            dst: i(0),
            value: i(1),
            len: i(len),
        };
        let copy = |len| Stmt::MemoryCopy {
            dst: i(0),
            src: i(400),
            len: i(len),
        };
        let grow = |pages| Stmt::Drop(Expr::MemoryGrow(Box::new(i(pages))));
        let counted = vec![
            Stmt::SetLocal(LocalId(0), i(3)),
            Stmt::Loop(vec![
                Stmt::SetLocal(
                    LocalId(0),
                    Expr::Binary(
                        ValType::I32,
                        BinOp::Sub,
                        Box::new(Expr::Local(LocalId(0))),
                        Box::new(i(1)),
                    ),
                ),
                Stmt::BrIf(0, Expr::Local(LocalId(0))),
            ]),
        ];
        let bodies = [
            (vec![], 2),
            (vec![Stmt::Drop(i(1))], 3),
            (vec![Stmt::Block(vec![Stmt::Br(0)])], 3),
            (
                vec![Stmt::If {
                    cond: i(1),
                    then_body: vec![Stmt::Drop(i(2))],
                    else_body: vec![Stmt::Drop(i(3))],
                }],
                5,
            ),
            (counted, 22),
            (vec![call(0)], 4),
            (vec![call(0), call(0)], 6),
            (vec![indirect(1)], 5),
            (vec![fill(0)], 6),
            (vec![fill(9)], 15),
            (vec![copy(300)], 306),
            (vec![grow(0)], 4),
            (vec![grow(2)], 6),
            // One that fails costs as much.
            (vec![grow(9)], 13),
            // And one that costs more than there is uses it up.
            (vec![fill(1000)], 1000),
        ];
        for (body, used) in bodies {
            let empty = ir::Func {
                name: "empty".to_string(),
                exports: Vec::new(),
                params: Vec::new(),
                results: Vec::new(),
                locals: Vec::new(),
                body: Vec::new(),
            };
            let local = ir::Local {
                name: "n".to_string(),
                ty: ValType::I32,
            };
            let entry = ir::Func {
                name: "entry".to_string(),
                exports: vec![ENTRY.to_string()],
                locals: vec![local],
                body: body.clone(),
                ..empty.clone()
            };
            let module = ir::Module {
                memory: ir::Memory {
                    min_pages: 0,
                    max_pages: None,
                    export: "memory".to_string(),
                },
                data: Vec::new(),
                table: Some(ir::Table {
                    export: Some("table".to_string()),
                    funcs: vec![FuncId(0), FuncId(1)],
                }),
                globals: Vec::new(),
                imports: Vec::new(),
                funcs: vec![empty, entry],
            };
            let mut ours = Evaluator::new(4, 4);
            let mut theirs = Reference::new(4);
            assert!(ours.cover(PAGE_SIZE) && theirs.cover(PAGE_SIZE));
            let (_, ours) = ours.run(&module, 1000);
            let (_, theirs) = theirs.run(&module, 1000);
            assert_eq!(
                (1000 - ours, 1000 - theirs),
                (used, used),
                "{}",
                show(&module)
            );
        }
    }

    #[test]
    fn modules_made_at_random_run_as_on_wasmtime() {
        let mut outcomes = std::collections::BTreeMap::<String, usize>::new();
        for seed in 1..=120 {
            *outcomes.entry(compare(seed).unwrap()).or_default() += 1;
        }
        // Enough run to their end, and enough fail in each way.
        let count = |name: &str| {
            let failed = outcomes
                .iter()
                .filter(|(outcome, _)| outcome.contains(name));
            failed.map(|(_, count)| count).sum::<usize>()
        };
        assert!(count("returned") > 20, "{outcomes:#?}");
        assert!(count("Trap") > 20, "{outcomes:#?}");
        assert!(count("Imported") > 5, "{outcomes:#?}");
        assert!(count("Unreachable") > 0, "{outcomes:#?}");
    }
}

//! Constants that are only known by running them: a global initializer, an
//! enum member's value or a default that calls a function, or reads what
//! one may have written.
//!
//! Such a constant is run as a function of its own, in a module with the
//! functions it may call, on the [`Evaluator`] that holds the state of the
//! program so far. Each function is lowered the first time a constant may
//! call it, and has what it reads folded first, so a constant is run with
//! everything it names, and is in its own definition if that leads back to
//! it. What the runs leave in memory and in the globals is what the module
//! starts with.
//!
//! A constant may call the functions it calls by name, those it takes a
//! pointer to, and those that the constants it reads do, and so on through
//! each of them: [`Dep`] records what each names. A pointer that only
//! memory holds leads to its function if an earlier run could have called
//! it, and otherwise to one that traps.

use std::collections::HashSet;
use std::mem;

use crate::eval::{self, Evaluator, Failure, FailureKind};
use crate::ir::{self, Const, Expr, FuncId, Stmt, ValType};
use crate::lex::Span;
use crate::load::Program;

use super::{
    Checker, Fold, MEMORY_EXPORT, PAGE_SIZE, TABLE_EXPORT, TEMP, Ty, TypeError, TypeErrorKind,
    Value, exprs, fn_decls,
};

/// The fuel the constants of one item run on, unless the settings say: about
/// a second's worth.
pub const DEFAULT_FUEL: u64 = 10_000_000_000;

/// The most pages memory grows to while constants are evaluated, where the
/// settings leave it unlimited: 1 GiB.
const MAX_CONSTANT_PAGES: u64 = 16 * 1024;

/// The most functions an error names of those that were running.
const MAX_STACK: usize = 8;

/// What a constant or a function names that code run for a constant may go
/// on to call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum Dep {
    /// A function whose pointer is taken.
    Func(FuncId),
    /// An item whose constants are read, which name what they do.
    Item(usize),
}

impl Checker {
    /// Lowers function `id` for a constant to call, while constants are
    /// still being folded: those its body is first to read are folded for
    /// it.
    fn lower_for_constant(&mut self, program: &Program, id: FuncId) {
        self.lowering.insert(id);
        self.deps.push(Vec::new());
        // What is folding may be in another module, or a generic function's.
        let module = self.module;
        let type_params = mem::take(&mut self.type_params);
        let chain = mem::take(&mut self.instance_chain);
        let first = self.funcs.len() - self.synths.len();
        let func = match (id.0 as usize) < first {
            true => {
                let defined = (id.0 - self.import_count) as usize;
                let (item, decl) = fn_decls(program).nth(defined).unwrap();
                self.lower_decl(program, id, item, decl)
            }
            false => self.lower_synth(program, id),
        };
        self.module = module;
        self.type_params = type_params;
        self.instance_chain = chain;
        let deps = self.deps.pop().unwrap_or_default();
        self.func_deps.insert(id, deps);
        self.lowering.remove(&id);
        self.lowered.insert(id, func);
    }

    /// Lowers every function that code run for the constant being folded
    /// may call: those that `thunk`, the code itself, calls, those it and
    /// the constants it reads take pointers to, and so on through each of
    /// them. Returns them, with those an earlier run may have left a
    /// pointer to. `None` after reporting, at `span`, one that is itself
    /// being lowered: it reads the constant, so the constant is used in its
    /// own definition.
    fn lower_callable(
        &mut self,
        program: &Program,
        thunk: &ir::Func,
        span: Span,
    ) -> Option<HashSet<FuncId>> {
        let mut work = self.deps.last().cloned().unwrap_or_default();
        push_calls(&thunk.body, &mut work);
        // Only a function that is lowered has run, or been run by one that
        // has.
        let pointed = self.table.iter().filter(|id| self.lowered.contains_key(id));
        work.extend(pointed.map(|id| Dep::Func(*id)));
        let (mut funcs, mut items) = (HashSet::new(), HashSet::new());
        while let Some(dep) = work.pop() {
            let id = match dep {
                Dep::Item(index) => {
                    if items.insert(index) {
                        work.extend(self.item_deps.get(&index).into_iter().flatten());
                    }
                    continue;
                }
                // An imported function has no body.
                Dep::Func(id) if id.0 < self.import_count => continue,
                Dep::Func(id) if !funcs.insert(id) => continue,
                Dep::Func(id) => id,
            };
            if self.lowering.contains(&id) {
                let folding = self.folding.last().copied();
                let name = folding.map_or_else(String::new, |index| self.item_name(program, index));
                self.error(TypeErrorKind::RecursiveConstant(name), span);
                return None;
            }
            if !self.lowered.contains_key(&id) {
                self.lower_for_constant(program, id);
            }
            work.extend(self.func_deps.get(&id).into_iter().flatten());
            push_calls(&self.lowered[&id].body, &mut work);
        }
        Some(funcs)
    }

    /// The scalars of the lowered constant `value`, whose temporaries are
    /// `locals`: folded, or else found by running it, with every function
    /// it calls. `None` after reporting, at `span`, why it has none, or if
    /// it isn't run.
    pub(super) fn evaluate(
        &mut self,
        program: &Program,
        locals: Vec<ir::Local>,
        value: Value,
        span: Span,
    ) -> Option<Vec<Const>> {
        match self.fold_value(&value) {
            Ok(consts) => Some(consts),
            Err(Fold::Trap) => {
                self.error(TypeErrorKind::ConstTrap, span);
                None
            }
            Err(Fold::NotConstant) => self.run(program, locals, value, span),
        }
    }

    /// Runs the lowered constant `value`, whose temporaries are `locals`,
    /// and returns each of its scalars. `None` after reporting, at `span`,
    /// why it has none, or if it isn't run: after any error, nothing is,
    /// as what an error leaves lowered may not be valid.
    fn run(
        &mut self,
        program: &Program,
        locals: Vec<ir::Local>,
        value: Value,
        span: Span,
    ) -> Option<Vec<Const>> {
        if self.failed || !self.errors.is_empty() {
            return None;
        }
        let folding = self.folding.last().copied();
        let name = folding.map_or_else(String::new, |index| self.item_name(program, index));
        let results = value.scalars.iter().map(|(ty, _)| *ty).collect();
        let mut body = value.pre;
        body.push(Stmt::Return(exprs(value.scalars)));
        let thunk = ir::Func {
            name,
            exports: vec![eval::ENTRY.to_string()],
            params: Vec::new(),
            results,
            locals,
            body,
        };
        // A function lowered here folds constants as deep as this one is.
        self.constant_depth += 1;
        let reached = self.lower_callable(program, &thunk, span);
        self.constant_depth -= 1;
        let reached = reached?;
        // Literals that don't fit are at no address, and are reported.
        if self.failed || !self.errors.is_empty() || !self.data_fits() {
            return None;
        }
        let module = self.hosted(program, thunk, &reached);
        let fuel = self.fuel;
        let results = match self.sync().map(|eval| eval.run(&module, fuel)) {
            Ok((results, left)) => {
                self.fuel = left;
                results
            }
            Err(failure) => Err(failure),
        };
        match results {
            Ok(consts) => Some(consts),
            Err(failure) => {
                self.failed = true;
                let kind = self.failure_kind(&module, &reached, failure);
                self.error(kind, span);
                None
            }
        }
    }

    /// The module that runs `thunk`, the code of a constant, with the state
    /// of the program so far. It has every function there is, each where
    /// the program has it, so that what is lowered calls what it names, but
    /// only those of `reached` have their bodies. The others are never
    /// reached.
    fn hosted(&self, program: &Program, thunk: ir::Func, reached: &HashSet<FuncId>) -> ir::Module {
        let ids = (self.import_count..self.funcs.len() as u32).map(FuncId);
        let funcs = ids.map(|id| match self.lowered.get(&id) {
            Some(func) if reached.contains(&id) => ir::Func {
                exports: Vec::new(),
                ..func.clone()
            },
            _ => self.stub(id),
        });
        ir::Module {
            // The memory is the evaluator's, whatever size it is.
            memory: ir::Memory {
                min_pages: 0,
                max_pages: None,
                export: MEMORY_EXPORT.to_string(),
            },
            data: Vec::new(),
            table: Some(ir::Table {
                export: Some(TABLE_EXPORT.to_string()),
                funcs: self.table.clone(),
            }),
            globals: self.ir_globals.clone(),
            imports: self.lower_imports(program),
            funcs: funcs.chain([thunk]).collect(),
        }
    }

    /// A function with the wasm type of function `id` that traps.
    fn stub(&self, id: FuncId) -> ir::Func {
        let sig = &self.funcs[id.0 as usize];
        let params = sig.params.iter().filter(|(_, ty)| *ty != Ty::Type);
        let params: Vec<_> = params.flat_map(|(_, ty)| self.val_types(*ty)).collect();
        let local = |ty: &ValType| ir::Local {
            name: TEMP.to_string(),
            ty: *ty,
        };
        ir::Func {
            name: sig.name.clone(),
            exports: Vec::new(),
            locals: params.iter().map(local).collect(),
            params,
            results: self.val_types(sig.ret),
            body: vec![Stmt::Unreachable],
        }
    }

    /// The state that the code constants run leaves, made if none has run
    /// yet, with the literals placed and the globals defined since it was
    /// last asked for. An error if memory can't hold them.
    pub(super) fn sync(&mut self) -> Result<&mut Evaluator, Failure> {
        let eval = match &mut self.eval {
            Some(eval) => eval,
            none => {
                let most = MAX_CONSTANT_PAGES.min(u64::from(u32::MAX) / PAGE_SIZE + 1);
                let max = self.max_pages.unwrap_or(most);
                none.insert(Evaluator::new(max)?)
            }
        };
        let end = u64::try_from(self.data_end).unwrap_or(u64::MAX);
        if !eval.cover(end) {
            let why = "memory can't grow to hold the literals".to_string();
            return Err(Failure {
                kind: FailureKind::Invalid(why),
                stack: Vec::new(),
            });
        }
        for (offset, len) in self.zeroed.drain(..) {
            eval.zero(offset, len);
        }
        for data in &self.data[self.synced..] {
            eval.write(data.offset, &data.bytes);
        }
        self.synced = self.data.len();
        for global in &self.ir_globals[eval.global_count()..] {
            eval.add_global(global);
        }
        Ok(eval)
    }

    /// Gives the state that the code constants ran left, if any ran, the
    /// literals placed since the last of it did. Reports memory that can't
    /// hold them.
    pub(super) fn place_late_literals(&mut self) {
        if self.eval.is_none() || !self.errors.is_empty() {
            return;
        }
        if let Err(failure) = self.sync() {
            let FailureKind::Invalid(why) = failure.kind else {
                unreachable!("nothing is run");
            };
            self.errors.push(TypeError {
                kind: TypeErrorKind::ConstNotRun(why),
                span: None,
                instances: Vec::new(),
            });
        }
    }

    /// What an error says of `failure`, which stopped `module`. It has the
    /// bodies of the functions of `reached`.
    fn failure_kind(
        &self,
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
                fuel: self.fuel_limit,
                stack,
            },
            FailureKind::Imported(index) => TypeErrorKind::ConstCallsExtern {
                name: name(&index),
                stack,
            },
            FailureKind::Invalid(why) => TypeErrorKind::ConstNotRun(why),
        }
    }
}

/// Adds each function that `body` calls by name to `out`.
fn push_calls(body: &[Stmt], out: &mut Vec<Dep>) {
    for stmt in body {
        match stmt {
            Stmt::SetLocal(_, value) | Stmt::SetGlobal(_, value) | Stmt::Drop(value) => {
                push_expr_calls(value, out);
            }
            Stmt::Store { addr, value, .. } => {
                push_expr_calls(addr, out);
                push_expr_calls(value, out);
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
            } => [a, b, c].into_iter().for_each(|e| push_expr_calls(e, out)),
            Stmt::Call { func, args, .. } => {
                out.push(Dep::Func(*func));
                args.iter().for_each(|arg| push_expr_calls(arg, out));
            }
            Stmt::CallIndirect { args, index, .. } => {
                args.iter().for_each(|arg| push_expr_calls(arg, out));
                push_expr_calls(index, out);
            }
            Stmt::Block(body) | Stmt::Loop(body) => push_calls(body, out),
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                push_expr_calls(cond, out);
                push_calls(then_body, out);
                push_calls(else_body, out);
            }
            Stmt::BrIf(_, cond) => push_expr_calls(cond, out),
            Stmt::Return(values) => values.iter().for_each(|e| push_expr_calls(e, out)),
            Stmt::Br(_) | Stmt::Unreachable => {}
        }
    }
}

/// Adds each function that `expr` calls by name to `out`.
fn push_expr_calls(expr: &Expr, out: &mut Vec<Dep>) {
    match expr {
        Expr::Const(_) | Expr::Local(_) | Expr::Global(_) | Expr::MemorySize => {}
        Expr::Unary(_, _, x) | Expr::Load { addr: x, .. } | Expr::MemoryGrow(x) => {
            push_expr_calls(x, out);
        }
        Expr::Binary(_, _, a, b) => {
            push_expr_calls(a, out);
            push_expr_calls(b, out);
        }
        Expr::Call(func, args) => {
            out.push(Dep::Func(*func));
            args.iter().for_each(|arg| push_expr_calls(arg, out));
        }
        Expr::CallIndirect { args, index, .. } => {
            args.iter().for_each(|arg| push_expr_calls(arg, out));
            push_expr_calls(index, out);
        }
        Expr::If {
            cond,
            then_expr,
            else_expr,
            ..
        } => [cond, then_expr, else_expr]
            .into_iter()
            .for_each(|e| push_expr_calls(e, out)),
        Expr::Seq(body, value) => {
            push_calls(body, out);
            push_expr_calls(value, out);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::check;
    use super::*;
    use crate::file::{DummyManager, FileManager, Settings};
    use crate::lex::tokenize;
    use crate::parse;

    fn check_with(src: &str, settings: &Settings) -> Result<ir::Module, Vec<TypeError>> {
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        check(&program, settings)
    }

    fn lower(src: &str) -> ir::Module {
        match check_with(src, &Settings::default()) {
            Ok(module) => module,
            Err(errors) => panic!("unexpected type errors: {errors:#?}"),
        }
    }

    /// The module of `src`, compiled and instantiated, as its host finds it.
    struct Started {
        store: wasmtime::Store<()>,
        instance: wasmtime::Instance,
    }

    impl Started {
        fn of(src: &str) -> Self {
            let bytes = crate::emit::emit(&lower(src));
            let engine = wasmtime::Engine::default();
            let module = wasmtime::Module::new(&engine, bytes).unwrap();
            let mut store = wasmtime::Store::new(&engine, ());
            let instance = wasmtime::Instance::new(&mut store, &module, &[]).unwrap();
            Self { store, instance }
        }

        /// What the exported `i32` global `name` holds.
        fn global(&mut self, name: &str) -> i32 {
            let global = self.instance.get_global(&mut self.store, name).unwrap();
            global.get(&mut self.store).unwrap_i32()
        }

        /// The result of the exported function `name`, from `i32`s to an
        /// `i32`, called with `args`.
        fn call(&mut self, name: &str, args: &[i32]) -> i32 {
            let func = self.instance.get_func(&mut self.store, name).unwrap();
            let args: Vec<_> = args.iter().map(|arg| wasmtime::Val::I32(*arg)).collect();
            let mut results = [wasmtime::Val::I32(0)];
            func.call(&mut self.store, &args, &mut results).unwrap();
            results[0].unwrap_i32()
        }

        /// The `len` bytes of memory at `addr`.
        fn bytes(&mut self, addr: usize, len: usize) -> Vec<u8> {
            let memory = self.instance.get_memory(&mut self.store, "memory").unwrap();
            memory.data(&self.store)[addr..addr + len].to_vec()
        }

        /// The size of memory, in pages.
        fn pages(&mut self) -> u64 {
            let memory = self.instance.get_memory(&mut self.store, "memory").unwrap();
            memory.size(&self.store)
        }
    }

    /// Each exported global of `module` and what it starts as, as
    /// `name=value`.
    fn exported(module: &ir::Module) -> String {
        let value = |c: Const| match c {
            Const::I32(x) => x.to_string(),
            Const::I64(x) => format!("{x}i64"),
            Const::F32(x) => format!("{x:?}f32"),
            Const::F64(x) => format!("{x:?}f64"),
        };
        let globals = module.globals.iter().filter(|g| !g.exports.is_empty());
        let globals = globals.map(|g| format!("{}={}", g.name, value(g.init)));
        globals.collect::<Vec<_>>().join(" ")
    }

    /// What the exported globals of `src` start as.
    fn consts(src: &str) -> String {
        exported(&lower(src))
    }

    /// Each error of `src` as it is shown, and what it is reported at.
    fn errors_at(src: &str) -> Vec<(String, &str)> {
        let errors = check_with(src, &Settings::default()).unwrap_err();
        let at = |e: TypeError| {
            let span = e.span.unwrap();
            (e.kind.to_string(), &src[span.start..span.end])
        };
        errors.into_iter().map(at).collect()
    }

    #[test]
    fn a_module_starts_as_its_constants_left_it() {
        let src = "\
let squares: varray(u32) = [0; 4]
pub var count = 0
pub var untouched = 5
fn fill() -> uint:
    var i: uint = 0
    while i < squares.len:
        squares[i] = (i * i) as u32
        count += 1
        i += 1
    return i
pub let filled = fill()
pub fn get(i: i32) -> i32:
    return squares[i as uint] as i32
pub fn bump() -> i32:
    count += 1
    return count
";
        let mut started = Started::of(src);
        assert_eq!(
            started.bytes(0, 16),
            [0, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 9, 0, 0, 0]
        );
        assert_eq!(started.global("count"), 4);
        assert_eq!(started.global("untouched"), 5);
        assert_eq!(started.global("filled"), 4);
        assert_eq!(started.call("get", &[3]), 9);
        assert_eq!(started.call("bump", &[]), 5);
    }

    #[test]
    fn a_module_starts_with_what_its_constants_built() {
        // A list that is linked while the program is compiled.
        let src = "\
struct Node:
    value: i32
    next: &Node
let end = &Node(value: 0, next: 0)
let nodes: varray(Node) = [Node(value: 0, next: end); 3]
fn link() -> &Node:
    var i: uint = 0
    var head = end
    while i < nodes.len:
        nodes[i] = Node(value: (i + 1) as i32 * 10, next: head)
        head = &nodes[i]
        i += 1
    return head
let head = link()
pub fn sum() -> i32:
    var total = 0
    var at = head
    while at.value != 0:
        total += at.value
        at = at.next
    return total
";
        assert_eq!(Started::of(src).call("sum", &[]), 60);
    }

    #[test]
    fn a_module_starts_with_the_memory_its_constants_grew() {
        let src = "\
fn far() -> &var u32:
    module.grow(2)
    let p = (70000 as uint) as! &var u32
    p.* = 0xdeadbeef
    return p
let text = \"hi\"
let p = far()
pub let size = module.size() as i32
pub fn read() -> i32:
    return (p.* >> 16) as i32
";
        let module = lower(src);
        assert_eq!(exported(&module), "size=3");
        assert_eq!(module.memory.min_pages, 3);
        let offsets: Vec<_> = module.data.iter().map(|data| data.offset).collect();
        assert_eq!(offsets, [0, 70000]);
        let mut started = Started::of(src);
        assert_eq!(started.pages(), 3);
        assert_eq!(started.bytes(0, 2), *b"hi");
        assert_eq!(started.bytes(70000, 4), [0xef, 0xbe, 0xad, 0xde]);
        assert_eq!(started.call("read", &[]), 0xdead);
    }

    #[test]
    fn literals_placed_after_a_run_are_as_written() {
        // `scribble` writes where `later` is then placed.
        let src = "\
fn scribble() -> i32:
    module.fill(0 as uint as! &var u8, 0xff, 64)
    return 1
let first = \"ab\"
let ran = scribble()
let zeros: array(u8) = [0; 4]
let later: array(u8) = [7, 8]
let last = sum(zeros) + sum(later)
fn sum(of: array(u8)) -> i32:
    var total = 0
    for x in of:
        total += x as i32
    return total
pub let total = last
pub fn at(i: i32) -> i32:
    return module.memory()[i as uint] as i32
";
        let mut started = Started::of(src);
        assert_eq!(started.global("total"), 15);
        assert_eq!(
            started.bytes(0, 10),
            [0xff, 0xff, 0, 0, 0, 0, 7, 8, 0xff, 0xff]
        );
        assert_eq!(started.call("at", &[7]), 8);
    }

    #[test]
    fn global_initializers_call_functions() {
        let src = "\
fn fib(n: i32) -> i32:
    var (a, b) = (0, 1)
    var i = 0
    while i < n:
        let sum = a + b
        a = b
        b = sum
        i += 1
    return a
pub struct P:
    x: i32
    y: f64
fn make(x: i32) -> P:
    return P(x: x, y: 0.5)
pub let tenth = fib(10)
pub let next = fib(tenth - 44) + 1
pub let p = make(3)
pub var v = make(tenth).x
";
        assert_eq!(consts(src), "tenth=55 next=90 p.x=3 p.y=0.5f64 v=55");
    }

    #[test]
    fn defers_run_in_order_as_each_block_is_left() {
        let src = "\
var trace = 0
fn note(n: i32):
    trace = trace * 10 + n
fn run() -> i32:
    defer note(1)
    var i = 0
    while i < 2:
        defer note(2)
        i += 1
        defer note(3)
        note(4)
    return trace
fn early(stop: bool) -> i32:
    trace = 0
    defer note(1)
    while true:
        defer note(2)
        if stop:
            break
        return 7
    defer note(3)
    note(4)
    return trace
fn nested() -> i32:
    trace = 0
    defer:
        defer note(1)
        note(2)
    for n in Step:
        defer note(n as i32)
        if n == .skipped:
            continue
        note(5)
    return 0
enum(i32) Step:
    kept = 6
    skipped
pub let ran = run()
pub let after = trace
pub let broke = early(true)
pub let then = trace
pub let quit = early(false)
pub let last = trace
pub let _ = nested()
pub let inner = trace
";
        // A `return` is what it was before its defers ran, and a defer that
        // wasn't reached doesn't run.
        assert_eq!(
            consts(src),
            "ran=432432 after=4324321 broke=24 then=2431 quit=7 last=21 inner=56721"
        );
    }

    #[test]
    fn every_kind_of_constant_calls_functions() {
        let src = "\
fn twice(x: i32) -> i32:
    return x * 2
enum(i32) Size:
    small = twice(2)
    large
struct Box:
    side: i32 = twice(Size.large as i32)
fn area(w: i32 = twice(3), h: i32 = Box().side) -> i32:
    return w * h
pub let size = Size.large as i32
pub let side = Box().side
pub let a = area()
pub let b = area(h: 1)
";
        assert_eq!(consts(src), "size=5 side=10 a=60 b=6");
    }

    #[test]
    fn functions_are_lowered_with_the_constants_they_read() {
        // `late` is folded for `uses_late`, which `first` calls.
        let src = "\
pub let first = uses_late() + 1
fn uses_late() -> i32:
    return late * 2
let late = base() + 1
fn base() -> i32:
    return 20
";
        assert_eq!(consts(src), "first=43");
    }

    #[test]
    fn constants_call_generic_functions_and_compare_arrays() {
        let src = "\
fn(T) pick(first: bool, a: T, b: T) -> T:
    if first:
        return a
    return b
fn kind(s: array(u8)) -> i32:
    match s:
        \"one\":
            return 1
        \"two\":
            return 2
        else:
            return 0
let word = \"two\"
pub let picked = pick(false, 1, 2) + pick(true, 10, 20)
pub let same = word == \"two\"
pub let matched = kind(pick(true, word, \"one\"))
";
        assert_eq!(consts(src), "picked=12 same=1 matched=2");
    }

    #[test]
    fn constants_run_in_order_on_one_state() {
        let src = "\
var count = 0
fn next() -> i32:
    count += 1
    return count
pub let a = next()
pub let b = (next(), next())
pub let c = next() * 10 + count
";
        assert_eq!(consts(src), "a=1 b.0=2 b.1=3 c=44");
    }

    #[test]
    fn constants_read_and_write_memory() {
        let src = "\
let squares: varray(u32) = [0; 5]
let seven = &var 0
fn fill(out: varray(u32)) -> uint:
    var i: uint = 0
    while i < out.len:
        out[i] = (i * i) as u32
        i += 1
    seven.* = 7
    return i
fn sum(of: array(u32)) -> u32:
    var total: u32 = 0
    for x in of:
        total += x
    return total
pub let filled = fill(squares)
pub let total = sum(squares) + squares[4]
pub let read = seven.*
";
        assert_eq!(consts(src), "filled=5 total=46 read=7");
    }

    #[test]
    fn literals_hold_what_is_only_known_by_running_it() {
        let src = "\
var count = 0
fn next() -> i32:
    count += 1
    return count
struct P:
    x: i32
    y: i32
let list = [next(), 5, next()]
let copies = [P(x: next(), y: 9); 3]
let cell = &var next()
let sized: array(u8) = [1; next() as uint]
pub let first = list[0] * 100 + list[1] * 10 + list[2]
pub let second = copies[0].x * 100 + copies[2].x * 10 + copies[1].y
pub let third = cell.*
pub let len = sized.len
pub let calls = count
";
        assert_eq!(consts(src), "first=152 second=339 third=4 len=5 calls=5");
    }

    #[test]
    fn a_repeat_counts_before_the_rest_of_its_initializer_runs() {
        let src = "\
var count = 0
fn next() -> i32:
    count += 1
    return count
let pair: tuple(i32, array(u8)) = (next(), [0; next() as uint])
pub let first = pair.0
pub let len = pair.1.len
";
        assert_eq!(consts(src), "first=2 len=1");
    }

    #[test]
    fn constants_call_through_the_pointers_they_name() {
        let src = "\
fn double(x: i32) -> i32:
    return x * 2
fn triple(x: i32) -> i32:
    return x * 3
fn apply(f: fn(i32) -> i32, x: i32) -> i32:
    return f(x)
fn each(fs: array(fn(i32) -> i32), x: i32) -> i32:
    var total = 0
    for f in fs:
        total += f(x)
    return total
let both = [double, triple]
var held: fn(i32) -> i32 = triple
fn through() -> i32:
    return held(100)
pub let direct = apply(double, 4)
pub let listed = each(both, 5)
pub let kept = through()
";
        assert_eq!(consts(src), "direct=8 listed=25 kept=300");
    }

    #[test]
    fn a_pointer_does_not_put_a_constant_in_its_own_definition() {
        // `on_event` reads `limit`, but nothing `limit` runs names it.
        let src = "\
let handlers = [on_event]
pub let limit = compute()
fn compute() -> i32:
    return 7
fn on_event(x: i32) -> i32:
    return x + limit
pub let handled = handlers[0](1)
";
        assert_eq!(consts(src), "limit=7 handled=8");
    }

    #[test]
    fn a_constant_its_own_code_reads_is_in_its_own_definition() {
        let src = "\
let a = f()
fn f() -> i32:
    return g()
fn g() -> i32:
    return b
let b = f()
";
        let recursive = |name: &str| format!("`{name}` is used in its own definition");
        assert_eq!(errors_at(src), [(recursive("b"), "f()")]);

        let src = "\
let c = read()
fn read() -> i32:
    return c
";
        assert_eq!(errors_at(src), [(recursive("c"), "c")]);
    }

    #[test]
    fn traps_name_the_functions_that_were_running() {
        let src = "\
fn divide(a: i32, b: i32) -> i32:
    return a / b
fn ratio(of: i32) -> i32:
    return divide(of, of - of)
let r = ratio(4)
let after = ratio(1)
";
        let trap = "constant evaluation traps: integer divide by zero, \
                    in `divide`, called from `ratio`";
        // Nothing is run after a failure.
        assert_eq!(errors_at(src), [(trap.to_string(), "ratio(4)")]);

        let src = "\
let items: array(u8) = [1, 2]
fn at(i: uint) -> u8:
    if i > 5:
        module.unreachable()
    return items[i]
let a = at(2)
";
        let (message, at) = &errors_at(src)[0];
        assert!(message.contains("in `at`"), "{message}");
        assert_eq!(*at, "at(2)");
        let src = src.replace("at(2)", "at(9)");
        let (message, _) = &errors_at(&src)[0];
        assert_eq!(
            message,
            "constant evaluation traps: unreachable code is reached, in `at`"
        );
    }

    #[test]
    fn a_function_that_calls_itself_is_named_once() {
        let src = "\
fn down(n: i32) -> i32:
    return down(n + 1) + 1
fn start() -> i32:
    return down(0)
let depth = start()
";
        // Only the innermost of so many are known.
        let trap = "constant evaluation traps: call stack exhausted, in `down`";
        assert_eq!(errors_at(src), [(trap.to_string(), "start()")]);
    }

    #[test]
    fn fuel_bounds_the_constants_of_an_item() {
        let src = "\
fn spin(n: i32) -> i32:
    var i = 0
    while i != n:
        i += 1
    return i
enum(i32) E:
    a = spin(1000)
    b = spin(1001)
pub let quick = spin(1000)
";
        let settings = |fuel| Settings {
            fuel: Some(fuel),
            ..Settings::default()
        };
        let module = check_with(src, &settings(100_000)).unwrap();
        assert_eq!(exported(&module), "quick=1000");
        // The members of one enum share its fuel.
        let errors = check_with(src, &settings(15_000)).unwrap_err();
        let [error] = &errors[..] else {
            panic!("expected one error: {errors:#?}");
        };
        let fuel = "constant evaluation used up its fuel of 15000, in `spin`; \
                    `fuel` under `[const]` in Duck.toml gives it more";
        assert_eq!(error.kind.to_string(), fuel);
        let span = error.span.unwrap();
        assert_eq!(&src[span.start..span.end], "spin(1001)");
    }

    #[test]
    fn constants_never_call_the_host() {
        let src = "\
extern:
    fn now() -> i64
    fn flag() -> bool
fn stamp() -> i64:
    return now() + 1
let t = stamp()
";
        let called = "constant evaluation calls the extern function `now`, in `stamp`";
        assert_eq!(errors_at(src), [(called.to_string(), "stamp()")]);

        // A pointer to one is to the function that calls it.
        let src = "\
extern:
    fn flag() -> bool
let f: fn() -> bool = flag
let b = f()
";
        let called = "constant evaluation calls the extern function `flag`, \
                      in `extern flag`";
        assert_eq!(errors_at(src), [(called.to_string(), "f()")]);
    }

    #[test]
    fn a_pointer_that_only_memory_holds_leads_nowhere() {
        // Nothing `b` names leads to `hidden`: its pointer is read from
        // an address.
        let src = "\
fn hidden() -> i32:
    return 1
let table: array(fn() -> i32) = [hidden]
fn sneak() -> i32:
    let f = (0 as uint) as! &fn() -> i32
    return f.*()
let b = sneak()
";
        let unnamed = "constant evaluation calls `hidden` through a pointer that nothing \
                       the constant names leads to, in `sneak`";
        assert_eq!(errors_at(src), [(unnamed.to_string(), "sneak()")]);
    }

    #[test]
    fn errors_are_found_without_making_the_module() {
        let src = "\
fn half(x: i32) -> i32:
    return x / 2
let fine = half(4)
let bad = half(1) / half(1)
";
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let errors = crate::ty::errors(&program, &Settings::default());
        let kinds: Vec<_> = errors.iter().map(|e| e.kind.to_string()).collect();
        assert_eq!(kinds, ["constant evaluation traps: integer divide by zero"]);
        let fixed = src.replace("half(1) / half(1)", "half(8)");
        let tokens = tokenize(entry, &fixed).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        assert_eq!(crate::ty::errors(&program, &Settings::default()), []);
    }

    #[test]
    fn nothing_runs_after_an_error() {
        let src = "\
fn f() -> i32:
    return true
fn g() -> i32:
    return 1 / (1 - 1)
let a = f()
let b = g()
enum(i32) E:
    x = g()
    y = g()
";
        let errors = check_with(src, &Settings::default()).unwrap_err();
        let kinds: Vec<_> = errors.into_iter().map(|e| e.kind).collect();
        let mismatch = TypeErrorKind::Mismatch {
            expected: "i32".to_string(),
            found: "bool".to_string(),
        };
        assert_eq!(kinds, [mismatch]);
    }

    #[test]
    fn literals_leave_the_pages_a_constant_grew_to_it() {
        let src = "\
fn claim() -> &var u8:
    let page = module.grow(1) as uint
    let p = (page * module.page_size) as! &var u8
    p.* = 0xaa
    return p
let first = \"a\"
let mine = claim()
let fits = \"bc\"
let large: array(u8) = [7; 70000]
let last = \"d\"
pub let kept = mine.*
pub let pages = module.size() as i32
pub fn read() -> i32:
    return mine.* as i32
pub fn grow() -> i32:
    return module.grow(1) as i32
";
        let module = lower(src);
        assert_eq!(exported(&module), "kept=170 pages=4");
        // `fits` is in the page `first` is, and `large`, which that page has
        // no room for, is past the one `claim` grew.
        let segments = module.data.iter();
        let segments: Vec<_> = segments
            .map(|data| (data.offset, data.bytes.len()))
            .collect();
        assert_eq!(segments, [(0, 3), (65536, 1), (131072, 70001)]);
        assert_eq!(module.memory.min_pages, 4);
        let mut started = Started::of(src);
        assert_eq!(started.bytes(0, 4), *b"abc\0");
        assert_eq!(started.bytes(131072 + 69999, 3), [7, b'd', 0]);
        assert_eq!(started.call("read", &[]), 0xaa);
        // The module grows from where its constants left off.
        assert_eq!(started.call("grow", &[]), 4);
    }

    #[test]
    fn literals_fill_the_pages_after_theirs_if_no_constant_grew_memory() {
        let src = "\
fn count() -> i32:
    return module.size() as i32
let first = \"a\"
pub let before = count()
let large: array(u8) = [7; 70000]
pub let after = count()
";
        let module = lower(src);
        assert_eq!(exported(&module), "before=1 after=2");
        let segments = module.data.iter();
        let segments: Vec<_> = segments
            .map(|data| (data.offset, data.bytes.len()))
            .collect();
        assert_eq!(segments, [(0, 70001)]);
        assert_eq!(module.memory.min_pages, 2);
    }

    #[test]
    fn a_function_reads_its_literals_whenever_it_is_called() {
        let src = "\
let LIMIT: uint = 2
fn sum(a: array(i32)) -> i32:
    var total = 0
    for x in a:
        total += x
    return total
pub fn lengths(i: i32) -> i32:
    let words = [\"ab\", \"cde\"]
    let sevens = [7; LIMIT + 2]
    return sum([1, 2, 3]) + words[i as uint].len as i32 + sevens[3]
pub fn steps(n: i32) -> i32:
    let first = [0, 1]
    if n < 2:
        return first[n as uint]
    # Each call that is running reads the one `first`.
    return steps(n - 1) + steps(n - 2) + first[1]
pub fn late(i: i32) -> i32:
    let primes: array(u8) = [2, 3, 5, 7]
    var total = 0
    for word in [\"cde\", \"fghi\"]:
        total += word.len as i32
    return primes[i as uint] as i32 + total
pub let folded = lengths(1)
pub let stepped = steps(6)
";
        let module = lower(src);
        assert_eq!(exported(&module), "folded=16 stepped=20");
        let mut started = Started::of(src);
        // Those of a function that a constant called are as they were.
        assert_eq!(started.call("lengths", &[0]), 15);
        assert_eq!(started.call("lengths", &[1]), 16);
        assert_eq!(started.call("steps", &[6]), 20);
        // Those of one that none called are placed after it ran.
        assert_eq!(started.call("late", &[3]), 14);
    }

    #[test]
    fn a_function_in_a_function_runs_for_a_constant_and_for_the_host() {
        let src = "\
var trace = 0
fn note(n: i32):
    trace = trace * 10 + n
fn word(s: array(u8)) -> i32:
    fn number(s: array(u8)) -> i32:
        defer note(1)
        match s:
            \"two\":
                return 2
            else:
                return 0
    return number(s) + number(\"one\")
pub fn factorial(n: i32) -> i32:
    fn fact(n: i32) -> i32:
        if n < 2:
            return 1
        return n * fact(n - 1)
    var total = 0
    for step in [1, 1]:
        fn times(a: i32, b: i32) -> i32:
            return a * b
        total += times(step, fact(n))
    return total
pub let two = word(\"two\")
pub let ran = trace
";
        assert_eq!(consts(src), "two=2 ran=11");
        assert_eq!(Started::of(src).call("factorial", &[5]), 240);
    }
}

//! Constants that are only known by running them: a global initializer, an
//! enum member's value or a default that calls a function, or reads what
//! one may have written.
//!
//! Such a constant is run as a function of its own, in a module with the
//! functions it may call, once the program is [linked](super::link): on the
//! state of the program as lowering left it where the constant is. Each
//! function is lowered here the first time a constant may call it, and has
//! what it reads folded first, so a constant is run with everything it
//! names, and is in its own definition if that leads back to it. What the
//! runs leave in memory and in the globals is what the module starts with.
//!
//! A constant may call the functions it calls by name, those it takes a
//! pointer to, and those that the constants it reads do, and so on through
//! each of them: [`Dep`] records what each names. A pointer that only
//! memory holds leads to its function if an earlier run could have called
//! it, and otherwise to one that traps.

use std::mem;

use rustc_hash::FxHashSet;

use crate::eval;
use crate::ir::{self, Expr, FuncId, Stmt, Symbol};
use crate::lex::Span;
use crate::load::Program;

use super::{
    Checker, Finding, Fold, InstanceSite, Scalar, TypeErrorKind, Value, ValueDef, exprs, fn_decls,
};

/// The fuel the constants of one item run on, unless the settings say: about
/// a second's worth, as the evaluator runs them.
pub const DEFAULT_FUEL: u64 = 300_000_000;

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
    /// Lowers function `id` before its turn: for a constant to call, while
    /// constants are still being folded, or for what its result hides.
    /// The constants that its body is first to read are folded for it.
    pub(super) fn lower_early(&mut self, program: &Program, id: FuncId) {
        let first = self.funcs.len() - self.synths.len();
        let normal = mem::replace(&mut self.normal, false);
        match (id.0 as usize) < first {
            true => {
                let defined = (id.0 - self.import_count) as usize;
                let (item, decl) = fn_decls(program).nth(defined).unwrap();
                self.lower_kept(program, id, |ck, program| {
                    ck.lower_decl(program, id, item, decl)
                });
            }
            false => self.lower_kept(program, id, |ck, program| ck.lower_synth(program, id)),
        }
        self.normal = normal;
    }

    /// Lowers function `id` with `lower`, keeping what it names for a
    /// constant that is run later to call it. One lowered in the turn of its
    /// package, rather than for a constant, is kept as one that no run has
    /// reached.
    pub(super) fn lower_kept(
        &mut self,
        program: &Program,
        id: FuncId,
        lower: impl FnOnce(&mut Self, &Program) -> ir::Func,
    ) {
        self.lowering.insert(id);
        self.deps.push(Vec::new());
        // What is folding may be in another module, or a generic function's.
        let module = self.module;
        let type_params = mem::take(&mut self.type_params);
        let chain = mem::take(&mut self.instance_chain);
        let func = lower(self, program);
        self.module = module;
        self.type_params = type_params;
        self.instance_chain = chain;
        let deps = self.deps.pop().unwrap_or_default();
        self.func_deps.insert(id, deps);
        self.lowering.remove(&id);
        self.keep_lowered(id, func);
    }

    /// Keeps `func`, function `id` lowered, as one lowered for a constant
    /// to call unless it is lowered in the turn of its package.
    pub(super) fn keep_lowered(&mut self, id: FuncId, func: ir::Func) {
        if self.normal {
            self.normally.insert(id);
        }
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
    ) -> Option<FxHashSet<FuncId>> {
        let mut work = self.deps.last().cloned().unwrap_or_default();
        push_calls(&thunk.body, &mut work);
        // Only a function that is lowered for a constant has run, or been
        // run by one that has, or one that a run has reached.
        let ran = |id: &&FuncId| {
            let early = self.lowered.contains_key(id) && !self.normally.contains(id);
            early || self.ran.contains(id)
        };
        let pointed = self.table.iter().filter(ran);
        work.extend(pointed.map(|id| Dep::Func(*id)));
        let (mut funcs, mut items) = (FxHashSet::default(), FxHashSet::default());
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
                // One of a package that is compiled already has its body in
                // its artifact, which linking has: what it calls is found
                // then, and what it names is known.
                Dep::Func(id) if self.is_foreign(id) => {
                    work.extend(self.func_deps.get(&id).into_iter().flatten());
                    continue;
                }
                Dep::Func(id) => id,
            };
            if self.lowering.contains(&id) {
                let folding = self.folding.last().copied();
                let name = folding.map_or_else(String::new, |index| self.item_name(program, index));
                self.error(TypeErrorKind::RecursiveConstant(name), span);
                return None;
            }
            if !self.lowered.contains_key(&id) {
                self.lower_early(program, id);
            }
            work.extend(self.func_deps.get(&id).into_iter().flatten());
            push_calls(&self.lowered[&id].body, &mut work);
        }
        Some(funcs)
    }

    /// The scalars of the lowered constant `value`, whose temporaries are
    /// `locals`: folded, or else found by running it, with every function
    /// it calls, once the program is linked. `None` after reporting, at
    /// `span`, why it has none, or if it isn't run.
    pub(super) fn evaluate(
        &mut self,
        program: &Program,
        locals: Vec<ir::Local>,
        value: Value,
        span: Span,
    ) -> Option<Vec<Scalar>> {
        match self.fold_value(&value) {
            Ok(scalars) => Some(scalars),
            Err(Fold::Trap) => {
                self.error(TypeErrorKind::ConstTrap, span);
                None
            }
            Err(Fold::Linked) => Some(self.fold_linked(value, span)),
            Err(Fold::NotConstant) => self.run(program, locals, value, span),
        }
    }

    /// The scalars of the lowered constant `value`, which is made of
    /// constants alone, some of which only linking knows: it is folded
    /// once they are known, and a trap is reported then, at `span`.
    pub(super) fn fold_linked(&mut self, value: Value, span: Span) -> Vec<Scalar> {
        let results = value.scalars.iter().map(|(ty, _)| *ty).collect();
        let thunk = ir::Func {
            name: String::new(),
            exports: Vec::new(),
            params: Vec::new(),
            results,
            locals: Vec::new(),
            body: vec![Stmt::Return(exprs(value.scalars))],
        };
        self.find(Finding::Fold(thunk), span)
    }

    /// Runs the lowered constant `value`, whose temporaries are `locals`,
    /// once the program is linked, and returns each of its scalars, which
    /// only linking knows. `None` after reporting, at `span`, why it has
    /// none, or if it isn't run: after any error, nothing is, as what an
    /// error leaves lowered may not be valid.
    fn run(
        &mut self,
        program: &Program,
        locals: Vec<ir::Local>,
        value: Value,
        span: Span,
    ) -> Option<Vec<Scalar>> {
        if !self.errors.is_empty() {
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
        if !self.errors.is_empty() {
            return None;
        }
        self.ran.extend(&reached);
        Some(self.find(Finding::Run { thunk, reached }, span))
    }

    /// The scalars of the constant that linking finds as `how` says, of
    /// types `results`, where the program has been lowered to here. What
    /// fails of it is reported at `span`.
    pub(super) fn find(&mut self, how: Finding, span: Span) -> Vec<Scalar> {
        let results = match &how {
            Finding::Fold(thunk) | Finding::Run { thunk, .. } => thunk.results.clone(),
            Finding::Count { prim, .. } => vec![prim.val_type()],
        };
        let mut instances = Vec::new();
        let mut at = span;
        for instance in &self.instance_chain {
            instances.push(InstanceSite {
                name: instance.name.clone(),
                span: at,
            });
            at = instance.call;
        }
        instances.reverse();
        let id = self.link.find(ValueDef {
            how,
            item: self.folding.last().copied(),
            span: at,
            instances,
            funcs: self.funcs.len(),
            globals: self.ir_globals.len(),
            table: self.table.len(),
            errors: self.errors.len(),
        });
        let scalars = results.into_iter().enumerate();
        let scalars =
            scalars.map(|(index, ty)| Scalar::Linked(ty, Symbol::Value(id, index as u32)));
        scalars.collect()
    }
}

/// Adds each function that `body` calls by name to `out`.
pub(super) fn push_calls(body: &[Stmt], out: &mut Vec<Dep>) {
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
        Expr::Const(_) | Expr::Symbol(..) | Expr::Local(_) | Expr::Global(_) | Expr::MemorySize => {
        }
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
    use super::super::{TypeError, check};
    use super::*;
    use crate::file::{DummyManager, FileManager, Settings};
    use crate::ir::Const;
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

        /// Whether the exported function `name`, from `i32`s to an `i32`,
        /// traps when it is called with `args`.
        fn traps(&mut self, name: &str, args: &[i32]) -> bool {
            let func = self.instance.get_func(&mut self.store, name).unwrap();
            let args: Vec<_> = args.iter().map(|arg| wasmtime::Val::I32(*arg)).collect();
            let mut results = [wasmtime::Val::I32(0)];
            func.call(&mut self.store, &args, &mut results).is_err()
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
        // One segment, from `text` to what `far` wrote.
        let segments = module.data.iter();
        let segments: Vec<_> = segments
            .map(|data| (data.offset, data.bytes.len()))
            .collect();
        assert_eq!(segments, [(0, 70004)]);
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
    fn a_constant_runs_among_functions_it_never_calls() {
        // What a constant calls is not where the program has it in the
        // module that runs it, which leaves `idle`, `spare` and `last` out:
        // by name or through a pointer, each call still reaches its own.
        let src = "\
fn idle() -> i32:
    return 1
fn double(x: i32) -> i32:
    return x * 2
fn spare(x: i32) -> i32:
    return idle() + x
fn triple(x: i32) -> i32:
    return x * 3
fn apply(f: fn(i32) -> i32, x: i32) -> i32:
    return f(x)
fn last() -> i32:
    return apply(spare, 1)
var held: fn(i32) -> i32 = spare
pub let named = triple(double(1))
pub let pointed = apply(triple, 4)
pub let both = apply(double, 5) + triple(1)
";
        assert_eq!(consts(src), "named=6 pointed=12 both=13");

        // A failure names them as the program does.
        let src = "\
fn idle() -> i32:
    return 1
fn divide(a: i32, b: i32) -> i32:
    return a / b
fn spare() -> i32:
    return idle()
fn ratio(of: i32) -> i32:
    return divide(of, of - of)
var held: fn() -> i32 = spare
let r = ratio(4)
";
        let trap = "constant evaluation traps: integer divide by zero, \
                    in `divide`, called from `ratio`";
        assert_eq!(errors_at(src), [(trap.to_string(), "ratio(4)")]);

        // One that only the table leads to is still the one that is named.
        let src = "\
fn idle() -> i32:
    return 1
fn hidden() -> i32:
    return 2
let table: array(fn() -> i32) = [idle, hidden]
fn sneak() -> i32:
    let f = (4 as uint) as! &fn() -> i32
    return f.*()
let b = sneak()
";
        let unnamed = "constant evaluation calls `hidden` through a pointer that nothing \
                       the constant names leads to, in `sneak`";
        assert_eq!(errors_at(src), [(unnamed.to_string(), "sneak()")]);
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
    fn members_count_up_from_one_that_is_run() {
        let src = "\
fn three() -> u8:
    return 3
fn top() -> u8:
    return 255
enum(u8) E:
    a = three()
    b
    c
pub let b = E.b as u8
pub let c = E.c as u8
";
        assert_eq!(consts(src), "b=4 c=5");
        // Linking counts as checking would, past the type as well.
        let src = "\
fn top() -> u8:
    return 255
enum(u8) F:
    x = top()
    y
";
        let error = "member `y` counts past the largest `u8`".to_string();
        assert_eq!(errors_at(src), [(error, "y")]);
    }

    #[test]
    fn members_that_are_run_are_told_apart_once_they_are() {
        let same = |member: &str, other: &str| {
            format!("member `{member}` has the same value as `{other}`")
        };
        let src = "\
fn three() -> i32:
    return 3
enum(i32) E:
    a = three()
    b = 3
";
        assert_eq!(errors_at(src), [(same("b", "a"), "b = 3")]);
        // From the first that is run, each is compared with every one
        // before it, in order.
        let src = "\
fn three() -> i32:
    return 3
enum(i32) G:
    a = three()
    b = 1
    c = 1
    d = 3
";
        assert_eq!(
            errors_at(src),
            [(same("c", "b"), "c = 1"), (same("d", "a"), "d = 3")]
        );
        // Those before it are told apart by checking, and once: nothing is
        // run after its error, so the rest aren't known.
        let src = "\
fn three() -> i32:
    return 3
enum(i32) H:
    a = 1
    b = 1
    c = three()
    d = 3
";
        assert_eq!(errors_at(src), [(same("b", "a"), "b = 1")]);
    }

    #[test]
    fn what_is_folded_of_a_constant_that_is_run_traps_where_it_is() {
        let src = "\
fn zero() -> i32:
    return 0
let a = zero()
let b = 10 / a
";
        let error = "constant evaluation traps".to_string();
        assert_eq!(errors_at(src), [(error, "10 / a")]);
    }

    #[test]
    fn copies_that_a_run_counts_hold_their_value_if_there_are_any() {
        // What is copied is made once, whether or not it is stored.
        let src = "\
var made = 0
fn make() -> i32:
    made += 1
    return 7
fn three() -> uint:
    return 3
fn none() -> uint:
    return 0
let filled: varray(i32) = [make(); three()]
let empty: varray(i32) = [make(); none()]
pub let firsts = filled[0] + filled[2]
pub let calls = made
pub let lens = (filled.len + empty.len) as i32
";
        assert_eq!(consts(src), "firsts=14 calls=2 lens=3");
    }

    #[test]
    fn a_writable_literal_that_a_run_counts_is_shared_if_it_holds_any() {
        let src = "\
fn none() -> uint:
    return 0
fn three() -> uint:
    return 3
let N = none()
let M = three()
fn f() -> uint:
    let a: varray(u8) = [0; N]
    let b: varray(u8) = [0; M]
    return a.len + b.len
";
        let error = "a writable literal in a function is shared by every call, so it must be empty";
        assert_eq!(errors_at(src), [(error.to_string(), "[0; M]")]);
    }

    #[test]
    fn a_folded_constant_is_what_running_it_makes() {
        // To the bits of a NaN, which a machine's own arithmetic may give
        // any of.
        let src = "\
fn zero() -> f64:
    return 0.0
pub let folded = 0.0 / 0.0
pub let run = zero() / zero()
pub let narrowed = (0.0 / 0.0) as f32
";
        let bits: Vec<_> = lower(src)
            .globals
            .iter()
            .map(|global| match global.init {
                Const::F32(x) => u64::from(x.to_bits()),
                Const::F64(x) => x.to_bits(),
                c => panic!("{c:?} is no float"),
            })
            .collect();
        assert_eq!(
            bits,
            [0x7ff8_0000_0000_0000, 0x7ff8_0000_0000_0000, 0x7fc0_0000]
        );
    }

    #[test]
    fn constants_grow_memory_to_32_mib_at_most() {
        // Whatever the settings let the host grow it to.
        let src = "\
fn take(pages: uint) -> int:
    return module.grow(pages)
pub let past = take(513) as i32
pub let all = take(512) as i32
pub let more = take(1) as i32
pub let none = take(0) as i32
";
        assert_eq!(consts(src), "past=-1 all=0 more=-1 none=512");
        let module = lower(src);
        assert_eq!(
            (module.memory.min_pages, module.memory.max_pages),
            (512, None)
        );
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
        assert_eq!(segments, [(0, 131072 + 70001)]);
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
    fn for_loops_count_what_they_iterate() {
        let src = "\
enum(i32) Step:
    first = 10
    second = 20
    third
fn weigh(a: array(i32)) -> i32:
    var total = 0
    for i, x in a:
        if x == 0:
            continue
        total += x * (i as i32 + 1)
    return total
fn spread(pairs: array(tuple(i32, i32))) -> i32:
    var total = 0
    for i, (low, high) in pairs:
        total += (high - low) * i as i32
    return total
fn steps() -> i32:
    var total = 0
    for i, step in Step:
        if step == .second:
            continue
        total += step as i32 * (i as i32 + 1)
    return total
pub let weighed = weigh([5, 0, 7])
pub let spreads = spread([(1, 9), (2, 5), (0, 4)])
pub let stepped = steps()
";
        let mut started = Started::of(src);
        assert_eq!(started.global("weighed"), 5 + 7 * 3);
        assert_eq!(started.global("spreads"), 3 + 4 * 2);
        assert_eq!(started.global("stepped"), 10 + 21 * 3);
    }

    #[test]
    fn for_loops_count_from_a_start_up_to_an_end() {
        let src = "\
var calls = 0
fn bound(n: i32) -> i32:
    calls += 1
    return n
fn sum(from: i32, to: i32) -> i32:
    var total = 0
    for i in bound(from)..bound(to):
        if i == 0:
            continue
        total += i
    return total
fn bytes() -> i32:
    var count = 0
    for b in 250..255 as u8:
        count += b as i32 - 249
    return count
fn wide(from: i64) -> i32:
    var count = 0
    for n in from..0x7fff_ffff_ffff_ffff:
        if n == 0x1_0000_0001:
            break
        count += 1
    return count
pub let up = sum(-2, 4)
pub let none = sum(4, 4) + sum(5, -5)
pub let read = calls
pub let narrow = bytes()
pub let crossed = wide(0xffff_fffe)
";
        let mut started = Started::of(src);
        // From -2 to 3, without the 0 that it skips.
        assert_eq!(started.global("up"), 3);
        // Nothing where the start isn't less than the end.
        assert_eq!(started.global("none"), 0);
        assert_eq!(started.global("read"), 6);
        assert_eq!(started.global("narrow"), 1 + 2 + 3 + 4 + 5);
        assert_eq!(started.global("crossed"), 3);
    }

    #[test]
    fn slices_view_the_elements_between_their_bounds() {
        let src = "\
struct(T) Vec:
    use varray(T)
    cap: uint
let numbers: varray(i32) = [1, 2, 3, 4, 5]
let vec = &var Vec(i32)(ptr: numbers.ptr, len: 4, cap: numbers.len)
fn sum(a: array(i32)) -> i32:
    var total = 0
    for x in a:
        total += x
    return total
fn(T, A: array(T)) tail(a: A) -> array(T):
    return a[1..]
pub fn between(from: i32, to: i32) -> i32:
    return sum(numbers[from as uint..to as uint])
pub fn after(from: i32) -> i32:
    return sum(numbers[from as uint..])
pub fn before(to: i32) -> i32:
    return sum(numbers[..to as uint])
pub fn double(from: i32) -> i32:
    # Through the pointer, as `vec[i]` is, and only its `len` elements.
    let rest = vec[from as uint..]
    for i, x in rest:
        rest[i] = x * 2
    return sum(numbers[..]) * 10 + rest.len as i32
pub let middle = between(1, 4)
pub let none = between(2, 2) + after(5) + before(0)
pub let all = sum(numbers[..]) + sum(tail(numbers)) + sum(tail(vec.*))
pub let text = \"hello\"[1..3] == \"el\"
";
        let mut started = Started::of(src);
        assert_eq!(started.global("middle"), 2 + 3 + 4);
        assert_eq!(started.global("none"), 0);
        assert_eq!(started.global("all"), 15 + 14 + 9);
        assert_eq!(started.global("text"), 1);
        assert_eq!(started.call("after", &[3]), 4 + 5);
        assert_eq!(started.call("before", &[2]), 1 + 2);
        // It traps unless `start <= end <= len`.
        for (from, to) in [(3, 2), (0, 6), (6, 6), (-1, 2)] {
            assert!(started.traps("between", &[from, to]), "{from}..{to}");
        }
        assert!(started.traps("after", &[6]));
        assert!(started.traps("before", &[6]));
        assert!(started.traps("double", &[5]));
        assert_eq!(started.call("double", &[2]), (1 + 2 + 6 + 8 + 5) * 10 + 2);
    }

    #[test]
    fn for_loops_write_through_a_pointer_to_each_element() {
        let src = "\
struct Pair:
    low: i32
    high: i32
struct(T) Vec:
    use varray(T)
    cap: uint
let pairs: varray(Pair) = [Pair(low: 1, high: 0), Pair(low: 2, high: 0), Pair(low: 3, high: 0)]
let vec = &var Vec(Pair)(ptr: pairs.ptr, len: 2, cap: pairs.len)
fn widen() -> i32:
    for i, &var pair in vec.*:
        if pair.low == 1:
            continue
        pair.high = pair.low * 10 + i as i32
    for &var pair in pairs[2..]:
        pair.* = Pair(low: 7, high: 8)
    var total = 0
    for &pair in pairs:
        total = total * 100 + pair.low * 10 + pair.high
    return total
pub let widened = widen()
";
        let mut started = Started::of(src);
        // The first is skipped, the second is written through `vec`, which
        // has two, and the third through the slice.
        assert_eq!(started.global("widened"), 10_00_00 + (20 + 21) * 100 + 78);
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

    #[test]
    fn a_closure_runs_with_what_it_captured_where_it_was_declared() {
        let src = "\
struct(F: fn(i32) -> i32) Held:
    tag: u8
    f: F
let cell = &var 0
let slots: varray(i32) = [0; 3]
fn(F: fn(i32) -> i32) call(x: i32, f: F) -> i32:
    return f(x)
fn(F) keep(f: F) -> F:
    return f
fn(F: fn(i32) -> i32) stored(at: &var Held(F), f: F, x: i32) -> i32:
    at.* = Held(F)(tag: 7, f: f)
    return at.f(x) + at.tag as i32
pub fn copied(n: i32) -> i32:
    var k = n
    fn add(x: i32) -> i32:
        return x + k
    k = 100
    return add(1) * 1000 + k
pub fn written(n: i32) -> i32:
    let total = cell
    fn tally(x: i32):
        total.* += x
        slots[1] = x
    tally(n)
    tally(n + 1)
    return cell.* * 100 + slots[1]
pub fn passed(n: i32) -> i32:
    fn scale(x: i32) -> i32:
        return x * n
    let kept = keep(scale)
    return call(3, scale) + kept(4)
pub fn looped(n: i32) -> i32:
    var sum = 0
    var i = 0
    while i < n:
        fn plus(x: i32) -> i32:
            return x + i
        i += 1
        sum = sum * 10 + plus(0)
    return sum
pub fn held(n: i32) -> i32:
    fn twice(x: i32) -> i32:
        return x * 2 + n
    let at = module.grow(1) as uint * module.page_size
    return stored(at as! &var Held(twice), twice, 5)
pub fn deep(n: i32) -> i32:
    fn outer(d: i32) -> i32:
        fn inner(x: i32) -> i32:
            if x > 0:
                return outer(x - 1) + n
            return d
        return inner(d)
    return outer(3)
fn folded() -> i32:
    let base = 40
    fn more(x: i32) -> i32:
        return base + x
    return call(2, more)
pub let constant = folded()
";
        assert_eq!(consts(src), "constant=42");
        let mut started = Started::of(src);
        // A capture is as its variable was, whatever that is by the call.
        assert_eq!(started.call("copied", &[5]), 6100);
        // What it points to is the same memory.
        assert_eq!(started.call("written", &[2]), 503);
        assert_eq!(started.call("passed", &[5]), 35);
        // Each time its statement runs, it has what is there then.
        assert_eq!(started.call("looped", &[3]), 12);
        // Its captures are stored and read as a struct of them is.
        assert_eq!(started.call("held", &[1]), 18);
        assert_eq!(started.call("deep", &[10]), 30);
    }

    #[test]
    fn what_an_opaque_result_hides_runs_as_itself() {
        let src = "\
struct Head:
    id: i32
struct Named:
    use Head
    more: i32
union ReadError:
    closed
    timeout: u32
union IoError:
    use ReadError
    denied: i64
struct(F: fn(i32) -> i32) Held:
    tag: u8
    f: F
let slot = &var 0
fn(T: Head) id_of(x: T) -> i32:
    return x.id
fn(E: IoError) code(e: E) -> i32:
    match e:
        .timeout(ms):
            return ms as i32
        .denied(at):
            return at as i32
        .closed:
            return -1
fn(F: fn(i32) -> i32) call(x: i32, f: F) -> i32:
    return f(x)
fn(T) hold(x: T) -> opaque(fn() -> T):
    fn get() -> T:
        return x
    return get
fn first(id: i32) -> opaque(Head):
    return Named(id: id, more: 40)
fn failed(ms: u32) -> opaque(IoError):
    if ms == 0:
        return ReadError.closed
    return ReadError.timeout(ms)
fn make_adder(n: i32) -> opaque(fn(i32) -> i32):
    fn add(x: i32) -> i32:
        return x + n
    return add
fn counter(at: &var i32) -> opaque(fn(i32) -> i32):
    fn count(by: i32) -> i32:
        at.* += by
        return at.*
    return count
fn pair(n: i32) -> tuple(opaque(fn(i32) -> i32), option(opaque(Head))):
    if n < 0:
        return (make_adder(0), option(Named).none)
    return (make_adder(n), .some(Named(id: n, more: 1)))
fn held(n: i32) -> Held(opaque(fn(i32) -> i32)):
    fn scale(x: i32) -> i32:
        return x * n
    return Held(scale)(tag: 9, f: scale)
fn again(n: i32) -> opaque(fn(i32) -> i32):
    return make_adder(n + 1)
let add10 = make_adder(10)
pub let folded = add10(5) + call(1, add10)
pub fn adds(n: i32) -> i32:
    var add = make_adder(n)
    let first = add(1)
    add = make_adder(n * 2)
    return first * 100 + call(1, add) + add10(0)
pub fn heads(n: i32) -> i32:
    let named = first(n)
    let head = named as Head
    return named.id * 100 + head.id * 10 + id_of(named)
pub fn fails(ms: i32) -> i32:
    let wide = failed(ms as u32) as IoError
    match failed(ms as u32):
        .timeout(got):
            return got as i32 * 100 + code(failed(ms as u32)) * 10 + code(wide)
        .closed:
            return code(failed(0))
        .denied(_):
            return -2
pub fn counts() -> i32:
    let count = counter(slot)
    let a = count(2)
    return a * 10 + count(3)
pub fn pairs(n: i32) -> i32:
    let (add, head) = pair(n)
    match head:
        .some(named):
            return add(1) * 10 + named.id
        .none:
            return add(7)
pub fn holds(n: i32) -> i32:
    let h = held(n)
    let get = hold(n)
    let wide = hold(n as i64 * 2)
    return h.f(3) * 100 + h.tag as i32 * 10 + get() + wide() as i32 + again(n)(0)
";
        assert_eq!(consts(src), "folded=26");
        let mut started = Started::of(src);
        assert_eq!(started.call("adds", &[3]), 417);
        assert_eq!(started.call("heads", &[4]), 444);
        assert_eq!(started.call("fails", &[5]), 555);
        assert_eq!(started.call("fails", &[0]), -1);
        assert_eq!(started.call("counts", &[]), 25);
        assert_eq!(started.call("pairs", &[4]), 54);
        assert_eq!(started.call("pairs", &[-1]), 7);
        assert_eq!(started.call("holds", &[2]), 699);
    }

    #[test]
    fn an_opaque_type_is_called_and_captured_wherever_it_goes() {
        let src = "\
fn make_adder(n: i32) -> opaque(fn(i32) -> i32):
    fn add(x: i32) -> i32:
        return x + n
    return add
fn(A, R, F: fn(A) -> R) call(f: F, a: A) -> R:
    return f(a)
fn(T) through(x: T, by: i32) -> i32:
    let add = make_adder(by)
    fn apply(n: i32) -> i32:
        return add(n)
    return apply(1) + T.size as i32
fn compose(n: i32) -> opaque(fn(i32) -> i32):
    fn inner(by: i32) -> opaque(fn(i32) -> i32):
        fn scale(x: i32) -> i32:
            return x * by + n
        return scale
    let double = inner(2)
    let add = make_adder(n)
    fn both(x: i32) -> i32:
        return double(add(x))
    return both
pub fn pointed(n: i32) -> i32:
    let make: fn(i32) -> i32 = pointed
    let made = call(make_adder, n)
    return made(1) + (make == pointed) as i32
pub fn generic(n: i32) -> i32:
    return through(n as i64, n) * 10 + through(n as u8, n)
pub fn composed(n: i32) -> i32:
    return compose(n)(1)
";
        let mut started = Started::of(src);
        // A pointer to a function gives what the function hides.
        assert_eq!(started.call("pointed", &[4]), 6);
        assert_eq!(started.call("generic", &[2]), 114);
        assert_eq!(started.call("composed", &[3]), 11);
    }

    #[test]
    fn an_opaque_type_argument_is_used_as_the_declaration_uses_its_parameter() {
        let src = "\
struct(T) Box:
    v: T
struct Head:
    id: i32
struct Named:
    use Head
    more: i32
union ReadError:
    closed
    timeout: u32
union IoError:
    use ReadError
    denied: i64
fn(T) wrap(x: T) -> opaque(Box(T)):
    return Box(T)(v: x)
fn(T) size_of(x: T) -> uint:
    return T.size
fn(T, B: Box(T)) held_size(b: B) -> uint:
    return size_of(b.v)
fn(T) relay(x: T) -> T:
    match x:
        other:
            return other
fn(T) same(x: T) -> T:
    return x as T
fn first() -> opaque(Head):
    return Named(id: 7, more: 8)
fn failed(ms: u32) -> opaque(IoError):
    return ReadError.timeout(ms)
fn(T) hold(x: T, again: i32) -> opaque(fn() -> T):
    fn get() -> T:
        return x
    if again == 0:
        return get
    return hold(x, again - 1)
fn width(T: type, x: i32) -> i32:
    return x + T.size as i32
pub fn sizes() -> i32:
    let narrow = held_size(wrap(3 as u8))
    let wide = held_size(Box(i64)(v: 300))
    return (narrow * 10 + wide) as i32
pub fn relayed(ms: i32) -> i32:
    match relay(failed(ms as u32)):
        .timeout(got):
            return got as i32 + same(first()).id + same(relay(first())).id
        else:
            return -1
pub fn held(n: i32) -> i32:
    return hold(n, 2)() + hold(n as i64, 1)() as i32
pub fn named(n: i32) -> i32:
    fn add(x: i32) -> i32:
        return x + n
    fn inner(f: add) -> i32:
        let g: add = f
        return g(1) + width(add, 0)
    return inner(add) * 10 + width(add, 1)
";
        let mut started = Started::of(src);
        // Whichever instance is lowered first, each reads its own.
        assert_eq!(started.call("sizes", &[]), 18);
        assert_eq!(started.call("relayed", &[5]), 19);
        assert_eq!(started.call("held", &[4]), 8);
        // A function declared in a function is a type where one is given.
        assert_eq!(started.call("named", &[2]), 75);
    }

    #[test]
    fn a_function_generic_over_enums_lists_iterates_and_compares_their_members() {
        let src = "\
enum(u8) Warm:
    red
    green = 5
enum(u8) Color:
    use Warm
    blue
enum Tile:
    grass
    water
    sand
enum(string) Word:
    one = \"one\"
    two = \"two\"
enum(i64) Big:
    low = -3
    high = 7
struct(E: enum) Slot:
    value: E
let all = Big.members
fn pick(E: enum, n: uint) -> E:
    let members = E.members
    return members[n % members.len]
fn(E: enum) place(e: E) -> uint:
    for i, m in E:
        if m == e:
            return i
    return 99
fn(C: Color) shade(c: C) -> uint:
    var seen: uint = 0
    for m in C:
        seen += 1
        if m == c:
            break
    return seen
fn(E: enum) last(s: Slot(E)) -> E:
    return E.members[E.members.len - 1]
fn hidden() -> opaque(enum):
    return Tile.water
pub fn picks(n: i32) -> i32:
    let c = pick(Color, n as uint) as u8 as i32
    let w = pick(Word, n as uint) as string
    return c * 10 + w.len as i32 + pick(Big, n as uint) as i64 as i32 * 100
pub fn places() -> i32:
    let p = place(Tile.sand) + place(Word.two) * 10 + place(Big.high) * 100
    return (p + shade(Warm.green) * 1000 + shade(Color.blue) * 10000) as i32
pub fn lists() -> i32:
    let slot = Slot(Big)(value: .low)
    let n = all.len + Tile.members.len * 10 + Color.members[1] as u8 as uint * 100
    let compared = last(slot) == Big.high and not (hidden() != hidden())
    return n as i32 + compared as i32 * 1000
";
        let mut started = Started::of(src);
        assert_eq!(started.call("picks", &[0]), -300 + 3);
        assert_eq!(started.call("picks", &[1]), 700 + 53);
        assert_eq!(started.call("picks", &[2]), -300 + 63);
        assert_eq!(started.call("places", &[]), 32112);
        assert_eq!(started.call("lists", &[]), 1532);
    }
}

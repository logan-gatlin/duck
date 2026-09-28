//! Encoding of [`crate::ir`] as a WebAssembly binary module.
//!
//! The IR is already shaped after wasm, so this is one direct walk: every
//! statement and expression maps to a fixed instruction sequence. The module
//! imports its `extern` functions and exports its memory, `pub fn`s, and `pub`
//! globals. Source names go in a `name` custom section so tools can show them.

use std::collections::HashMap;

use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, EntityType, ExportKind, ExportSection, Function,
    FunctionSection, GlobalSection, GlobalType, ImportSection, IndirectNameMap, Instruction,
    MemArg, MemorySection, MemoryType, NameMap, NameSection, TypeSection,
};

use crate::ir::{BinOp, Const, Expr, Func, LoadOp, Module, Stmt, StoreOp, UnOp, ValType};

/// Encodes a lowered module as the contents of a `.wasm` file.
pub fn emit(module: &Module) -> Vec<u8> {
    let mut types = TypeSection::new();
    let mut type_ids = HashMap::new();
    let mut type_id = |params: &[ValType], results: &[ValType]| {
        *type_ids
            .entry((params.to_vec(), results.to_vec()))
            .or_insert_with(|| {
                let params = params.iter().map(|ty| val_type(*ty));
                let results = results.iter().map(|ty| val_type(*ty));
                types.ty().function(params, results);
                types.len() - 1
            })
    };

    let mut imports = ImportSection::new();
    for import in &module.imports {
        let id = type_id(&import.params, &import.results);
        imports.import(&import.module, &import.field, EntityType::Function(id));
    }

    let mut functions = FunctionSection::new();
    for func in &module.funcs {
        functions.function(type_id(&func.params, &func.results));
    }

    let mut memories = MemorySection::new();
    memories.memory(MemoryType {
        minimum: module.memory.min_pages.into(),
        maximum: module.memory.max_pages.map(Into::into),
        memory64: false,
        shared: false,
        page_size_log2: None,
    });

    let mut globals = GlobalSection::new();
    for global in &module.globals {
        let ty = GlobalType {
            val_type: val_type(global.ty),
            mutable: global.mutable,
            shared: false,
        };
        globals.global(ty, &const_expr(global.init));
    }

    // Defined functions are indexed after the imported ones.
    let func_index = |i: usize| (module.imports.len() + i) as u32;

    let mut exports = ExportSection::new();
    exports.export(&module.memory.export, ExportKind::Memory, 0);
    for (i, func) in module.funcs.iter().enumerate() {
        if let Some(name) = &func.export {
            exports.export(name, ExportKind::Func, func_index(i));
        }
    }
    for (i, global) in module.globals.iter().enumerate() {
        if let Some(name) = &global.export {
            exports.export(name, ExportKind::Global, i as u32);
        }
    }

    let mut code = CodeSection::new();
    for func in &module.funcs {
        code.function(&function(func));
    }

    let mut func_names = NameMap::new();
    for (i, import) in module.imports.iter().enumerate() {
        func_names.append(i as u32, &import.name);
    }
    let mut local_names = IndirectNameMap::new();
    for (i, func) in module.funcs.iter().enumerate() {
        func_names.append(func_index(i), &func.name);
        let mut locals = NameMap::new();
        for (j, local) in func.locals.iter().enumerate() {
            locals.append(j as u32, &local.name);
        }
        local_names.append(func_index(i), &locals);
    }
    let mut global_names = NameMap::new();
    for (i, global) in module.globals.iter().enumerate() {
        global_names.append(i as u32, &global.name);
    }
    let mut names = NameSection::new();
    names.functions(&func_names);
    names.locals(&local_names);
    names.globals(&global_names);

    let mut out = wasm_encoder::Module::new();
    out.section(&types)
        .section(&imports)
        .section(&functions)
        .section(&memories)
        .section(&globals)
        .section(&exports)
        .section(&code)
        .section(&names);
    out.finish()
}

fn function(func: &Func) -> Function {
    let locals = func.locals[func.params.len()..].iter();
    let mut f = Function::new_with_locals_types(locals.map(|local| val_type(local.ty)));
    stmts(&mut f, &func.body);
    f.instruction(&Instruction::End);
    f
}

fn stmt(f: &mut Function, stmt: &Stmt) {
    match stmt {
        Stmt::SetLocal(local, value) => {
            expr(f, value);
            f.instruction(&Instruction::LocalSet(local.0));
        }
        Stmt::SetGlobal(global, value) => {
            expr(f, value);
            f.instruction(&Instruction::GlobalSet(global.0));
        }
        Stmt::Store {
            ty,
            op,
            offset,
            addr,
            value,
        } => {
            expr(f, addr);
            expr(f, value);
            f.instruction(&store(*ty, *op, *offset));
        }
        Stmt::Drop(value) => {
            expr(f, value);
            f.instruction(&Instruction::Drop);
        }
        Stmt::Call { func, args, dests } => {
            exprs(f, args);
            f.instruction(&Instruction::Call(func.0));
            // The last result is on top of the stack.
            for dest in dests.iter().rev() {
                f.instruction(&Instruction::LocalSet(dest.0));
            }
        }
        Stmt::Block(body) => {
            f.instruction(&Instruction::Block(BlockType::Empty));
            stmts(f, body);
            f.instruction(&Instruction::End);
        }
        Stmt::Loop(body) => {
            f.instruction(&Instruction::Loop(BlockType::Empty));
            stmts(f, body);
            f.instruction(&Instruction::End);
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            expr(f, cond);
            f.instruction(&Instruction::If(BlockType::Empty));
            stmts(f, then_body);
            if !else_body.is_empty() {
                f.instruction(&Instruction::Else);
                stmts(f, else_body);
            }
            f.instruction(&Instruction::End);
        }
        Stmt::Br(depth) => {
            f.instruction(&Instruction::Br(*depth));
        }
        Stmt::BrIf(depth, cond) => {
            expr(f, cond);
            f.instruction(&Instruction::BrIf(*depth));
        }
        Stmt::Return(values) => {
            exprs(f, values);
            f.instruction(&Instruction::Return);
        }
        Stmt::Unreachable => {
            f.instruction(&Instruction::Unreachable);
        }
    }
}

fn stmts(f: &mut Function, body: &[Stmt]) {
    for s in body {
        stmt(f, s);
    }
}

fn expr(f: &mut Function, expr: &Expr) {
    match expr {
        Expr::Const(c) => {
            f.instruction(&konst(*c));
        }
        Expr::Local(local) => {
            f.instruction(&Instruction::LocalGet(local.0));
        }
        Expr::Global(global) => {
            f.instruction(&Instruction::GlobalGet(global.0));
        }
        Expr::Unary(ty, op, x) => {
            self::expr(f, x);
            f.instruction(&unary(*ty, *op));
        }
        Expr::Binary(ty, op, a, b) => {
            self::expr(f, a);
            self::expr(f, b);
            f.instruction(&binary(*ty, *op));
        }
        Expr::Call(func, args) => {
            exprs(f, args);
            f.instruction(&Instruction::Call(func.0));
        }
        Expr::Load {
            ty,
            op,
            offset,
            addr,
        } => {
            self::expr(f, addr);
            f.instruction(&load(*ty, *op, *offset));
        }
        Expr::If {
            ty,
            cond,
            then_expr,
            else_expr,
        } => {
            self::expr(f, cond);
            f.instruction(&Instruction::If(BlockType::Result(val_type(*ty))));
            self::expr(f, then_expr);
            f.instruction(&Instruction::Else);
            self::expr(f, else_expr);
            f.instruction(&Instruction::End);
        }
        Expr::Seq(body, value) => {
            stmts(f, body);
            self::expr(f, value);
        }
    }
}

fn exprs(f: &mut Function, values: &[Expr]) {
    for value in values {
        expr(f, value);
    }
}

fn konst(c: Const) -> Instruction<'static> {
    match c {
        Const::I32(x) => Instruction::I32Const(x),
        Const::I64(x) => Instruction::I64Const(x),
        Const::F32(x) => Instruction::F32Const(x.into()),
        Const::F64(x) => Instruction::F64Const(x.into()),
    }
}

fn const_expr(c: Const) -> ConstExpr {
    match c {
        Const::I32(x) => ConstExpr::i32_const(x),
        Const::I64(x) => ConstExpr::i64_const(x),
        Const::F32(x) => ConstExpr::f32_const(x.into()),
        Const::F64(x) => ConstExpr::f64_const(x.into()),
    }
}

/// `<ty>.<op> offset=<offset>` with its natural alignment.
fn load(ty: ValType, op: LoadOp, offset: u32) -> Instruction<'static> {
    use LoadOp::*;
    use ValType::*;
    let arg = |align| memarg(align, offset);
    match (ty, op) {
        (I32, Load) => Instruction::I32Load(arg(2)),
        (I64, Load) => Instruction::I64Load(arg(3)),
        (F32, Load) => Instruction::F32Load(arg(2)),
        (F64, Load) => Instruction::F64Load(arg(3)),
        (I32, Load8S) => Instruction::I32Load8S(arg(0)),
        (I32, Load8U) => Instruction::I32Load8U(arg(0)),
        (I32, Load16S) => Instruction::I32Load16S(arg(1)),
        (I32, Load16U) => Instruction::I32Load16U(arg(1)),
        (I64, Load8S) => Instruction::I64Load8S(arg(0)),
        (I64, Load8U) => Instruction::I64Load8U(arg(0)),
        (I64, Load16S) => Instruction::I64Load16S(arg(1)),
        (I64, Load16U) => Instruction::I64Load16U(arg(1)),
        _ => panic!("no wasm instruction {ty:?}.{op:?}"),
    }
}

/// `<ty>.<op> offset=<offset>` with its natural alignment.
fn store(ty: ValType, op: StoreOp, offset: u32) -> Instruction<'static> {
    use StoreOp::*;
    use ValType::*;
    let arg = |align| memarg(align, offset);
    match (ty, op) {
        (I32, Store) => Instruction::I32Store(arg(2)),
        (I64, Store) => Instruction::I64Store(arg(3)),
        (F32, Store) => Instruction::F32Store(arg(2)),
        (F64, Store) => Instruction::F64Store(arg(3)),
        (I32, Store8) => Instruction::I32Store8(arg(0)),
        (I32, Store16) => Instruction::I32Store16(arg(1)),
        (I64, Store8) => Instruction::I64Store8(arg(0)),
        (I64, Store16) => Instruction::I64Store16(arg(1)),
        _ => panic!("no wasm instruction {ty:?}.{op:?}"),
    }
}

/// An access to the one memory, `align` given as a power of two.
fn memarg(align: u32, offset: u32) -> MemArg {
    MemArg {
        offset: offset.into(),
        align,
        memory_index: 0,
    }
}

/// `<ty>.<op>`, where `ty` is the operand type.
fn unary(ty: ValType, op: UnOp) -> Instruction<'static> {
    use UnOp::*;
    use ValType::*;
    match (ty, op) {
        (I32, Eqz) => Instruction::I32Eqz,
        (I64, Eqz) => Instruction::I64Eqz,
        (F32, Neg) => Instruction::F32Neg,
        (F64, Neg) => Instruction::F64Neg,
        (I32, Extend8S) => Instruction::I32Extend8S,
        (I32, Extend16S) => Instruction::I32Extend16S,
        (I64, Extend8S) => Instruction::I64Extend8S,
        (I64, Extend16S) => Instruction::I64Extend16S,
        (I64, Wrap) => Instruction::I32WrapI64,
        (I32, ExtendS) => Instruction::I64ExtendI32S,
        (I32, ExtendU) => Instruction::I64ExtendI32U,
        (F32, TruncSatS(I32)) => Instruction::I32TruncSatF32S,
        (F32, TruncSatU(I32)) => Instruction::I32TruncSatF32U,
        (F64, TruncSatS(I32)) => Instruction::I32TruncSatF64S,
        (F64, TruncSatU(I32)) => Instruction::I32TruncSatF64U,
        (F32, TruncSatS(I64)) => Instruction::I64TruncSatF32S,
        (F32, TruncSatU(I64)) => Instruction::I64TruncSatF32U,
        (F64, TruncSatS(I64)) => Instruction::I64TruncSatF64S,
        (F64, TruncSatU(I64)) => Instruction::I64TruncSatF64U,
        (I32, ConvertS(F32)) => Instruction::F32ConvertI32S,
        (I32, ConvertU(F32)) => Instruction::F32ConvertI32U,
        (I64, ConvertS(F32)) => Instruction::F32ConvertI64S,
        (I64, ConvertU(F32)) => Instruction::F32ConvertI64U,
        (I32, ConvertS(F64)) => Instruction::F64ConvertI32S,
        (I32, ConvertU(F64)) => Instruction::F64ConvertI32U,
        (I64, ConvertS(F64)) => Instruction::F64ConvertI64S,
        (I64, ConvertU(F64)) => Instruction::F64ConvertI64U,
        (F64, Demote) => Instruction::F32DemoteF64,
        (F32, Promote) => Instruction::F64PromoteF32,
        _ => panic!("no wasm instruction {ty:?}.{op:?}"),
    }
}

/// `<ty>.<op>`, where `ty` is the operand type.
fn binary(ty: ValType, op: BinOp) -> Instruction<'static> {
    use BinOp::*;
    use ValType::*;
    match (ty, op) {
        (I32, Add) => Instruction::I32Add,
        (I32, Sub) => Instruction::I32Sub,
        (I32, Mul) => Instruction::I32Mul,
        (I32, DivS) => Instruction::I32DivS,
        (I32, DivU) => Instruction::I32DivU,
        (I32, RemS) => Instruction::I32RemS,
        (I32, RemU) => Instruction::I32RemU,
        (I32, And) => Instruction::I32And,
        (I32, Or) => Instruction::I32Or,
        (I32, Xor) => Instruction::I32Xor,
        (I32, Shl) => Instruction::I32Shl,
        (I32, ShrS) => Instruction::I32ShrS,
        (I32, ShrU) => Instruction::I32ShrU,
        (I32, Eq) => Instruction::I32Eq,
        (I32, Ne) => Instruction::I32Ne,
        (I32, LtS) => Instruction::I32LtS,
        (I32, LtU) => Instruction::I32LtU,
        (I32, LeS) => Instruction::I32LeS,
        (I32, LeU) => Instruction::I32LeU,
        (I32, GtS) => Instruction::I32GtS,
        (I32, GtU) => Instruction::I32GtU,
        (I32, GeS) => Instruction::I32GeS,
        (I32, GeU) => Instruction::I32GeU,

        (I64, Add) => Instruction::I64Add,
        (I64, Sub) => Instruction::I64Sub,
        (I64, Mul) => Instruction::I64Mul,
        (I64, DivS) => Instruction::I64DivS,
        (I64, DivU) => Instruction::I64DivU,
        (I64, RemS) => Instruction::I64RemS,
        (I64, RemU) => Instruction::I64RemU,
        (I64, And) => Instruction::I64And,
        (I64, Or) => Instruction::I64Or,
        (I64, Xor) => Instruction::I64Xor,
        (I64, Shl) => Instruction::I64Shl,
        (I64, ShrS) => Instruction::I64ShrS,
        (I64, ShrU) => Instruction::I64ShrU,
        (I64, Eq) => Instruction::I64Eq,
        (I64, Ne) => Instruction::I64Ne,
        (I64, LtS) => Instruction::I64LtS,
        (I64, LtU) => Instruction::I64LtU,
        (I64, LeS) => Instruction::I64LeS,
        (I64, LeU) => Instruction::I64LeU,
        (I64, GtS) => Instruction::I64GtS,
        (I64, GtU) => Instruction::I64GtU,
        (I64, GeS) => Instruction::I64GeS,
        (I64, GeU) => Instruction::I64GeU,

        (F32, Add) => Instruction::F32Add,
        (F32, Sub) => Instruction::F32Sub,
        (F32, Mul) => Instruction::F32Mul,
        (F32, Div) => Instruction::F32Div,
        (F32, Min) => Instruction::F32Min,
        (F32, Max) => Instruction::F32Max,
        (F32, Eq) => Instruction::F32Eq,
        (F32, Ne) => Instruction::F32Ne,
        (F32, Lt) => Instruction::F32Lt,
        (F32, Le) => Instruction::F32Le,
        (F32, Gt) => Instruction::F32Gt,
        (F32, Ge) => Instruction::F32Ge,

        (F64, Add) => Instruction::F64Add,
        (F64, Sub) => Instruction::F64Sub,
        (F64, Mul) => Instruction::F64Mul,
        (F64, Div) => Instruction::F64Div,
        (F64, Min) => Instruction::F64Min,
        (F64, Max) => Instruction::F64Max,
        (F64, Eq) => Instruction::F64Eq,
        (F64, Ne) => Instruction::F64Ne,
        (F64, Lt) => Instruction::F64Lt,
        (F64, Le) => Instruction::F64Le,
        (F64, Gt) => Instruction::F64Gt,
        (F64, Ge) => Instruction::F64Ge,

        _ => panic!("no wasm instruction {ty:?}.{op:?}"),
    }
}

fn val_type(ty: ValType) -> wasm_encoder::ValType {
    match ty {
        ValType::I32 => wasm_encoder::ValType::I32,
        ValType::I64 => wasm_encoder::ValType::I64,
        ValType::F32 => wasm_encoder::ValType::F32,
        ValType::F64 => wasm_encoder::ValType::F64,
        ValType::ExternRef => wasm_encoder::ValType::EXTERNREF,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::{DummyManager, FileManager, MemoryLimits, Settings};
    use crate::lex::tokenize;
    use crate::{parse, ty};

    /// Compiles `src` and checks that the output is a valid module.
    fn emit_src(src: &str) -> Vec<u8> {
        emit_with(src, &Settings::default())
    }

    /// Compiles `src` under `settings` and checks that the output is a valid
    /// module.
    fn emit_with(src: &str, settings: &Settings) -> Vec<u8> {
        let tokens = tokenize(DummyManager::new().entry_point(), src).unwrap();
        let module = match ty::check(&parse::parse(&tokens).unwrap(), settings) {
            Ok(module) => module,
            Err(errors) => panic!("unexpected type errors: {errors:#?}"),
        };
        let bytes = emit(&module);
        if let Err(e) = wasmparser::validate(&bytes) {
            panic!("invalid module: {e}\n{}", wat(&bytes));
        }
        bytes
    }

    fn wat(bytes: &[u8]) -> String {
        wasmprinter::print_bytes(bytes).unwrap()
    }

    /// The text of the function `name`, from its `(func` to its last line.
    fn func_wat(bytes: &[u8], name: &str) -> String {
        let wat = wat(bytes);
        let start = wat.find(&format!("(func ${name} ")).unwrap();
        let end = wat[start..].find("\n  )").unwrap();
        wat[start..start + end].to_string()
    }

    #[test]
    fn example_program() {
        let wat = wat(&emit_src(include_str!("../example.duck")));
        assert!(
            wat.contains(r#"(import "env" "log_f32" (func $logf (;1;) (type 1)))"#),
            "{wat}"
        );
        assert!(wat.contains(r#"(export "add" (func $add))"#), "{wat}");
        assert!(wat.contains(r#"(export "main" (func $main))"#), "{wat}");
        assert!(wat.contains(r#"(global $counter (;1;) (mut i32) i32.const 0)"#));
    }

    #[test]
    fn imports_precede_defined_functions() {
        let src = "\
struct P:
    x: f32
    y: i64
pub fn f(a: i32) -> i32:
    return a
extern \"js\":
    fn now(scale: i32) -> i32 = \"Date.now\"
extern:
    fn put(p: *P, v: P) -> P
    fn flag() -> bool
pub fn g() -> i32:
    let p = put(0 as *P, P(x: 1.0, y: 2))
    if flag():
        return f(now(1))
    return 0
";
        let bytes = emit_src(src);
        let wat = wat(&bytes);
        let lines: Vec<_> = wat
            .lines()
            .filter(|l| l.contains("(import ") || l.contains("(export \"f"))
            .collect();
        assert_eq!(
            lines,
            [
                r#"  (import "js" "Date.now" (func $now (;0;) (type 0)))"#,
                r#"  (import "env" "put" (func $put (;1;) (type 1)))"#,
                r#"  (import "env" "flag" (func $flag (;2;) (type 2)))"#,
                r#"  (export "f" (func $f))"#,
            ]
        );
        assert!(wat.contains("(type (;1;) (func (param i32 f32 i64) (result f32 i64)))"));
        assert!(wat.contains("(func $f (;3;) (type 0)"), "{wat}");
        assert!(wat.contains("(func $g (;4;) (type 2)"), "{wat}");
        let g = func_wat(&bytes, "g");
        assert!(g.contains("call $put\n"), "{g}");
        assert!(
            g.contains("call $flag\n    i32.const 0\n    i32.ne\n"),
            "{g}"
        );
        assert!(g.contains("call $now\n      call $f\n"), "{g}");
    }

    #[test]
    fn one_host_function_can_back_several_imports() {
        let src = "\
extern:
    fn logi(n: i32) = \"log\"
    fn logf(n: f32) = \"log\"
fn f():
    logi(1)
    logf(2.0)
";
        let wat = wat(&emit_src(src));
        let imports: Vec<_> = wat.lines().filter(|l| l.contains("(import ")).collect();
        assert_eq!(
            imports,
            [
                r#"  (import "env" "log" (func $logi (;0;) (type 0)))"#,
                r#"  (import "env" "log" (func $logf (;1;) (type 1)))"#,
            ]
        );
    }

    #[test]
    fn exports() {
        let src = "\
pub let a = 1
let b = 2
fn hidden():
    return
pub fn shown():
    return
";
        let wat = wat(&emit_src(src));
        let exports: Vec<_> = wat.lines().filter(|l| l.contains("(export ")).collect();
        assert_eq!(
            exports,
            [
                r#"  (export "memory" (memory 0))"#,
                r#"  (export "shown" (func $shown))"#,
                r#"  (export "a" (global $a))"#,
            ]
        );
        assert!(wat.contains("(memory (;0;) 1)"), "{wat}");
    }

    #[test]
    fn memory_limits() {
        let settings = Settings {
            memory: MemoryLimits {
                min_pages: 2,
                max_pages: Some(16),
            },
        };
        let wat = wat(&emit_with("pub fn f():\n    pass\n", &settings));
        assert!(wat.contains("(memory (;0;) 2 16)"), "{wat}");
    }

    #[test]
    fn function_types_are_shared() {
        let src = "\
fn a(x: i32) -> i64:
    return 0
fn b():
    return
fn c(y: i32) -> i64:
    return 1
";
        let wat = wat(&emit_src(src));
        let types: Vec<_> = wat.lines().filter(|l| l.contains("(type (;")).collect();
        assert_eq!(
            types,
            [
                "  (type (;0;) (func (param i32) (result i64)))",
                "  (type (;1;) (func))",
            ]
        );
        assert!(wat.contains("(func $c (;2;) (type 0)"), "{wat}");
    }

    #[test]
    fn externrefs_are_reference_values() {
        let src = "\
struct Handle:
    el: externref
    id: i32
extern:
    fn get(id: i32) -> externref
    fn put(el: externref)
pub fn f(a: externref) -> Handle:
    var b = get(1)
    put(b)
    b = a
    return Handle(el: b, id: 2)
";
        let wat = wat(&emit_src(src));
        assert!(
            wat.contains("(type (;0;) (func (param i32) (result externref)))"),
            "{wat}"
        );
        assert!(
            wat.contains("(func $f (;2;) (type 2) (param $a externref) (result externref i32)"),
            "{wat}"
        );
        assert!(wat.contains("(local $b externref)"), "{wat}");
    }

    #[test]
    fn globals_have_constant_initializers() {
        let wat = wat(&emit_src("let a = 1\nvar b: i64 = -2\nvar c: f32 = 1.5\n"));
        assert!(wat.contains("(global $a (;0;) i32 i32.const 1)"), "{wat}");
        assert!(wat.contains("(global $b (;1;) (mut i64) i64.const -2)"));
        assert!(wat.contains("(global $c (;2;) (mut f32) f32.const 0x1.8p+0 (;=1.5;))"));
    }

    #[test]
    fn statements() {
        let src = "\
fn f(a: bool) -> i32:
    var i = 0
    while a:
        if i > 2:
            break
        i += 1
    return i
";
        assert_eq!(
            func_wat(&emit_src(src), "f"),
            "\
(func $f (;0;) (type 0) (param $a i32) (result i32)
    (local $i i32)
    i32.const 0
    local.set $i
    block ;; label = @1
      loop ;; label = @2
        local.get $a
        i32.eqz
        br_if 1 (;@1;)
        local.get $i
        i32.const 2
        i32.gt_s
        if ;; label = @3
          br 2 (;@1;)
        end
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br 0 (;@2;)
      end
    end
    local.get $i
    return"
        );
    }

    #[test]
    fn memory_accesses_are_naturally_aligned() {
        let src = "\
struct P:
    a: u8
    b: i16
    c: f64
fn f(p: *P) -> f64:
    p.b = p.a as i16
    return p.c
";
        let func = func_wat(&emit_src(src), "f");
        assert!(func.contains("i32.load8_u"), "{func}");
        assert!(func.contains("i32.store16 offset=2"), "{func}");
        assert!(func.contains("f64.load offset=8"), "{func}");
    }

    #[test]
    fn multi_value_calls_set_their_destinations_last_first() {
        let src = "\
struct P:
    x: i32
    y: f32
fn make() -> P:
    return P(x: 1, y: 2.0)
fn f() -> f32:
    let p = make()
    return p.y
";
        let func = func_wat(&emit_src(src), "f");
        // Both temporaries are named `tmp`, so the second is printed by index.
        assert!(
            func.contains("call $make\n    local.set $\"#local1 tmp\"\n    local.set $tmp\n"),
            "{func}"
        );
    }

    #[test]
    fn conversions() {
        let src = "\
fn f(a: i8, b: u32, c: i64, x: f32, y: f64) -> f64:
    let d = a as i64
    let e = b as i64
    let g = c as i32
    let h = x as u8
    let i = y as i64
    let j = b as f32
    let k = x as f64
    return y as f32 as f64
";
        let func = func_wat(&emit_src(src), "f");
        for op in [
            "i64.extend_i32_s",
            "i64.extend_i32_u",
            "i32.wrap_i64",
            "i32.trunc_sat_f32_u",
            "i64.trunc_sat_f64_s",
            "f32.convert_i32_u",
            "f64.promote_f32",
            "f32.demote_f64",
        ] {
            assert!(func.contains(op), "missing {op} in {func}");
        }
    }
}

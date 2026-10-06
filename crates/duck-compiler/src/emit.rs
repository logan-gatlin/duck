//! Encoding of [`crate::ir`] as a WebAssembly binary module.
//!
//! The IR is already shaped after wasm, so this is one direct walk: every
//! statement and expression maps to a fixed instruction sequence. The module
//! imports its `extern` functions and exports its memory and the `pub fn`s
//! and `pub` globals of the entry module, names its start function if it has
//! one, and fills memory with its literals. A module that takes pointers to
//! functions also exports the table that holds them. Source names go in a `name` custom section so tools can show them.

use std::collections::HashMap;

use wasm_encoder::{
    BlockType, CodeSection, ConstExpr, DataSection, ElementSection, Elements, EntityType,
    ExportKind, ExportSection, Function, FunctionSection, GlobalSection, GlobalType, HeapType,
    ImportSection, IndirectNameMap, Instruction, MemArg, MemorySection, MemoryType, NameMap,
    NameSection, RefType, StartSection, TableSection, TableType, TypeSection,
};

use crate::ir::{BinOp, Const, Expr, Func, FuncType, LoadOp, Module, Stmt, StoreOp, UnOp, ValType};

/// The module's function types, each encoded the first time it's asked for.
#[derive(Default)]
struct Types {
    section: TypeSection,
    ids: HashMap<FuncType, u32>,
}

impl Types {
    /// The index of the type of functions from `params` to `results`.
    fn id(&mut self, params: &[ValType], results: &[ValType]) -> u32 {
        let ty = FuncType {
            params: params.to_vec(),
            results: results.to_vec(),
        };
        *self.ids.entry(ty).or_insert_with(|| {
            let params = params.iter().map(|ty| val_type(*ty));
            let results = results.iter().map(|ty| val_type(*ty));
            self.section.ty().function(params, results);
            self.section.len() - 1
        })
    }
}

/// Encodes a lowered module as the contents of a `.wasm` file.
pub fn emit(module: &Module) -> Vec<u8> {
    let mut types = Types::default();

    let mut imports = ImportSection::new();
    for import in &module.imports {
        let id = types.id(&import.params, &import.results);
        imports.import(&import.module, &import.field, EntityType::Function(id));
    }

    let mut functions = FunctionSection::new();
    for func in &module.funcs {
        functions.function(types.id(&func.params, &func.results));
    }

    // Index 0 is left empty, so the functions start at 1.
    let mut tables = TableSection::new();
    let mut elements = ElementSection::new();
    if let Some(table) = &module.table {
        let size = table.funcs.len() as u64 + 1;
        tables.table(TableType {
            element_type: RefType::FUNCREF,
            table64: false,
            minimum: size,
            maximum: Some(size),
            shared: false,
        });
        let funcs: Vec<_> = table.funcs.iter().map(|func| func.0).collect();
        elements.active(
            None,
            &ConstExpr::i32_const(1),
            Elements::Functions(funcs.into()),
        );
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
    if let Some(table) = &module.table {
        exports.export(&table.export, ExportKind::Table, 0);
    }
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

    let start = module.start.map(|func| StartSection {
        function_index: func.0,
    });

    let mut code = CodeSection::new();
    for func in &module.funcs {
        code.function(&function(func, &mut types));
    }

    let mut data = DataSection::new();
    for segment in &module.data {
        let offset = ConstExpr::i32_const(segment.offset as i32);
        data.active(0, &offset, segment.bytes.iter().copied());
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
    out.section(&types.section)
        .section(&imports)
        .section(&functions);
    if module.table.is_some() {
        out.section(&tables);
    }
    out.section(&memories).section(&globals).section(&exports);
    if let Some(start) = &start {
        out.section(start);
    }
    if module.table.is_some() {
        out.section(&elements);
    }
    out.section(&code).section(&data).section(&names);
    out.finish()
}

fn function(func: &Func, types: &mut Types) -> Function {
    let locals = func.locals[func.params.len()..].iter();
    let mut f = Function::new_with_locals_types(locals.map(|local| val_type(local.ty)));
    stmts(&mut f, types, &func.body);
    f.instruction(&Instruction::End);
    f
}

fn stmt(f: &mut Function, types: &mut Types, stmt: &Stmt) {
    match stmt {
        Stmt::SetLocal(local, value) => {
            expr(f, types, value);
            f.instruction(&Instruction::LocalSet(local.0));
        }
        Stmt::SetGlobal(global, value) => {
            expr(f, types, value);
            f.instruction(&Instruction::GlobalSet(global.0));
        }
        Stmt::Store {
            ty,
            op,
            offset,
            addr,
            value,
        } => {
            expr(f, types, addr);
            expr(f, types, value);
            f.instruction(&store(*ty, *op, *offset));
        }
        Stmt::Drop(value) => {
            expr(f, types, value);
            f.instruction(&Instruction::Drop);
        }
        Stmt::MemoryFill { dst, value, len } => {
            exprs(f, types, [dst, value, len]);
            f.instruction(&Instruction::MemoryFill(0));
        }
        Stmt::MemoryCopy { dst, src, len } => {
            exprs(f, types, [dst, src, len]);
            f.instruction(&Instruction::MemoryCopy {
                src_mem: 0,
                dst_mem: 0,
            });
        }
        Stmt::Call { func, args, dests } => {
            exprs(f, types, args);
            f.instruction(&Instruction::Call(func.0));
            // The last result is on top of the stack.
            for dest in dests.iter().rev() {
                f.instruction(&Instruction::LocalSet(dest.0));
            }
        }
        Stmt::CallIndirect {
            ty,
            args,
            index,
            dests,
        } => {
            exprs(f, types, args);
            expr(f, types, index);
            f.instruction(&call_indirect(types, ty));
            for dest in dests.iter().rev() {
                f.instruction(&Instruction::LocalSet(dest.0));
            }
        }
        Stmt::Block(body) => {
            f.instruction(&Instruction::Block(BlockType::Empty));
            stmts(f, types, body);
            f.instruction(&Instruction::End);
        }
        Stmt::Loop(body) => {
            f.instruction(&Instruction::Loop(BlockType::Empty));
            stmts(f, types, body);
            f.instruction(&Instruction::End);
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            expr(f, types, cond);
            f.instruction(&Instruction::If(BlockType::Empty));
            stmts(f, types, then_body);
            if !else_body.is_empty() {
                f.instruction(&Instruction::Else);
                stmts(f, types, else_body);
            }
            f.instruction(&Instruction::End);
        }
        Stmt::Br(depth) => {
            f.instruction(&Instruction::Br(*depth));
        }
        Stmt::BrIf(depth, cond) => {
            expr(f, types, cond);
            f.instruction(&Instruction::BrIf(*depth));
        }
        Stmt::Return(values) => {
            exprs(f, types, values);
            f.instruction(&Instruction::Return);
        }
        Stmt::Unreachable => {
            f.instruction(&Instruction::Unreachable);
        }
    }
}

fn stmts(f: &mut Function, types: &mut Types, body: &[Stmt]) {
    for s in body {
        stmt(f, types, s);
    }
}

fn expr(f: &mut Function, types: &mut Types, expr: &Expr) {
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
            self::expr(f, types, x);
            f.instruction(&unary(*ty, *op));
        }
        Expr::Binary(ty, op, a, b) => {
            self::expr(f, types, a);
            self::expr(f, types, b);
            f.instruction(&binary(*ty, *op));
        }
        Expr::Call(func, args) => {
            exprs(f, types, args);
            f.instruction(&Instruction::Call(func.0));
        }
        Expr::CallIndirect { ty, args, index } => {
            exprs(f, types, args);
            self::expr(f, types, index);
            f.instruction(&call_indirect(types, ty));
        }
        Expr::Load {
            ty,
            op,
            offset,
            addr,
        } => {
            self::expr(f, types, addr);
            f.instruction(&load(*ty, *op, *offset));
        }
        Expr::MemorySize => {
            f.instruction(&Instruction::MemorySize(0));
        }
        Expr::MemoryGrow(pages) => {
            self::expr(f, types, pages);
            f.instruction(&Instruction::MemoryGrow(0));
        }
        Expr::If {
            ty,
            cond,
            then_expr,
            else_expr,
        } => {
            self::expr(f, types, cond);
            f.instruction(&Instruction::If(BlockType::Result(val_type(*ty))));
            self::expr(f, types, then_expr);
            f.instruction(&Instruction::Else);
            self::expr(f, types, else_expr);
            f.instruction(&Instruction::End);
        }
        Expr::Seq(body, value) => {
            stmts(f, types, body);
            self::expr(f, types, value);
        }
    }
}

fn exprs<'a>(f: &mut Function, types: &mut Types, values: impl IntoIterator<Item = &'a Expr>) {
    for value in values {
        expr(f, types, value);
    }
}

/// `call_indirect` of a function of type `ty` in the one table.
fn call_indirect(types: &mut Types, ty: &FuncType) -> Instruction<'static> {
    Instruction::CallIndirect {
        type_index: types.id(&ty.params, &ty.results),
        table_index: 0,
    }
}

fn konst(c: Const) -> Instruction<'static> {
    match c {
        Const::I32(x) => Instruction::I32Const(x),
        Const::I64(x) => Instruction::I64Const(x),
        Const::F32(x) => Instruction::F32Const(x.into()),
        Const::F64(x) => Instruction::F64Const(x.into()),
        Const::Null => Instruction::RefNull(HeapType::EXTERN),
    }
}

fn const_expr(c: Const) -> ConstExpr {
    match c {
        Const::I32(x) => ConstExpr::i32_const(x),
        Const::I64(x) => ConstExpr::i64_const(x),
        Const::F32(x) => ConstExpr::f32_const(x.into()),
        Const::F64(x) => ConstExpr::f64_const(x.into()),
        Const::Null => ConstExpr::ref_null(HeapType::EXTERN),
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
        (I32, Clz) => Instruction::I32Clz,
        (I64, Clz) => Instruction::I64Clz,
        (I32, Ctz) => Instruction::I32Ctz,
        (I64, Ctz) => Instruction::I64Ctz,
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
        (F32, Reinterpret) => Instruction::I32ReinterpretF32,
        (F64, Reinterpret) => Instruction::I64ReinterpretF64,
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
    use crate::load::Program;
    use crate::{parse, ty};

    /// Compiles `src` and checks that the output is a valid module.
    fn emit_src(src: &str) -> Vec<u8> {
        emit_with(src, &Settings::default())
    }

    /// Compiles `src` under `settings` and checks that the output is a valid
    /// module.
    fn emit_with(src: &str, settings: &Settings) -> Vec<u8> {
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let module = match ty::check(&program, settings) {
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
        assert!(
            wat.contains(r#"(data (;0;) (i32.const 0) "Hello, duck!")"#),
            "{wat}"
        );
        assert!(wat.contains(r#"(global $counter (;1;) (mut i32) i32.const 0)"#));
    }

    #[test]
    fn unions_hold_externrefs_and_null_in_place_of_them() {
        let src = "\
extern:
    fn get() -> externref
    fn put(r: Ref)
pub union Ref:
    some: externref
    none
pub var held: Ref = .none
pub fn f():
    held = .some(get())
    put(held)
    put(.none)
";
        let bytes = emit_src(src);
        let wat = wat(&bytes);
        assert!(
            wat.contains(r#"(global $held.some (;1;) (mut externref) ref.null extern)"#),
            "{wat}"
        );
        assert!(
            wat.contains("(type (;1;) (func (param i32 externref)))"),
            "{wat}"
        );
        let f = func_wat(&bytes, "f");
        assert!(
            f.contains("i32.const 1\n    ref.null extern\n    call $put"),
            "{f}"
        );
    }

    #[test]
    fn match_arms_leave_the_block_they_are_in() {
        let src = "\
enum(u8) Color:
    red
    green
union(T) Option:
    some: T
    none
fn code(o: Option(Color)) -> i32:
    var n = 0
    match o:
        .some(c):
            match c:
                .red:
                    n = 1
                .green:
                    return 2
        .none:
            n = 3
    return n
";
        let bytes = emit_src(src);
        let code = func_wat(&bytes, "code");
        let lines: Vec<_> = code.lines().map(str::trim).collect();
        let count = |line: &str| lines.iter().filter(|l| l.starts_with(line)).count();
        // A block for each `match`, an `if` for each arm, and a branch out
        // of the block from each arm that doesn't return.
        assert_eq!(count("block"), 2, "{code}");
        assert_eq!(count("if"), 4, "{code}");
        assert_eq!(count("br 1"), 3, "{code}");
        assert_eq!(count("unreachable"), 2, "{code}");
    }

    #[test]
    fn array_equality_functions_follow_defined_functions() {
        let src = "\
pub struct N:
    kids: array(N)
extern:
    fn log(x: i32)
pub fn f(a: N, b: N, s: array(u8)) -> bool:
    return a == b and s == s
";
        let bytes = emit_src(src);
        let wat = wat(&bytes);
        let funcs: Vec<_> = wat.lines().filter(|l| l.starts_with("  (func $")).collect();
        assert_eq!(funcs.len(), 3, "{wat}");
        assert!(funcs[0].contains("(func $f (;1;)"), "{wat}");
        assert!(funcs[1].contains(r#"(func $"==(array(N))" (;2;)"#), "{wat}");
        assert!(
            funcs[2].contains(r#"(func $"==(array(u8))" (;3;)"#),
            "{wat}"
        );
        let own = func_wat(&bytes, r#""==(array(N))""#);
        assert!(own.contains(r#"call $"==(array(N))""#), "{own}");
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
    fn put(p: &P, v: P) -> P
    fn flag() -> bool
pub fn g() -> i32:
    let p = put(0 as &P, P(x: 1.0, y: 2))
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
        // No literals, so nothing for memory to start with.
        assert!(wat.contains("(memory (;0;) 0)"), "{wat}");
    }

    #[test]
    fn memory_limits() {
        let settings = Settings {
            memory: MemoryLimits {
                min_pages: Some(2),
                max_pages: Some(16),
            },
            ..Settings::default()
        };
        let wat = wat(&emit_with("pub fn f():\n    pass\n", &settings));
        assert!(wat.contains("(memory (;0;) 2 16)"), "{wat}");
    }

    #[test]
    fn start_function() {
        let settings = Settings {
            start: Some("init".to_string()),
            ..Settings::default()
        };
        let src = "\
extern:
    fn log(n: i32)
fn init():
    log(1)
";
        let started = wat(&emit_with(src, &settings));
        assert!(started.contains("(start $init)"), "{started}");
        let unstarted = wat(&emit_src(src));
        assert!(!unstarted.contains("(start"), "{unstarted}");
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
pub struct Handle:
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
        let wat = wat(&emit_src(
            "pub let a = 1\nvar b: i64 = -2\nvar c: f32 = 1.5\n",
        ));
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
fn f(p: &var P) -> f64:
    p.b = p.a as i16
    return p.c
";
        let func = func_wat(&emit_src(src), "f");
        assert!(func.contains("i32.load8_u"), "{func}");
        assert!(func.contains("i32.store16 offset=2"), "{func}");
        assert!(func.contains("f64.load offset=8"), "{func}");
    }

    #[test]
    fn module_functions_are_memory_instructions() {
        let src = "\
pub fn f(p: &var u8, q: &u8, n: u32) -> i32:
    module.fill(p, 0, n)
    module.copy(p, q, n)
    let all = module.memory()
    return module.grow(all.len / module.page_size - module.size())
";
        let func = func_wat(&emit_src(src), "f");
        assert!(!func.contains("call"), "{func}");
        for instr in ["memory.fill", "memory.copy", "memory.size", "memory.grow"] {
            assert!(func.contains(instr), "{instr}\n{func}");
        }
    }

    #[test]
    fn module_zero_counts_are_instructions() {
        let src = "\
pub fn f(a: u32, b: i64, c: u8) -> u32:
    let wide = module.count_leading_zeros(b) + module.count_trailing_zeros(b)
    let narrow = module.count_leading_zeros(c) + module.count_trailing_zeros(c)
    return module.count_leading_zeros(a) + module.count_trailing_zeros(a)
";
        let func = func_wat(&emit_src(src), "f");
        assert!(!func.contains("call"), "{func}");
        for instr in ["i32.clz", "i32.ctz", "i64.clz", "i64.ctz"] {
            assert!(func.contains(instr), "{instr}\n{func}");
        }
    }

    #[test]
    fn module_unreachable_ends_a_function_with_results() {
        let src = "\
pub fn f(x: u32) -> u32:
    if x == 0:
        return 1
    module.unreachable()
";
        let func = func_wat(&emit_src(src), "f");
        assert!(func.contains("unreachable"), "{func}");
    }

    #[test]
    fn tuples_are_multiple_values() {
        let src = "\
extern:
    fn divmod(a: i32, b: i32) -> tuple(i32, u8)
pub let (w, h) = (640, 480)
pub var pos = (1, (2.5, 3))
pub fn f(p: &tuple(u8, f64)) -> tuple(f64, i32):
    let (q, r) = divmod(w, h)
    pos.1.0 = p.1
    return (pos.1.0, q + r as i32)
";
        let wat = wat(&emit_src(src));
        for line in [
            "(type (;0;) (func (param i32 i32) (result i32 i32)))",
            "(type (;1;) (func (param i32) (result f64 i32)))",
            r#"(export "w" (global $w))"#,
            r#"(export "h" (global $h))"#,
            r#"(export "pos.0" (global $pos.0))"#,
            r#"(export "pos.1.0" (global $pos.1.0))"#,
            r#"(export "pos.1.1" (global $pos.1.1))"#,
            "(global $pos.1.0 (;3;) (mut f64) f64.const 0x1.4p+1 (;=2.5;))",
        ] {
            assert!(wat.contains(line), "{line}\n{wat}");
        }
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

    #[test]
    fn literals_are_active_data_segments() {
        let src = "\
pub let greeting = \"hey\"
let table: array(u16) = [1, 2]
";
        let wat = wat(&emit_src(src));
        for line in [
            r#"(data (;0;) (i32.const 0) "hey")"#,
            r#"(data (;1;) (i32.const 4) "\01\00\02\00")"#,
            r#"(export "greeting.len" (global $greeting.len))"#,
            r#"(export "greeting.ptr" (global $greeting.ptr))"#,
        ] {
            assert!(wat.contains(line), "{line}\n{wat}");
        }
    }

    #[test]
    fn indexing_traps_out_of_bounds() {
        let src = "\
fn f(a: array(u8), i: u32) -> u8:
    return a[i]
";
        let func = func_wat(&emit_src(src), "f");
        assert!(
            func.contains("i32.ge_u\n    if ;; label = @1\n      unreachable\n    end\n"),
            "{func}"
        );
    }

    #[test]
    fn for_loops_index_from_zero_to_len() {
        let src = "\
extern:
    fn log(n: i32)
fn f(a: array(i32)):
    for x in a:
        log(x)
";
        let func = func_wat(&emit_src(src), "f");
        let loop_start = func.find("block").unwrap();
        assert_eq!(
            &func[loop_start..],
            "\
    block ;; label = @1
      loop ;; label = @2
        local.get $\"#local4 tmp\"
        local.get $\"#local3 tmp\"
        i32.ge_u
        br_if 1 (;@1;)
        local.get $tmp
        local.get $\"#local4 tmp\"
        i32.const 4
        i32.mul
        i32.add
        i32.load
        local.set $x
        local.get $\"#local4 tmp\"
        i32.const 1
        i32.add
        local.set $\"#local4 tmp\"
        local.get $x
        call $log
        br 0 (;@2;)
      end
    end"
        );
    }

    #[test]
    fn enums_compare_bits_and_loop_over_members() {
        let src = "\
extern:
    fn log(text: array(u8))
enum(array(u8)) Greeting:
    hi = \"hello\"
    bye = \"goodbye\"
pub enum(tuple(f64, f32)) Point:
    origin = (0.0, 0.0)
    unit = (1.0, 1.0)
pub fn f(p: Point) -> bool:
    for g in Greeting:
        log(g as array(u8))
    return p == Point.origin
";
        let func = func_wat(&emit_src(src), "f");
        for op in ["i64.reinterpret_f64", "i32.reinterpret_f32"] {
            assert!(func.contains(op), "missing {op} in {func}");
        }
        // Unrolled, with a call per member.
        assert!(!func.contains("loop"), "{func}");
        assert_eq!(func.matches("call $log").count(), 2, "{func}");
    }

    #[test]
    fn function_pointers_index_an_exported_table() {
        let src = "\
fn inc(x: i32) -> i32:
    return x + 1
fn pair(x: i32) -> tuple(i32, f32):
    return (x, 1.0)
pub fn apply(f: fn(i32) -> i32, g: fn(i32) -> tuple(i32, f32)) -> i32:
    let (a, b) = g(1)
    return f(a)
pub fn main() -> i32:
    return apply(inc, pair)
";
        let bytes = emit_src(src);
        let wat = wat(&bytes);
        for line in [
            "(table (;0;) 3 3 funcref)",
            r#"(export "table" (table 0))"#,
            "(elem (;0;) (i32.const 1) func $inc $pair)",
        ] {
            assert!(wat.contains(line), "{line}\n{wat}");
        }
        let apply = func_wat(&bytes, "apply");
        // The type of `pair`, then of `inc`.
        assert!(apply.contains("call_indirect (type 1)"), "{apply}");
        assert!(
            apply.contains("local.get $f\n    call_indirect (type 0)"),
            "{apply}"
        );
        let main = func_wat(&bytes, "main");
        assert!(
            main.contains("i32.const 1\n    i32.const 2\n    call $apply"),
            "{main}"
        );

        let wat = self::wat(&emit_src("pub fn f():\n    pass\n"));
        assert!(!wat.contains("table") && !wat.contains("elem"), "{wat}");
    }

    #[test]
    fn imports_are_table_elements_unless_their_results_need_wrapping() {
        let src = "\
extern:
    fn log(n: i32)
    fn flag() -> bool
pub let handlers: array(fn(i32)) = [log, log]
pub fn pick(first: bool) -> fn() -> bool:
    let f = flag
    return f
pub fn run(f: fn() -> bool, g: fn(i32)) -> bool:
    g(1)
    return f()
";
        let bytes = emit_src(src);
        let wat = wat(&bytes);
        assert!(
            wat.contains(r#"(elem (;0;) (i32.const 1) func $log $"extern flag")"#),
            "{wat}"
        );
        let flag = func_wat(&bytes, r#""extern flag""#);
        assert!(
            flag.contains("call $flag\n    i32.const 0\n    i32.ne"),
            "{flag}"
        );
        assert!(wat.contains(r#"(data (;0;) (i32.const 0) "\01\00\00\00\01\00\00\00")"#));
    }
}

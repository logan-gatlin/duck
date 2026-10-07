//! The lowered program handed to codegen.
//!
//! Everything here is already resolved and type checked, and shaped after
//! wasm: values are the four numeric wasm value types and `externref`, structs
//! have been split into one local or global per scalar field, function
//! pointers are indices into the module's table, and control flow is wasm's
//! structured `block`/`loop`/`if` with branch targets given as label depths.
//! An address, a function pointer and a count of pages are each an `i32`, or
//! an `i64` where [`Memory::memory64`] is set.

/// A wasm function index: [`Module::imports`] come first, then
/// [`Module::funcs`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FuncId(pub u32);

/// Index into [`Module::globals`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GlobalId(pub u32);

/// Index into [`Func::locals`]. Parameters come first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LocalId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub memory: Memory,
    /// What memory holds when the module is instantiated, in address order.
    pub data: Vec<Data>,
    /// `None` if the module calls nothing through its table.
    pub table: Option<Table>,
    pub globals: Vec<Global>,
    pub imports: Vec<Import>,
    pub funcs: Vec<Func>,
    /// Called when the module is instantiated. Takes and returns nothing.
    pub start: Option<FuncId>,
}

/// The module's one linear memory, which pointers address.
#[derive(Debug, Clone, PartialEq)]
pub struct Memory {
    /// Initial size in 64 KiB pages.
    pub min_pages: u64,
    /// Size in 64 KiB pages it may grow to; `None` is unlimited.
    pub max_pages: Option<u64>,
    /// Whether it is addressed with an `i64` rather than an `i32`.
    pub memory64: bool,
    pub export: String,
}

/// The module's one table, which function pointers index.
#[derive(Debug, Clone, PartialEq)]
pub struct Table {
    /// Whether it is indexed with an `i64` rather than an `i32`, as it is
    /// where the memory is.
    pub table64: bool,
    pub export: String,
    /// The function at each index from 1 up. Nothing is at index 0, so
    /// calling it traps.
    pub funcs: Vec<FuncId>,
}

/// Bytes copied into memory at `offset` when the module is instantiated.
#[derive(Debug, Clone, PartialEq)]
pub struct Data {
    pub offset: u64,
    pub bytes: Vec<u8>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
    /// An opaque reference from the host. Only null is constant.
    ExternRef,
}

/// The wasm type of a function.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Const {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
    /// The null `externref`, which a union has for a variant it doesn't
    /// hold.
    Null,
}

/// A `var`, or an exported `let`. A `let` is a [`Expr::Const`] wherever it
/// is used, so only the host reads an exported one.
#[derive(Debug, Clone, PartialEq)]
pub struct Global {
    /// Source name, with a `.field` suffix per level for split structs.
    pub name: String,
    pub ty: ValType,
    pub mutable: bool,
    pub init: Const,
    /// Export name, set for `pub let` and `pub var`.
    pub export: Option<String>,
}

/// A function supplied by the host, imported as `module`.`field`.
#[derive(Debug, Clone, PartialEq)]
pub struct Import {
    /// Source name, for debugging.
    pub name: String,
    pub module: String,
    pub field: String,
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Func {
    pub name: String,
    /// Export name, set for `pub fn`.
    pub export: Option<String>,
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
    /// Every local, starting with one per parameter.
    pub locals: Vec<Local>,
    pub body: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Local {
    /// Source name for debugging, with a `.field` suffix per level for split
    /// structs. Compiler temporaries are named `tmp`, but for those that
    /// hold what a pattern names.
    pub name: String,
    pub ty: ValType,
}

/// An instruction sequence that leaves the operand stack as it found it.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    SetLocal(LocalId, Expr),
    SetGlobal(GlobalId, Expr),
    /// `<ty>.<op> offset=<offset>`, writing `value` to `addr + offset` with
    /// the natural alignment of the access. `addr` is evaluated first.
    Store {
        ty: ValType,
        op: StoreOp,
        offset: u32,
        addr: Expr,
        value: Expr,
    },
    /// Evaluates `expr` and discards its value.
    Drop(Expr),
    /// `memory.fill`, setting the `len` bytes from `dst` to the low byte of
    /// `value`. Operands are evaluated in order.
    MemoryFill {
        dst: Expr,
        value: Expr,
        len: Expr,
    },
    /// `memory.copy`, copying `len` bytes from `src` to `dst`, which may
    /// overlap. Operands are evaluated in order.
    MemoryCopy {
        dst: Expr,
        src: Expr,
        len: Expr,
    },
    /// A call whose results (zero, or more than one) are stored to `dests`
    /// in order. Single-result calls are [`Expr::Call`].
    Call {
        func: FuncId,
        args: Vec<Expr>,
        dests: Vec<LocalId>,
    },
    /// [`Expr::CallIndirect`] with zero results, or more than one, which are
    /// stored to `dests` in order.
    CallIndirect {
        ty: FuncType,
        args: Vec<Expr>,
        index: Expr,
        dests: Vec<LocalId>,
    },
    /// A label that `Br` jumps to the end of.
    Block(Vec<Stmt>),
    /// A label that `Br` jumps to the start of.
    Loop(Vec<Stmt>),
    /// Also a label, jumping to the end.
    If {
        cond: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    /// Branches to the label `depth` levels out; 0 is the innermost.
    Br(u32),
    BrIf(u32, Expr),
    Return(Vec<Expr>),
    Unreachable,
}

/// An expression producing exactly one value.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Const(Const),
    Local(LocalId),
    Global(GlobalId),
    /// The instruction `<ty>.<op>`, where `ty` is the operand type.
    Unary(ValType, UnOp, Box<Expr>),
    /// The instruction `<ty>.<op>`, where `ty` is the operand type.
    Binary(ValType, BinOp, Box<Expr>, Box<Expr>),
    Call(FuncId, Vec<Expr>),
    /// `call_indirect`, calling the function at `index` in the table, and
    /// trapping unless one of type `ty` is there. `args` are evaluated in
    /// order, then `index`.
    CallIndirect {
        ty: FuncType,
        args: Vec<Expr>,
        index: Box<Expr>,
    },
    /// `<ty>.<op> offset=<offset>`, reading from `addr + offset` with the
    /// natural alignment of the access.
    Load {
        ty: ValType,
        op: LoadOp,
        offset: u32,
        addr: Box<Expr>,
    },
    /// `memory.size`, the memory's current size in pages.
    MemorySize,
    /// `memory.grow`, adding the number of pages and producing the old size,
    /// or -1 if the memory can't grow that much.
    MemoryGrow(Box<Expr>),
    /// `if (result ty)`. A label, but nothing inside can branch.
    If {
        ty: ValType,
        cond: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
    },
    /// Runs the statements and then evaluates the expression. Not a label:
    /// codegen emits the statements inline.
    Seq(Vec<Stmt>, Box<Expr>),
}

/// Unary instructions, named as in wasm. Conversions name their result type;
/// the operand type is the `ValType` in [`Expr::Unary`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    /// Integer `== 0`.
    Eqz,
    /// The number of zero bits above the highest set bit of an integer: all
    /// of its bits for 0.
    Clz,
    /// The number of zero bits below the lowest set bit of an integer: all
    /// of its bits for 0.
    Ctz,
    /// Float negation.
    Neg,
    Extend8S,
    Extend16S,
    /// `i32.wrap_i64`
    Wrap,
    /// `i64.extend_i32_s`
    ExtendS,
    /// `i64.extend_i32_u`
    ExtendU,
    /// `<to>.trunc_sat_<from>_s`
    TruncSatS(ValType),
    /// `<to>.trunc_sat_<from>_u`
    TruncSatU(ValType),
    /// `<to>.convert_<from>_s`
    ConvertS(ValType),
    /// `<to>.convert_<from>_u`
    ConvertU(ValType),
    /// `f32.demote_f64`
    Demote,
    /// `f64.promote_f32`
    Promote,
    /// `i32.reinterpret_f32` or `i64.reinterpret_f64`, the bits of a float,
    /// or `f32.reinterpret_i32` or `f64.reinterpret_i64`, the float with the
    /// bits of an integer.
    Reinterpret,
}

/// Load instructions, named as in wasm. Narrow loads extend to their `ValType`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LoadOp {
    Load,
    Load8S,
    Load8U,
    Load16S,
    Load16U,
}

/// Store instructions, named as in wasm. Narrow stores keep the low bits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StoreOp {
    Store,
    Store8,
    Store16,
}

/// Binary instructions, named as in wasm. Unsuffixed comparisons and `Div`
/// are the float forms.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    DivS,
    DivU,
    RemS,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    ShrS,
    ShrU,
    Min,
    Max,
    Eq,
    Ne,
    Lt,
    LtS,
    LtU,
    Le,
    LeS,
    LeU,
    Gt,
    GtS,
    GtU,
    Ge,
    GeS,
    GeU,
}

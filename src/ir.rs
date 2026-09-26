//! The lowered program handed to codegen.
//!
//! Everything here is already resolved and type checked, and shaped after
//! wasm: values are the four wasm value types, structs have been split into
//! one local or global per scalar field, and control flow is wasm's structured
//! `block`/`loop`/`if` with branch targets given as label depths.

/// Index into [`Module::funcs`].
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
    pub globals: Vec<Global>,
    pub funcs: Vec<Func>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Const {
    I32(i32),
    I64(i64),
    F32(f32),
    F64(f64),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Global {
    /// Source name, with a `.field` suffix per level for split structs.
    pub name: String,
    pub ty: ValType,
    pub mutable: bool,
    pub init: Const,
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
    /// structs. Compiler temporaries are named `tmp`.
    pub name: String,
    pub ty: ValType,
}

/// An instruction sequence that leaves the operand stack as it found it.
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    SetLocal(LocalId, Expr),
    SetGlobal(GlobalId, Expr),
    /// Evaluates `expr` and discards its value.
    Drop(Expr),
    /// A call whose results (zero, or more than one) are stored to `dests`
    /// in order. Single-result calls are [`Expr::Call`].
    Call {
        func: FuncId,
        args: Vec<Expr>,
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

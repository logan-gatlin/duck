//! Name resolution, type checking, and lowering to [`crate::ir`].
//!
//! All three happen in one walk over each function body. Signatures are
//! collected first so items can be used before they are declared. Functions
//! imported from `extern` blocks come first in the function index space.

use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::ops::Range;

use crate::file::{FileId, Settings};
use crate::ir::{
    self, BinOp as IrBinOp, Const, Expr, FuncId, GlobalId, LoadOp, LocalId, Stmt, StoreOp,
    UnOp as IrUnOp, ValType,
};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{
    self, Arg, BinOp, ExprKind, ExternBlock, ExternFn, FnSig, Ident, ItemKind, Mutability, Pattern,
    PatternKind, StmtKind, TypeKind, UnaryOp,
};

use enums::EnumDef;
use generic::{Arity, Instance, ParamDef};
use generic_fn::{FnInstance, GenericFn};

mod enums;
mod equality;
mod generic;
mod generic_fn;

/// Folds the wasm integer instruction `$op` over `$a` and `$b`, which have
/// signed type `$s` and unsigned counterpart `$u`. Returns from the enclosing
/// function on a trap or a non-integer instruction.
macro_rules! fold_int_binary {
    ($op:expr, $a:expr, $b:expr, $s:ty, $u:ty, $variant:ident) => {{
        let (a, b): ($s, $s) = ($a, $b);
        let (ua, ub) = (a as $u, b as $u);
        let bool = |x: bool| Const::I32(x as i32);
        match $op {
            IrBinOp::Add => Const::$variant(a.wrapping_add(b)),
            IrBinOp::Sub => Const::$variant(a.wrapping_sub(b)),
            IrBinOp::Mul => Const::$variant(a.wrapping_mul(b)),
            IrBinOp::DivS => Const::$variant(a.checked_div(b).ok_or(Fold::Trap)?),
            IrBinOp::DivU => Const::$variant(ua.checked_div(ub).ok_or(Fold::Trap)? as $s),
            IrBinOp::RemS if b == 0 => return Err(Fold::Trap),
            IrBinOp::RemS => Const::$variant(a.wrapping_rem(b)),
            IrBinOp::RemU => Const::$variant(ua.checked_rem(ub).ok_or(Fold::Trap)? as $s),
            IrBinOp::And => Const::$variant(a & b),
            IrBinOp::Or => Const::$variant(a | b),
            IrBinOp::Xor => Const::$variant(a ^ b),
            IrBinOp::Shl => Const::$variant(a.wrapping_shl(b as u32)),
            IrBinOp::ShrS => Const::$variant(a.wrapping_shr(b as u32)),
            IrBinOp::ShrU => Const::$variant(ua.wrapping_shr(b as u32) as $s),
            IrBinOp::Eq => bool(a == b),
            IrBinOp::Ne => bool(a != b),
            IrBinOp::LtS => bool(a < b),
            IrBinOp::LtU => bool(ua < ub),
            IrBinOp::LeS => bool(a <= b),
            IrBinOp::LeU => bool(ua <= ub),
            IrBinOp::GtS => bool(a > b),
            IrBinOp::GtU => bool(ua > ub),
            IrBinOp::GeS => bool(a >= b),
            IrBinOp::GeU => bool(ua >= ub),
            _ => return Err(Fold::NotConstant),
        }
    }};
}

/// Folds the wasm float instruction `$op` over `$a` and `$b` of type `$f`.
macro_rules! fold_float_binary {
    ($op:expr, $a:expr, $b:expr, $f:ty, $variant:ident) => {{
        let (a, b): ($f, $f) = ($a, $b);
        let bool = |x: bool| Const::I32(x as i32);
        match $op {
            IrBinOp::Add => Const::$variant(a + b),
            IrBinOp::Sub => Const::$variant(a - b),
            IrBinOp::Mul => Const::$variant(a * b),
            IrBinOp::Div => Const::$variant(a / b),
            IrBinOp::Min => Const::$variant(wasm_min(a as f64, b as f64) as $f),
            IrBinOp::Max => Const::$variant(wasm_max(a as f64, b as f64) as $f),
            IrBinOp::Eq => bool(a == b),
            IrBinOp::Ne => bool(a != b),
            IrBinOp::Lt => bool(a < b),
            IrBinOp::Le => bool(a <= b),
            IrBinOp::Gt => bool(a > b),
            IrBinOp::Ge => bool(a >= b),
            _ => return Err(Fold::NotConstant),
        }
    }};
}

/// The export name of the module's memory, which no item may take.
const MEMORY_EXPORT: &str = "memory";

/// The name of the global holding the first address after literal data, and
/// its export name, which no item may take.
const DATA_END_EXPORT: &str = "data_end";

/// Bytes in a wasm page.
const PAGE_SIZE: u64 = 64 * 1024;

/// The name of the built-in array type.
const ARRAY: &str = "array";

/// The name of the built-in tuple type.
const TUPLE: &str = "tuple";

/// The name of the host reference type.
const EXTERNREF: &str = "externref";

/// The name of the built-in type of types used as values.
const TYPE: &str = "type";

/// The fields of every array, in order.
const ARRAY_FIELDS: [&str; 2] = ["len", "ptr"];

/// The fields of a `type`, in order.
const TYPE_FIELDS: [&str; 2] = ["size", "align"];

/// The module that `extern` blocks without one import from.
const DEFAULT_IMPORT_MODULE: &str = "env";

/// A primitive stored as exactly one wasm value. `tuple()` is [`Ty::Unit`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Prim {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    F32,
    F64,
    Bool,
}

/// Index of a struct declaration, in declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StructId(u32);

/// Index of an enum declaration, in declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct EnumId(u32);

/// Index of an interned pointer type, which records the pointee.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PtrId(u32);

/// Index of an interned tuple type, which records the element types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TupleId(u32);

/// Index of an interned array type, which records the type of its `ptr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArrayId(u32);

/// Index of a generic struct's or function's type parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamId(u32);

/// Index of a generic function declaration, in declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GenericFnId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ty {
    Prim(Prim),
    Struct(StructId),
    /// An enum, stored as the value of its member, so laid out like the type
    /// of its values.
    Enum(EnumId),
    /// `&T`, an address in linear memory, stored as an `i32`.
    Ptr(PtrId),
    /// `tuple(A, B)`, which is laid out like a struct with a field per element.
    Tuple(TupleId),
    /// `array(T)`, a view of elements in linear memory that it doesn't own.
    /// Laid out like a struct with the fields `len: u32` and `ptr: &T`.
    Array(ArrayId),
    /// `type`, the value of a type written where a value belongs, as in
    /// `malloc(Point)`. Laid out like a struct with the fields `size: u32`
    /// and `align: u32`, which describe the type in memory.
    Type,
    /// A type parameter, which only the fields of its generic struct's
    /// declaration have. Uses of the struct replace it with a type argument.
    Param(ParamId),
    /// `externref`, an opaque reference that only the host can create. It
    /// can't be stored in linear memory, so nothing that holds one has a
    /// pointer type.
    ExternRef,
    /// `tuple()`, the return type of functions without one. Its values have no
    /// scalars, so they take no storage in wasm.
    Unit,
    /// The type of an expression that already failed to check. Compatible
    /// with everything, so one mistake is reported once.
    Error,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeError {
    pub kind: TypeErrorKind,
    /// `None` for errors in the [`Settings`], which no source file holds.
    pub span: Option<Span>,
    /// The instances of generic functions the error is in, innermost first.
    pub instances: Vec<InstanceSite>,
}

/// An instance of a generic function, and the call that first used it.
#[derive(Debug, Clone, PartialEq)]
pub struct InstanceSite {
    /// The instance as written, such as `id(i32)`.
    pub name: String,
    pub call: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeErrorKind {
    UnknownName(String),
    UnknownType(String),
    /// A function used as a value, or a struct or enum called as one.
    NotAValue(String),
    NotCallable(String),
    DuplicateItem(String),
    DuplicateField(String),
    DuplicateParam(String),
    /// A name bound twice by one pattern.
    DuplicateBinding(String),
    /// A struct that contains itself by value.
    RecursiveStruct(String),
    /// An enum whose values hold the enum itself, outside of any struct.
    RecursiveEnum(String),
    DuplicateMember(String),
    /// Two members of an enum with the same bits.
    DuplicateValue {
        member: String,
        same_as: String,
    },
    /// A member without a value in an enum whose values aren't integers,
    /// which count up.
    MissingValue(String),
    /// A member without a value that counts past the largest integer of the
    /// enum's type.
    MemberOutOfRange {
        member: String,
        ty: String,
    },
    NoMember {
        ty: String,
        member: String,
    },
    /// A generic struct that uses itself with ever larger type arguments,
    /// so it has no end of instances.
    ExpansiveRecursion(String),
    /// A type without type parameters given a list of type arguments, as in
    /// `i32()`.
    NotGeneric(String),
    /// A type that takes a list of type arguments written without one, as
    /// in `array`.
    MissingTypeArgs(String),
    /// A type parameter of generic function `func` that no argument of a
    /// call gives a type, so the call must give type arguments.
    CannotInfer {
        func: String,
        param: String,
    },
    /// A generic function instantiated within its instances, or those of
    /// others, too many times over, as recursion with ever larger type
    /// arguments would be.
    InstanceTooDeep(String),
    /// A generic function instantiated with type arguments too large to
    /// lower, as recursion that doubles them would make.
    InstanceTooLarge(String),
    /// A type given the wrong number of type arguments.
    TypeArgCount {
        name: String,
        expected: usize,
        found: usize,
    },
    /// A type that takes an empty list of type arguments, or one with at
    /// least some number, given too few.
    TooFewTypeArgs {
        name: String,
        at_least: usize,
        found: usize,
    },
    Mismatch {
        expected: String,
        found: String,
    },
    InvalidOperand {
        op: &'static str,
        ty: String,
    },
    InvalidCast {
        from: String,
        to: String,
    },
    IntOutOfRange(String),
    NoField {
        ty: String,
        field: String,
    },
    NotAssignable,
    /// `&` applied to something not behind a pointer, such as a local.
    NotAddressable,
    /// A pointer to a type holding an `externref`, which can't be in memory.
    NotStorable(String),
    ImmutableAssign(String),
    MissingArg(String),
    UnknownLabel(String),
    DuplicateArg(String),
    PositionalAfterLabel,
    /// A struct constructed with a positional argument.
    UnlabelledField,
    TooManyArgs {
        expected: usize,
        found: usize,
    },
    MissingReturn(String),
    BreakOutsideLoop,
    ContinueOutsideLoop,
    /// A global initializer or enum member's value that can't be evaluated
    /// at compile time.
    NotConstant,
    /// A global initializer that traps, such as dividing by zero.
    ConstTrap,
    /// A `pub` item whose export name is taken by the module itself.
    ReservedExport(String),
    /// An item of another module that isn't `pub`.
    Private(String),
    /// A name that no item of the module `module` has.
    NoItem {
        module: String,
        item: String,
    },
    /// A field that isn't `pub`, used outside the module of its struct.
    PrivateField {
        ty: String,
        field: String,
    },
    /// A type that isn't `pub` in the type of `item`, which is.
    PrivateInPublic {
        ty: String,
        item: String,
    },
    /// A start function named in the [`Settings`] that isn't a function.
    UnknownStart(String),
    /// A start function that takes arguments or returns something.
    InvalidStart(String),
    /// Literal data that doesn't fit in the memory's initial pages.
    DataTooLarge {
        bytes: u32,
        min_pages: u32,
    },
    /// A string or array literal outside a global initializer.
    LiteralOutsideGlobal,
    /// `[]` with no type to give its elements.
    UntypedEmptyArray,
    /// An expression where a type argument should be.
    NotAType,
    /// A type argument given a label, as only fields and parameters are.
    LabelledTypeArg,
}

#[derive(Default)]
struct Checker {
    /// The names declared in each module: its items and the modules it
    /// imports.
    scopes: HashMap<FileId, HashMap<String, Entry>>,
    /// The module whose names are in scope.
    module: FileId,
    /// The module whose `pub` items are exported.
    entry: FileId,
    /// Struct declarations in declaration order, then instances of generic
    /// ones as they are used.
    structs: Vec<StructDef>,
    /// Each instance of a generic struct by its declaration and type
    /// arguments.
    instances: HashMap<(StructId, Vec<Ty>), StructId>,
    /// Every generic struct's type parameters, indexed by [`ParamId`].
    params: Vec<ParamDef>,
    /// The type parameters in scope, while resolving a generic struct's
    /// fields.
    type_params: Vec<(String, Ty)>,
    /// Enum declarations in declaration order.
    enums: Vec<EnumDef>,
    /// Instances whose fields wait on every generic struct's being defined.
    pending: Vec<StructId>,
    /// Whether every generic struct's fields are known, so instances can
    /// be given theirs.
    generics_defined: bool,
    /// The pointee of each pointer type.
    pointees: Vec<Ty>,
    ptr_ids: HashMap<Ty, PtrId>,
    /// The element types of each tuple type.
    tuples: Vec<Vec<Ty>>,
    tuple_ids: HashMap<Vec<Ty>, TupleId>,
    /// The type of each array type's `ptr` field, which points to its
    /// elements.
    arrays: Vec<Ty>,
    array_ids: HashMap<Ty, ArrayId>,
    /// Whether every struct's fields are known, so pointer types can be
    /// checked for storability as they are resolved.
    structs_defined: bool,
    /// Every function, indexed by [`FuncId`]: imports, then definitions,
    /// then the functions in `synths`.
    funcs: Vec<FuncSig>,
    /// How many of `funcs` are imported. They come first.
    import_count: u32,
    /// The functions the checker creates as they are used, whose signatures
    /// end `funcs` in the same order.
    synths: Vec<Synth>,
    /// The function `==` compares each array type through.
    eq_funcs: HashMap<Ty, FuncId>,
    /// Generic function declarations, indexed by [`GenericFnId`].
    generic_fns: Vec<GenericFn>,
    /// Each instance of a generic function by its declaration and type
    /// arguments.
    fn_instances: HashMap<(GenericFnId, Vec<Ty>), FuncId>,
    /// While lowering an instance of a generic function, it and the
    /// instances whose calls led to it, innermost first. Given to errors.
    instance_chain: Vec<InstanceSite>,
    /// `None` until the global's initializer has been checked.
    globals: Vec<Option<GlobalDef>>,
    ir_globals: Vec<ir::Global>,
    /// The contents of literals, placed in memory in the order they are
    /// lowered.
    data: Vec<ir::Data>,
    /// The first address after `data`.
    data_end: u32,
    errors: Vec<TypeError>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Item {
    Func(FuncId),
    GenericFn(GenericFnId),
    Struct(StructId),
    Enum(EnumId),
    Global(usize),
    /// A module, by the name it's imported as.
    Module(FileId),
}

/// Why a module's item can't be reached from another.
enum Member {
    Private,
    Missing,
}

/// A name declared in a module.
#[derive(Debug, Clone, Copy)]
struct Entry {
    item: Item,
    /// Whether other modules can see it.
    is_pub: bool,
}

struct StructDef {
    /// The declared name, or for an instance, its type as written.
    name: String,
    /// The module that declares it, or for an instance, its declaration.
    module: FileId,
    is_pub: bool,
    /// The [`Ty::Param`] of each type parameter of a generic declaration.
    params: Vec<Ty>,
    /// Set for instances of generic declarations.
    instance: Option<Instance>,
    /// Empty for instances whose type arguments hold type parameters, which
    /// are never laid out.
    fields: Vec<FieldDef>,
}

#[derive(Clone)]
struct FieldDef {
    name: String,
    ty: Ty,
    /// Whether modules other than the struct's can use it.
    is_pub: bool,
    span: Span,
}

#[derive(Clone)]
struct FuncSig {
    name: String,
    params: Vec<(String, Ty)>,
    ret: Ty,
}

/// A function the checker creates, rather than one defined in the source.
enum Synth {
    /// Compares two arrays of this type.
    Eq(Ty),
    Instance(FnInstance),
}

struct GlobalDef {
    ty: Ty,
    mutable: bool,
    /// One wasm global per scalar leaf of `ty`.
    slots: Vec<GlobalId>,
}

/// A name bound by a pattern.
struct Bound<'p> {
    name: &'p str,
    span: Span,
    ty: Ty,
    /// The leaves of the pattern's value that the name covers.
    leaves: Range<usize>,
}

/// State for checking and lowering one function body, or one global
/// initializer.
struct Body<'c> {
    ck: &'c mut Checker,
    ret: Ty,
    locals: Vec<ir::Local>,
    scopes: Vec<HashMap<String, Var>>,
    /// Enclosing wasm labels, innermost last.
    labels: Vec<Label>,
    /// Whether this is a global initializer, the only place literals that
    /// need memory can be.
    global: bool,
}

#[derive(Clone)]
struct Var {
    ty: Ty,
    mutable: bool,
    /// One local per scalar leaf of `ty`.
    slots: Vec<LocalId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Label {
    /// The `block` around a loop.
    Break,
    /// The `loop` itself.
    Continue,
    /// An `if`.
    Other,
}

/// A variable, a field of one, or memory behind a pointer, that can be
/// assigned.
struct Place {
    name: String,
    ty: Ty,
    mutable: bool,
    /// Computes the address of a `Slots::Memory` place. Runs before anything
    /// else in the assignment.
    pre: Vec<Stmt>,
    slots: Slots,
}

enum Slots {
    Local(Vec<LocalId>),
    Global(Vec<GlobalId>),
    /// `offset` bytes past `addr`, which is a local or constant so that it
    /// can be reused.
    Memory {
        addr: Expr,
        offset: u32,
    },
}

/// A lowered expression: run `pre`, then evaluate `scalars` in order, one per
/// scalar leaf of the expression's type.
#[derive(Default)]
struct Value {
    pre: Vec<Stmt>,
    scalars: Vec<(ValType, Expr)>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Visit {
    New,
    Active,
    Done,
}

/// Where one scalar leaf of a type lives in memory.
struct Cell {
    /// Bytes from the start of the value.
    offset: u32,
    ty: ValType,
    load: LoadOp,
    store: StoreOp,
    /// Whether the cell holds a `bool`, which may be any byte in memory.
    bool: bool,
}

/// Why a global initializer could not be folded.
enum Fold {
    NotConstant,
    Trap,
}

impl Prim {
    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "i8" => Self::I8,
            "i16" => Self::I16,
            "i32" => Self::I32,
            "i64" => Self::I64,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "f32" => Self::F32,
            "f64" => Self::F64,
            "bool" => Self::Bool,
            _ => return None,
        })
    }

    fn name(self) -> &'static str {
        match self {
            Self::I8 => "i8",
            Self::I16 => "i16",
            Self::I32 => "i32",
            Self::I64 => "i64",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::F32 => "f32",
            Self::F64 => "f64",
            Self::Bool => "bool",
        }
    }

    fn val_type(self) -> ValType {
        match self {
            Self::I64 | Self::U64 => ValType::I64,
            Self::F32 => ValType::F32,
            Self::F64 => ValType::F64,
            _ => ValType::I32,
        }
    }

    fn is_int(self) -> bool {
        !matches!(self, Self::F32 | Self::F64 | Self::Bool)
    }

    fn is_signed(self) -> bool {
        matches!(self, Self::I8 | Self::I16 | Self::I32 | Self::I64)
    }

    fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }

    fn is_numeric(self) -> bool {
        self != Self::Bool
    }

    /// Size in memory, which is also its alignment.
    fn size(self) -> u32 {
        match self {
            Self::I8 | Self::U8 | Self::Bool => 1,
            Self::I16 | Self::U16 => 2,
            Self::I32 | Self::U32 | Self::F32 => 4,
            Self::I64 | Self::U64 | Self::F64 => 8,
        }
    }

    fn load(self) -> LoadOp {
        match self {
            Self::I8 => LoadOp::Load8S,
            Self::U8 | Self::Bool => LoadOp::Load8U,
            Self::I16 => LoadOp::Load16S,
            Self::U16 => LoadOp::Load16U,
            _ => LoadOp::Load,
        }
    }

    fn store(self) -> StoreOp {
        match self.size() {
            1 => StoreOp::Store8,
            2 => StoreOp::Store16,
            _ => StoreOp::Store,
        }
    }

    /// Inclusive bounds of an integer type.
    fn range(self) -> (i128, i128) {
        match self {
            Self::I8 => (i8::MIN.into(), i8::MAX.into()),
            Self::I16 => (i16::MIN.into(), i16::MAX.into()),
            Self::I32 => (i32::MIN.into(), i32::MAX.into()),
            Self::I64 => (i64::MIN.into(), i64::MAX.into()),
            Self::U8 => (0, u8::MAX.into()),
            Self::U16 => (0, u16::MAX.into()),
            Self::U32 => (0, u32::MAX.into()),
            Self::U64 => (0, u64::MAX.into()),
            Self::F32 | Self::F64 | Self::Bool => (0, 0),
        }
    }
}

impl fmt::Display for TypeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownName(name) => write!(f, "unknown name `{name}`"),
            Self::UnknownType(name) => write!(f, "unknown type `{name}`"),
            Self::NotAValue(name) => write!(f, "`{name}` is not a value"),
            Self::NotCallable(name) => write!(f, "`{name}` is not callable"),
            Self::DuplicateItem(name) => write!(f, "`{name}` is already defined"),
            Self::DuplicateField(name) => write!(f, "duplicate field `{name}`"),
            Self::DuplicateParam(name) => write!(f, "duplicate parameter `{name}`"),
            Self::DuplicateBinding(name) => write!(f, "`{name}` is bound more than once"),
            Self::RecursiveStruct(name) => write!(f, "struct `{name}` contains itself"),
            Self::RecursiveEnum(name) => write!(f, "enum `{name}` contains itself"),
            Self::DuplicateMember(name) => write!(f, "duplicate member `{name}`"),
            Self::DuplicateValue { member, same_as } => {
                write!(f, "member `{member}` has the same value as `{same_as}`")
            }
            Self::MissingValue(name) => write!(
                f,
                "member `{name}` needs a value, as only members of integer enums count up"
            ),
            Self::MemberOutOfRange { member, ty } => {
                write!(f, "member `{member}` counts past the largest `{ty}`")
            }
            Self::NoMember { ty, member } => write!(f, "`{ty}` has no member `{member}`"),
            Self::ExpansiveRecursion(name) => write!(
                f,
                "struct `{name}` uses itself with ever larger type arguments"
            ),
            Self::NotGeneric(name) => write!(f, "`{name}` has no type parameters"),
            Self::InstanceTooDeep(name) => write!(
                f,
                "instance of `{name}` is nested more than {} instances deep; \
                 its type arguments may grow without end",
                generic_fn::MAX_INSTANCE_DEPTH
            ),
            Self::InstanceTooLarge(name) => write!(
                f,
                "type arguments of `{name}` have more than {} parts; \
                 they may grow without end",
                generic_fn::MAX_INSTANCE_SIZE
            ),
            Self::CannotInfer { func, param } => write!(
                f,
                "cannot infer `{param}` for `{func}`; give its type arguments, as in `{func}(...)(...)`"
            ),
            Self::MissingTypeArgs(name) => write!(f, "`{name}` needs a list of type arguments"),
            Self::TypeArgCount {
                name,
                expected,
                found,
            } => {
                let s = if *expected == 1 { "" } else { "s" };
                write!(
                    f,
                    "`{name}` takes {expected} type argument{s}, found {found}"
                )
            }
            Self::TooFewTypeArgs {
                name,
                at_least,
                found,
            } => write!(
                f,
                "`{name}` takes 0 or at least {at_least} type arguments, found {found}"
            ),
            Self::Mismatch { expected, found } => {
                write!(f, "expected `{expected}`, found `{found}`")
            }
            Self::InvalidOperand { op, ty } => write!(f, "`{op}` can't be applied to `{ty}`"),
            Self::InvalidCast { from, to } => write!(f, "can't cast `{from}` as `{to}`"),
            Self::IntOutOfRange(ty) => write!(f, "literal out of range for `{ty}`"),
            Self::NoField { ty, field } => write!(f, "`{ty}` has no field `{field}`"),
            Self::NotAssignable => write!(f, "invalid assignment target"),
            Self::NotAddressable => write!(f, "only memory behind a pointer has an address"),
            Self::NotStorable(ty) => write!(f, "`{ty}` can't be stored in memory"),
            Self::ImmutableAssign(name) => write!(f, "can't assign to immutable `{name}`"),
            Self::MissingArg(name) => write!(f, "missing argument `{name}`"),
            Self::UnknownLabel(name) => write!(f, "no parameter named `{name}`"),
            Self::DuplicateArg(name) => write!(f, "argument `{name}` given twice"),
            Self::PositionalAfterLabel => {
                write!(f, "positional arguments must come before labelled ones")
            }
            Self::UnlabelledField => write!(f, "struct fields must be labelled"),
            Self::TooManyArgs { expected, found } => {
                write!(f, "expected {expected} arguments, found {found}")
            }
            Self::MissingReturn(name) => write!(f, "`{name}` can finish without returning"),
            Self::BreakOutsideLoop => write!(f, "`break` outside of a loop"),
            Self::ContinueOutsideLoop => write!(f, "`continue` outside of a loop"),
            Self::NotConstant => write!(f, "global initializers and enum members must be constant"),
            Self::ConstTrap => write!(f, "constant evaluation traps"),
            Self::ReservedExport(name) => write!(f, "the export name `{name}` is reserved"),
            Self::UnknownStart(name) => write!(f, "no function named `{name}` to start"),
            Self::Private(name) => write!(f, "`{name}` is private"),
            Self::NoItem { module, item } => write!(f, "`{module}` has no item `{item}`"),
            Self::PrivateField { ty, field } => write!(f, "field `{field}` of `{ty}` is private"),
            Self::PrivateInPublic { ty, item } => {
                write!(f, "private type `{ty}` in the type of `pub` item `{item}`")
            }
            Self::InvalidStart(name) => write!(
                f,
                "start function `{name}` must take no arguments and return nothing"
            ),
            Self::DataTooLarge { bytes, min_pages } => write!(
                f,
                "literals take {bytes} bytes, more than the {min_pages} pages memory starts with"
            ),
            Self::LiteralOutsideGlobal => write!(
                f,
                "string and array literals are only allowed in global initializers"
            ),
            Self::UntypedEmptyArray => write!(f, "can't infer the element type of `[]`"),
            Self::NotAType => write!(f, "expected a type"),
            Self::LabelledTypeArg => write!(f, "type arguments can't be labelled"),
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.span {
            Some(span) => write!(f, "{} at {}..{}", self.kind, span.start, span.end)?,
            None => self.kind.fmt(f)?,
        }
        for site in &self.instances {
            let call = site.call;
            write!(
                f,
                ", in `{}` called at {}..{}",
                site.name, call.start, call.end
            )?;
        }
        Ok(())
    }
}

impl std::error::Error for TypeError {}

/// Resolves names in, type checks, and lowers a loaded program to one wasm
/// module, giving it the memory and start function `settings` describe.
///
/// Checking continues past errors, so every error in the program is reported
/// at once.
pub fn check(program: &Program, settings: &Settings) -> Result<ir::Module, Vec<TypeError>> {
    let mut ck = Checker {
        entry: program.entry,
        ..Checker::default()
    };
    ck.declare(program);
    ck.define_structs(program);
    ck.define_funcs(program);
    ck.define_globals(program);
    ck.end_data(settings);
    let start = settings
        .start
        .as_ref()
        .and_then(|name| ck.resolve_start(program, name));
    let imports = ck.lower_imports(program);
    let mut funcs = ck.lower_funcs(program);
    funcs.extend(ck.lower_synths(program));
    if ck.errors.is_empty() {
        Ok(ir::Module {
            memory: ir::Memory {
                min_pages: settings.memory.min_pages,
                max_pages: settings.memory.max_pages,
                export: MEMORY_EXPORT.to_string(),
            },
            data: ck.data,
            globals: ck.ir_globals,
            imports,
            funcs,
            start,
        })
    } else {
        Err(ck.errors)
    }
}

impl Checker {
    fn error(&mut self, kind: TypeErrorKind, span: Span) {
        self.errors.push(TypeError {
            kind,
            span: Some(span),
            instances: self.instance_chain.clone(),
        });
    }

    /// Registers every item's name, so bodies can refer to later items.
    fn declare(&mut self, program: &Program) {
        self.import_count = extern_fns(program).count() as u32;
        self.funcs = fn_sigs(program)
            .map(|(_, sig)| FuncSig {
                name: sig.name.name.clone(),
                params: Vec::new(),
                ret: Ty::Unit,
            })
            .collect();
        for import in &program.imports {
            self.module = import.module;
            self.declare_name(&import.name, Item::Module(import.target), import.is_pub);
        }
        let (mut next_import, mut next_def) = (0, self.import_count);
        for item in &program.items {
            self.module = item.span.file;
            let (name, entry) = match &item.kind {
                ItemKind::Struct(s) => {
                    let id = StructId(self.structs.len() as u32);
                    let params = self.new_params(&s.params);
                    self.structs.push(StructDef {
                        name: s.name.name.clone(),
                        module: self.module,
                        is_pub: item.is_pub,
                        params,
                        instance: None,
                        fields: Vec::new(),
                    });
                    (&s.name, Item::Struct(id))
                }
                ItemKind::Fn(f) if !f.sig.type_params.is_empty() => {
                    (&f.sig.name, Item::GenericFn(self.declare_generic_fn(f)))
                }
                ItemKind::Fn(f) => {
                    next_def += 1;
                    (&f.sig.name, Item::Func(FuncId(next_def - 1)))
                }
                ItemKind::Extern(block) => {
                    for f in &block.fns {
                        self.declare_name(&f.sig.name, Item::Func(FuncId(next_import)), f.is_pub);
                        next_import += 1;
                    }
                    continue;
                }
                ItemKind::Binding(b) => {
                    for name in pattern_names(&b.pattern) {
                        self.globals.push(None);
                        self.declare_item(item, &name, Item::Global(self.globals.len() - 1));
                    }
                    continue;
                }
                ItemKind::Enum(e) => (&e.name, Item::Enum(self.declare_enum(e, item.is_pub))),
                // Replaced by the imported items when loading.
                ItemKind::Import(_) => continue,
            };
            self.declare_item(item, name, entry);
        }
    }

    /// Declares a name defined by `item`, which may export it.
    fn declare_item(&mut self, item: &parse::Item, name: &Ident, entry: Item) {
        self.declare_name(name, entry, item.is_pub);
        if self.exports(item) && [MEMORY_EXPORT, DATA_END_EXPORT].contains(&name.name.as_str()) {
            self.error(TypeErrorKind::ReservedExport(name.name.clone()), name.span);
        }
    }

    /// Declares `name` in the current module.
    fn declare_name(&mut self, name: &Ident, item: Item, is_pub: bool) {
        let scope = self.scopes.entry(self.module).or_default();
        if scope.contains_key(&name.name) || [ARRAY, TUPLE, TYPE].contains(&name.name.as_str()) {
            self.error(TypeErrorKind::DuplicateItem(name.name.clone()), name.span);
        } else {
            scope.insert(name.name.clone(), Entry { item, is_pub });
        }
    }

    /// Whether `item` is exported: it's `pub` and in the entry module.
    fn exports(&self, item: &parse::Item) -> bool {
        item.is_pub && item.span.file == self.entry
    }

    /// The item `name` names in the current module.
    fn item(&self, name: &str) -> Option<Item> {
        let entry = self.scopes.get(&self.module)?.get(name)?;
        Some(entry.item)
    }

    /// The item `name` names in `module`, as other modules see it.
    fn member_of(&self, module: FileId, name: &str) -> Result<Item, Member> {
        let entry = self.scopes.get(&module).and_then(|scope| scope.get(name));
        match entry {
            Some(entry) if entry.is_pub || module == self.module => Ok(entry.item),
            Some(_) => Err(Member::Private),
            None => Err(Member::Missing),
        }
    }

    /// [`Self::member_of`], reporting why `name` is unreachable through
    /// `path`, the module as written.
    fn reach(&mut self, module: FileId, path: &str, name: &Ident) -> Option<Item> {
        match self.member_of(module, &name.name) {
            Ok(item) => Some(item),
            Err(Member::Private) => {
                self.error(TypeErrorKind::Private(name.name.clone()), name.span);
                None
            }
            Err(Member::Missing) => {
                let kind = TypeErrorKind::NoItem {
                    module: path.to_string(),
                    item: name.name.clone(),
                };
                self.error(kind, name.span);
                None
            }
        }
    }

    /// Resolves the type of every enum's values and every struct's fields,
    /// reporting generic structs that recurse without end and types that
    /// contain themselves, then gives every instance used so far its fields.
    fn define_structs(&mut self, program: &Program) {
        self.resolve_enums(program);
        let decls = program.items.iter().filter_map(|item| match &item.kind {
            ItemKind::Struct(s) => Some(s),
            _ => None,
        });
        let mut decl_count = 0;
        for (id, decl) in decls.enumerate() {
            decl_count += 1;
            self.module = decl.name.span.file;
            let params = self.structs[id].params.clone();
            self.declare_type_params(&decl.params, &params);
            let mut fields: Vec<FieldDef> = Vec::new();
            for field in &decl.fields {
                let ty = self.resolve_ty(&field.ty);
                if self.structs[id].is_pub && field.is_pub {
                    self.check_public(ty, field.ty.span, &field.name.name);
                }
                if fields.iter().any(|f| f.name == field.name.name) {
                    let kind = TypeErrorKind::DuplicateField(field.name.name.clone());
                    self.error(kind, field.name.span);
                    continue;
                }
                fields.push(FieldDef {
                    name: field.name.name.clone(),
                    ty,
                    is_pub: field.is_pub,
                    span: field.span,
                });
            }
            self.type_params.clear();
            self.structs[id].fields = fields;
        }
        self.break_expansions(decl_count);
        // Whether a declaration contains another by value doesn't depend on
        // type arguments, so a cycle of declarations is caught once here.
        let mut visits = vec![Visit::New; self.structs.len()];
        for id in 0..decl_count {
            self.break_cycles(id, &mut visits, true);
        }
        self.generics_defined = true;
        while let Some(id) = self.pending.pop() {
            self.fill_instance(id);
        }
        // Type arguments can close a cycle through a declaration, as in
        // `struct S: w: W(S)` where `struct(T) W: x: T`.
        let mut visits: Vec<_> = (0..self.structs.len())
            .map(|id| match self.is_open(StructId(id as u32)) {
                true => Visit::Done,
                false => Visit::New,
            })
            .collect();
        for id in 0..self.structs.len() {
            self.break_cycles(id, &mut visits, false);
        }
        self.check_field_pointers(0..self.structs.len());
        self.check_enum_pointers();
        self.structs_defined = true;
    }

    /// Reports pointer fields whose pointee can't be stored in memory, which
    /// `resolve_ty` couldn't know before every struct was defined, and gives
    /// them the error type. Only checks the structs `ids`.
    fn check_field_pointers(&mut self, ids: Range<usize>) {
        for id in ids {
            for i in 0..self.structs[id].fields.len() {
                if let Some(ty) = self.unstorable_pointee(self.structs[id].fields[i].ty) {
                    let kind = TypeErrorKind::NotStorable(self.ty_name(ty));
                    self.error(kind, self.field_site(id, i));
                    self.structs[id].fields[i].ty = Ty::Error;
                }
            }
        }
    }

    /// Where to report an error in field `i` of struct `id`: the field
    /// itself, or where an instance was used, since its declaration is fine.
    fn field_site(&self, id: usize, i: usize) -> Span {
        match &self.structs[id].instance {
            Some(instance) => instance.site,
            None => self.structs[id].fields[i].span,
        }
    }

    /// The first type behind a pointer in `ty` that can't be stored in
    /// memory, not counting the fields of structs, which are checked on their
    /// own.
    fn unstorable_pointee(&self, ty: Ty) -> Option<Ty> {
        let components = self.components(ty);
        match ty {
            // An array's elements are behind its `ptr`.
            Ty::Ptr(_) | Ty::Array(_) if !self.storable(components[0]) => Some(components[0]),
            _ => components
                .into_iter()
                .find_map(|component| self.unstorable_pointee(component)),
        }
    }

    /// Reports structs that contain themselves by value, and cuts each cycle
    /// by giving the offending field the error type. With `by_declaration`,
    /// an instance stands for its generic declaration.
    fn break_cycles(&mut self, id: usize, visits: &mut [Visit], by_declaration: bool) {
        if visits[id] != Visit::New {
            return;
        }
        visits[id] = Visit::Active;
        for i in 0..self.structs[id].fields.len() {
            let mut children = Vec::new();
            self.push_inline_structs(self.structs[id].fields[i].ty, &mut children);
            for StructId(child) in children {
                let mut child = child as usize;
                if by_declaration && let Some(instance) = &self.structs[child].instance {
                    child = instance.generic.0 as usize;
                }
                match visits[child] {
                    Visit::Active => {
                        let kind = TypeErrorKind::RecursiveStruct(self.structs[id].name.clone());
                        self.error(kind, self.field_site(id, i));
                        self.structs[id].fields[i].ty = Ty::Error;
                        break;
                    }
                    Visit::New => self.break_cycles(child, visits, by_declaration),
                    Visit::Done => {}
                }
            }
        }
        visits[id] = Visit::Done;
    }

    /// The structs that a value of type `ty` holds directly, rather than
    /// behind a pointer.
    fn push_inline_structs(&self, ty: Ty, out: &mut Vec<StructId>) {
        match ty {
            Ty::Struct(id) => out.push(id),
            Ty::Enum(id) => self.push_inline_structs(self.enum_ty(id), out),
            Ty::Tuple(id) => {
                for elem in &self.tuples[id.0 as usize] {
                    self.push_inline_structs(*elem, out);
                }
            }
            _ => {}
        }
    }

    /// Resolves the signature of every function, including generic ones.
    fn define_funcs(&mut self, program: &Program) {
        for (id, (is_pub, decl)) in fn_sigs(program).enumerate() {
            self.module = decl.name.span.file;
            let (params, ret) = self.resolve_sig(decl);
            if is_pub {
                self.check_public_sig(decl, &params, ret);
            }
            self.funcs[id].params = params;
            self.funcs[id].ret = ret;
        }
        self.define_generic_fns(program);
    }

    /// Reports types in `sig`, resolved as `params` and `ret`, that aren't
    /// `pub`.
    fn check_public_sig(&mut self, sig: &FnSig, params: &[(String, Ty)], ret: Ty) {
        let name = &sig.name.name;
        for (param, (_, ty)) in sig.params.iter().zip(params) {
            self.check_public(*ty, param.ty.span, name);
        }
        if let Some(written) = &sig.ret {
            self.check_public(ret, written.span, name);
        }
    }

    /// Reports a type in `ty`, written at `span` in the type of `pub` item
    /// `item`, that isn't `pub`.
    fn check_public(&mut self, ty: Ty, span: Span, item: &str) {
        if let Some(private) = self.private_part(ty) {
            let kind = TypeErrorKind::PrivateInPublic {
                ty: self.ty_name(private),
                item: item.to_string(),
            };
            self.error(kind, span);
        }
    }

    /// The first struct or enum in `ty` that isn't `pub`.
    fn private_part(&self, ty: Ty) -> Option<Ty> {
        match ty {
            Ty::Struct(id) => {
                let def = &self.structs[id.0 as usize];
                if !def.is_pub {
                    return Some(ty);
                }
                let args = def.instance.iter().flat_map(|instance| &instance.args);
                args.into_iter().find_map(|arg| self.private_part(*arg))
            }
            Ty::Enum(id) => (!self.enums[id.0 as usize].is_pub).then_some(ty),
            _ => self
                .components(ty)
                .into_iter()
                .find_map(|component| self.private_part(component)),
        }
    }

    /// The types of the parameters and result of `sig`.
    fn resolve_sig(&mut self, sig: &FnSig) -> (Vec<(String, Ty)>, Ty) {
        let mut params: Vec<(String, Ty)> = Vec::new();
        for param in &sig.params {
            if params.iter().any(|(name, _)| *name == param.name.name) {
                let kind = TypeErrorKind::DuplicateParam(param.name.name.clone());
                self.error(kind, param.name.span);
            }
            params.push((param.name.name.clone(), self.resolve_ty(&param.ty)));
        }
        let ret = sig.ret.as_ref().map_or(Ty::Unit, |ty| self.resolve_ty(ty));
        (params, ret)
    }

    /// Checks and folds global initializers and the values of enum members,
    /// in declaration order.
    fn define_globals(&mut self, program: &Program) {
        let (mut index, mut enum_index) = (0, 0);
        for item in &program.items {
            self.module = item.span.file;
            let decl = match &item.kind {
                ItemKind::Binding(decl) => decl,
                ItemKind::Enum(decl) => {
                    self.define_members(EnumId(enum_index), decl);
                    enum_index += 1;
                    continue;
                }
                _ => continue,
            };
            let mut body = Body::new(self, Ty::Unit);
            body.global = true;
            let (ty, value) = body.binding_value(decl);
            let mutable = decl.mutability == Mutability::Var;
            let inits = self.fold_value(&value, decl.value.span);
            // Each name gets its own globals, in the order `declare` gave them.
            for bound in self.destructure(&decl.pattern, ty) {
                let mut slots = Vec::new();
                let leaves = self.leaves(bound.ty, bound.name);
                for ((name, vt), i) in leaves.into_iter().zip(bound.leaves) {
                    slots.push(GlobalId(self.ir_globals.len() as u32));
                    self.ir_globals.push(ir::Global {
                        export: self.exports(item).then(|| name.clone()),
                        name,
                        ty: vt,
                        mutable,
                        init: inits.get(i).copied().unwrap_or(zero(vt)),
                    });
                }
                let ty = bound.ty;
                if item.is_pub {
                    self.check_public(ty, bound.span, bound.name);
                }
                self.globals[index] = Some(GlobalDef { ty, mutable, slots });
                index += 1;
            }
        }
    }

    /// Checks that literal data fits in the memory's initial pages, and
    /// exports where it ends.
    fn end_data(&mut self, settings: &Settings) {
        let min_pages = settings.memory.min_pages;
        if u64::from(self.data_end) > u64::from(min_pages) * PAGE_SIZE {
            self.errors.push(TypeError {
                kind: TypeErrorKind::DataTooLarge {
                    bytes: self.data_end,
                    min_pages,
                },
                span: None,
                instances: Vec::new(),
            });
        }
        self.ir_globals.push(ir::Global {
            name: DATA_END_EXPORT.to_string(),
            ty: ValType::I32,
            mutable: false,
            init: Const::I32(self.data_end as i32),
            export: Some(DATA_END_EXPORT.to_string()),
        });
    }

    /// The function `name`, which must take and return nothing. `None` after
    /// reporting an error.
    fn resolve_start(&mut self, program: &Program, name: &str) -> Option<FuncId> {
        self.module = self.entry;
        if let Some(Item::GenericFn(generic)) = self.item(name) {
            let (_, decl) = generic_fn_decls(program).nth(generic.0 as usize).unwrap();
            let span = decl.sig.name.span;
            self.error(TypeErrorKind::InvalidStart(name.to_string()), span);
            return None;
        }
        let Some(Item::Func(id)) = self.item(name) else {
            self.errors.push(TypeError {
                kind: TypeErrorKind::UnknownStart(name.to_string()),
                span: None,
                instances: Vec::new(),
            });
            return None;
        };
        let sig = &self.funcs[id.0 as usize];
        if !sig.params.is_empty() || !matches!(sig.ret, Ty::Unit | Ty::Error) {
            let span = fn_sigs(program).nth(id.0 as usize).unwrap().1.name.span;
            self.error(TypeErrorKind::InvalidStart(name.to_string()), span);
            return None;
        }
        Some(id)
    }

    fn lower_imports(&self, program: &Program) -> Vec<ir::Import> {
        let imports = extern_fns(program).zip(&self.funcs);
        imports
            .map(|((block, decl), sig)| ir::Import {
                name: sig.name.clone(),
                module: block
                    .module
                    .clone()
                    .unwrap_or_else(|| DEFAULT_IMPORT_MODULE.to_string()),
                field: decl.import_name.clone().unwrap_or_else(|| sig.name.clone()),
                params: sig
                    .params
                    .iter()
                    .flat_map(|(_, ty)| self.val_types(*ty))
                    .collect(),
                results: self.val_types(sig.ret),
            })
            .collect()
    }

    fn lower_funcs(&mut self, program: &Program) -> Vec<ir::Func> {
        let mut funcs = Vec::new();
        for (i, (item, decl)) in fn_decls(program).enumerate() {
            self.module = item.span.file;
            let sig = self.funcs[self.import_count as usize + i].clone();
            let export = self.exports(item).then(|| sig.name.clone());
            funcs.push(self.lower_body(sig, &decl.body, item.span, export));
        }
        funcs
    }

    /// Lowers a function with signature `sig` and body `block`, declared by
    /// the item spanning `span`, and exported as `export` if given.
    fn lower_body(
        &mut self,
        sig: FuncSig,
        block: &parse::Block,
        span: Span,
        export: Option<String>,
    ) -> ir::Func {
        let mut body = Body::new(self, sig.ret);
        for (name, ty) in &sig.params {
            let slots = body.alloc(name, *ty);
            body.bind(name, *ty, false, slots);
        }
        let params = body.locals.iter().map(|local| local.ty).collect();
        let mut stmts = body.block(block);
        let locals = body.locals;
        let results = self.val_types(sig.ret);
        if !matches!(sig.ret, Ty::Unit | Ty::Error) && !diverges(block) {
            self.error(TypeErrorKind::MissingReturn(sig.name.clone()), span);
        }
        // Wasm validates the end of a function with results as reachable
        // unless it follows a `return`.
        if !results.is_empty() && !matches!(stmts.last(), Some(Stmt::Return(_))) {
            stmts.push(Stmt::Unreachable);
        }
        ir::Func {
            export,
            name: sig.name,
            params,
            results,
            locals,
            body: stmts,
        }
    }

    /// Lowers every function in `synths`, including those that lowering the
    /// others creates.
    fn lower_synths(&mut self, program: &Program) -> Vec<ir::Func> {
        let first = self.funcs.len() - self.synths.len();
        let mut funcs = Vec::new();
        while funcs.len() < self.synths.len() {
            let id = FuncId((first + funcs.len()) as u32);
            let func = match &self.synths[funcs.len()] {
                Synth::Eq(ty) => self.lower_eq_func(id, *ty),
                Synth::Instance(instance) => {
                    let instance = instance.clone();
                    self.lower_instance(program, id, instance)
                }
            };
            funcs.push(func);
        }
        funcs
    }

    fn resolve_ty(&mut self, ty: &parse::Type) -> Ty {
        match &ty.kind {
            TypeKind::Named(name, args) => self.resolve_named(None, name, args, ty.span),
            TypeKind::Qualified(module, inner) => match self.item(&module.name) {
                Some(Item::Module(target)) => self.resolve_member_ty(target, &module.name, inner),
                _ => {
                    self.error(TypeErrorKind::UnknownName(module.name.clone()), module.span);
                    Ty::Error
                }
            },
            TypeKind::Pointer(pointee) => match self.resolve_ty(pointee) {
                Ty::Error => Ty::Error,
                // Struct fields are checked once every struct is defined.
                pointee if self.structs_defined && !self.storable(pointee) => {
                    let kind = TypeErrorKind::NotStorable(self.ty_name(pointee));
                    self.error(kind, ty.span);
                    Ty::Error
                }
                pointee => self.ptr_to(pointee),
            },
        }
    }

    /// Resolves `ty`, written after `path.` where `path` names `module`.
    fn resolve_member_ty(&mut self, module: FileId, path: &str, ty: &parse::Type) -> Ty {
        match &ty.kind {
            TypeKind::Named(name, args) => {
                let ident = Ident {
                    name: name.clone(),
                    span: ty.span,
                };
                match self.reach(module, path, &ident) {
                    Some(item) => self.resolve_named(Some(item), name, args, ty.span),
                    None => Ty::Error,
                }
            }
            TypeKind::Qualified(next, inner) => match self.reach(module, path, next) {
                Some(Item::Module(target)) => {
                    self.resolve_member_ty(target, &format!("{path}.{}", next.name), inner)
                }
                Some(_) => {
                    self.error(TypeErrorKind::UnknownName(next.name.clone()), next.span);
                    Ty::Error
                }
                None => Ty::Error,
            },
            TypeKind::Pointer(_) => unreachable!("only names are qualified"),
        }
    }

    /// Resolves the type `name`, given type arguments `args` if any, written
    /// at `span`. `member` is the item `name` names in another module, which
    /// it is qualified by; otherwise `name` is resolved in the current one.
    fn resolve_named(
        &mut self,
        member: Option<Item>,
        name: &str,
        args: &Option<Vec<parse::Type>>,
        span: Span,
    ) -> Ty {
        let param = match member {
            Some(_) => None,
            None => self.type_params.iter().find(|(p, _)| p == name),
        };
        let arity = match (param, member) {
            (Some(_), _) => Some(Arity::Plain),
            (None, Some(item)) => self.item_arity(item),
            (None, None) => self.type_arity(name),
        };
        let Some(arity) = arity else {
            self.error(TypeErrorKind::UnknownType(name.to_string()), span);
            return Ty::Error;
        };
        if let Some(kind) = arity.check(name, args.as_ref().map(Vec::len)) {
            self.error(kind, span);
            return Ty::Error;
        }
        if let Some((_, param)) = param {
            return *param;
        }
        let args: Vec<_> = args
            .iter()
            .flatten()
            .map(|arg| self.resolve_ty(arg))
            .collect();
        // Built-in types win over items of the same name.
        let item = match member {
            Some(_) => member,
            None if is_builtin_type(name) => None,
            None => self.item(name),
        };
        if args.contains(&Ty::Error) {
            Ty::Error
        } else if let Some(Item::Struct(id)) = item {
            match args.is_empty() {
                true => Ty::Struct(id),
                false => self.instantiate(id, args, span),
            }
        } else if let Some(Item::Enum(id)) = item {
            Ty::Enum(id)
        } else if let Some(prim) = Prim::from_name(name) {
            Ty::Prim(prim)
        } else if name == EXTERNREF {
            Ty::ExternRef
        } else if name == TYPE {
            Ty::Type
        } else if name == TUPLE && args.is_empty() {
            Ty::Unit
        } else if name == TUPLE {
            self.tuple_of(args)
        } else if name == ARRAY {
            match args[0] {
                // Struct fields are checked once every struct is defined.
                elem if self.structs_defined && !self.storable(elem) => {
                    let kind = TypeErrorKind::NotStorable(self.ty_name(elem));
                    self.error(kind, span);
                    Ty::Error
                }
                elem => self.array_of(elem),
            }
        } else {
            unreachable!("`type_arity` knows every type")
        }
    }

    /// Whether `ty` can live in linear memory: it holds no `externref`.
    fn storable(&self, ty: Ty) -> bool {
        match ty {
            Ty::ExternRef => false,
            Ty::Enum(id) => self.storable(self.enum_ty(id)),
            Ty::Struct(_) | Ty::Tuple(_) => self
                .members(ty)
                .into_iter()
                .all(|member| self.storable(member)),
            // Checked in each instance, once it is known.
            Ty::Param(_) => true,
            Ty::Prim(_) | Ty::Ptr(_) | Ty::Array(_) | Ty::Type | Ty::Unit | Ty::Error => true,
        }
    }

    /// The types of a struct's fields, a tuple's elements, an array's `len`
    /// and `ptr`, or a `type`'s `size` and `align`, in order. Empty for any
    /// other type.
    fn members(&self, ty: Ty) -> Vec<Ty> {
        match ty {
            Ty::Struct(id) => self.structs[id.0 as usize]
                .fields
                .iter()
                .map(|field| field.ty)
                .collect(),
            Ty::Tuple(id) => self.tuples[id.0 as usize].clone(),
            Ty::Array(id) => vec![Ty::Prim(Prim::U32), self.arrays[id.0 as usize]],
            Ty::Type => vec![Ty::Prim(Prim::U32); TYPE_FIELDS.len()],
            _ => Vec::new(),
        }
    }

    /// The interned tuple type with elements `elems`.
    fn tuple_of(&mut self, elems: Vec<Ty>) -> Ty {
        let next = TupleId(self.tuples.len() as u32);
        let id = *self.tuple_ids.entry(elems.clone()).or_insert(next);
        if id == next {
            self.tuples.push(elems);
        }
        Ty::Tuple(id)
    }

    /// The interned type `*pointee`.
    fn ptr_to(&mut self, pointee: Ty) -> Ty {
        let next = PtrId(self.pointees.len() as u32);
        let id = *self.ptr_ids.entry(pointee).or_insert(next);
        if id == next {
            self.pointees.push(pointee);
        }
        Ty::Ptr(id)
    }

    fn pointee(&self, id: PtrId) -> Ty {
        self.pointees[id.0 as usize]
    }

    /// The interned type `[elem]`.
    fn array_of(&mut self, elem: Ty) -> Ty {
        let ptr = self.ptr_to(elem);
        let next = ArrayId(self.arrays.len() as u32);
        let id = *self.array_ids.entry(elem).or_insert(next);
        if id == next {
            self.arrays.push(ptr);
        }
        Ty::Array(id)
    }

    /// The types a pointer, tuple, or array type is made of: its pointee,
    /// elements, or element type. Empty for any other type.
    fn components(&self, ty: Ty) -> Vec<Ty> {
        match ty {
            Ty::Ptr(id) => vec![self.pointee(id)],
            Ty::Tuple(id) => self.tuples[id.0 as usize].clone(),
            Ty::Array(id) => vec![self.element(id)],
            _ => Vec::new(),
        }
    }

    /// The type shaped like `ty` but made of `components`, as
    /// [`Self::components`] takes it apart. Any other type is itself.
    fn rebuild(&mut self, ty: Ty, components: Vec<Ty>) -> Ty {
        match ty {
            Ty::Ptr(_) => self.ptr_to(components[0]),
            Ty::Tuple(_) => self.tuple_of(components),
            Ty::Array(_) => self.array_of(components[0]),
            _ => ty,
        }
    }

    fn element(&self, id: ArrayId) -> Ty {
        match self.arrays[id.0 as usize] {
            Ty::Ptr(ptr) => self.pointee(ptr),
            _ => unreachable!("an array's `ptr` is a pointer"),
        }
    }

    fn ty_name(&self, ty: Ty) -> String {
        match ty {
            Ty::Prim(prim) => prim.name().to_string(),
            Ty::Struct(id) => self.structs[id.0 as usize].name.clone(),
            Ty::Enum(id) => self.enums[id.0 as usize].name.clone(),
            Ty::Ptr(id) => format!("&{}", self.ty_name(self.pointee(id))),
            Ty::Array(id) => format!("{ARRAY}({})", self.ty_name(self.element(id))),
            Ty::Tuple(id) => {
                let elems: Vec<_> = self.tuples[id.0 as usize]
                    .iter()
                    .map(|elem| self.ty_name(*elem))
                    .collect();
                format!("{TUPLE}({})", elems.join(", "))
            }
            Ty::Param(id) => self.params[id.0 as usize].name.clone(),
            Ty::ExternRef => EXTERNREF.to_string(),
            Ty::Type => TYPE.to_string(),
            Ty::Unit => format!("{TUPLE}()"),
            Ty::Error => "{error}".to_string(),
        }
    }

    /// The scalar leaves of `ty` in field order, each named `prefix` followed
    /// by its `.field` path. Tuple elements are named by index.
    fn leaves(&self, ty: Ty, prefix: &str) -> Vec<(String, ValType)> {
        let mut out = Vec::new();
        self.push_leaves(ty, prefix.to_string(), &mut out);
        out
    }

    fn push_leaves(&self, ty: Ty, name: String, out: &mut Vec<(String, ValType)>) {
        match ty {
            Ty::Prim(prim) => out.push((name, prim.val_type())),
            Ty::Ptr(_) => out.push((name, ValType::I32)),
            Ty::ExternRef => out.push((name, ValType::ExternRef)),
            Ty::Enum(id) => self.push_leaves(self.enum_ty(id), name, out),
            Ty::Struct(id) => {
                for field in &self.structs[id.0 as usize].fields {
                    self.push_leaves(field.ty, format!("{name}.{}", field.name), out);
                }
            }
            Ty::Tuple(id) => {
                for (i, elem) in self.tuples[id.0 as usize].iter().enumerate() {
                    self.push_leaves(*elem, format!("{name}.{i}"), out);
                }
            }
            Ty::Array(_) | Ty::Type => {
                for (field, member) in builtin_fields(ty).iter().zip(self.members(ty)) {
                    self.push_leaves(member, format!("{name}.{field}"), out);
                }
            }
            Ty::Param(_) | Ty::Unit | Ty::Error => {}
        }
    }

    fn val_types(&self, ty: Ty) -> Vec<ValType> {
        self.leaves(ty, "").into_iter().map(|(_, vt)| vt).collect()
    }

    /// The primitive type of each scalar leaf of `ty`, or `None` for pointers
    /// and `externref`s.
    fn leaf_prims(&self, ty: Ty) -> Vec<Option<Prim>> {
        let mut out = Vec::new();
        self.push_leaf_prims(ty, &mut out);
        out
    }

    fn push_leaf_prims(&self, ty: Ty, out: &mut Vec<Option<Prim>>) {
        match ty {
            Ty::Prim(prim) => out.push(Some(prim)),
            Ty::Ptr(_) | Ty::ExternRef => out.push(None),
            Ty::Enum(id) => self.push_leaf_prims(self.enum_ty(id), out),
            Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_) | Ty::Type => {
                for member in self.members(ty) {
                    self.push_leaf_prims(member, out);
                }
            }
            Ty::Param(_) | Ty::Unit | Ty::Error => {}
        }
    }

    /// The type of `field` in `ty`, the range of `ty`'s leaves it covers, and
    /// its offset in memory. A tuple's fields are its indices. `None` after
    /// reporting an error.
    fn field(&mut self, ty: Ty, field: &parse::Ident) -> Option<(Ty, Range<usize>, u32)> {
        let index = match ty {
            Ty::Struct(id) => self.structs[id.0 as usize]
                .fields
                .iter()
                .position(|def| def.name == field.name),
            Ty::Tuple(id) => field
                .name
                .parse()
                .ok()
                .filter(|i| *i < self.tuples[id.0 as usize].len()),
            Ty::Array(_) | Ty::Type => builtin_fields(ty)
                .iter()
                .position(|name| *name == field.name),
            _ => None,
        };
        if let (Some(index), Ty::Struct(id)) = (index, ty) {
            let def = &self.structs[id.0 as usize];
            if !def.fields[index].is_pub && def.module != self.module {
                let kind = TypeErrorKind::PrivateField {
                    ty: def.name.clone(),
                    field: field.name.clone(),
                };
                self.error(kind, field.span);
                return None;
            }
        }
        if let Some(index) = index {
            let members = self.members(ty);
            let start = members[..index]
                .iter()
                .map(|member| self.val_types(*member).len())
                .sum::<usize>();
            let len = self.val_types(members[index]).len();
            let offset = self.aggregate_layout(ty).0[index];
            return Some((members[index], start..start + len, offset));
        }
        if ty != Ty::Error {
            let kind = TypeErrorKind::NoField {
                ty: self.ty_name(ty),
                field: field.name.clone(),
            };
            self.error(kind, field.span);
        }
        None
    }

    /// `value as to`, where `value` has type `from`, and its type: `to`, or
    /// the error type for an enum whose values' type failed to resolve.
    /// `None` if the cast isn't allowed.
    fn cast_value(&self, from: Ty, to: Ty, value: Value) -> Option<(Ty, Value)> {
        match (from, to) {
            // Any type casts to itself.
            (from, to) if from == to => Some((to, value)),
            // Already reported.
            (Ty::Error, _) => Some((Ty::Error, Value::default())),
            (Ty::Prim(from), Ty::Prim(to)) if convertible(from, to) => Some((
                Ty::Prim(to),
                map1(value, to.val_type(), |e| convert(from, to, e)),
            )),
            (Ty::Ptr(_) | Ty::Prim(Prim::U32 | Prim::I32), Ty::Ptr(_))
            | (Ty::Ptr(_), Ty::Prim(Prim::U32 | Prim::I32)) => Some((to, value)),
            // An enum casts to whatever the type of its values does.
            (Ty::Enum(id), to) => self.cast_value(self.enum_ty(id), to, value),
            _ => None,
        }
    }

    /// The names `pattern` binds when it takes apart a value of type `ty`, in
    /// source order. A pattern that doesn't fit `ty` is reported, and its
    /// names get the error type.
    fn destructure<'p>(&mut self, pattern: &'p Pattern, ty: Ty) -> Vec<Bound<'p>> {
        let mut out = Vec::new();
        self.push_bounds(pattern, ty, 0, &mut out);
        out
    }

    /// Pushes the names `pattern` binds, given that the value it matches
    /// starts at leaf `start`.
    fn push_bounds<'p>(
        &mut self,
        pattern: &'p Pattern,
        ty: Ty,
        start: usize,
        out: &mut Vec<Bound<'p>>,
    ) {
        match &pattern.kind {
            PatternKind::Name(name) => out.push(Bound {
                name,
                span: pattern.span,
                ty,
                leaves: start..start + self.val_types(ty).len(),
            }),
            PatternKind::Discard => {}
            PatternKind::Tuple(elems) => {
                let members = match ty {
                    Ty::Tuple(id) if self.tuples[id.0 as usize].len() == elems.len() => {
                        self.members(ty)
                    }
                    Ty::Unit if elems.is_empty() => Vec::new(),
                    _ => {
                        if ty != Ty::Error {
                            let kind = TypeErrorKind::Mismatch {
                                expected: format!("{TUPLE}({})", vec!["_"; elems.len()].join(", ")),
                                found: self.ty_name(ty),
                            };
                            self.error(kind, pattern.span);
                        }
                        vec![Ty::Error; elems.len()]
                    }
                };
                let mut start = start;
                for (elem, member) in elems.iter().zip(members) {
                    self.push_bounds(elem, member, start, out);
                    start += self.val_types(member).len();
                }
            }
        }
    }

    /// Size and alignment of `ty` in memory.
    fn layout(&self, ty: Ty) -> (u32, u32) {
        match ty {
            Ty::Prim(prim) => (prim.size(), prim.size()),
            Ty::Ptr(_) => (4, 4),
            Ty::Enum(id) => self.layout(self.enum_ty(id)),
            Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_) | Ty::Type => {
                let (_, size, align) = self.aggregate_layout(ty);
                (size, align)
            }
            // Never in memory, but a struct holding one still has a layout
            // that `field` asks for.
            Ty::ExternRef | Ty::Param(_) | Ty::Unit | Ty::Error => (0, 1),
        }
    }

    /// Member offsets, size, and alignment of a struct, tuple, array, or `type`, laid
    /// out as C would: members in order, each at a multiple of its alignment,
    /// and the whole padded to a multiple of the largest.
    fn aggregate_layout(&self, ty: Ty) -> (Vec<u32>, u32, u32) {
        let (mut size, mut align) = (0u32, 1);
        let mut offsets = Vec::new();
        for member in self.members(ty) {
            let (member_size, member_align) = self.layout(member);
            size = size.next_multiple_of(member_align);
            offsets.push(size);
            size += member_size;
            align = align.max(member_align);
        }
        (offsets, size.next_multiple_of(align), align)
    }

    /// Where each scalar leaf of `ty` lives in memory, in leaf order.
    fn cells(&self, ty: Ty) -> Vec<Cell> {
        let mut out = Vec::new();
        self.push_cells(ty, 0, &mut out);
        out
    }

    fn push_cells(&self, ty: Ty, offset: u32, out: &mut Vec<Cell>) {
        match ty {
            Ty::Prim(prim) => out.push(Cell {
                offset,
                ty: prim.val_type(),
                load: prim.load(),
                store: prim.store(),
                bool: prim == Prim::Bool,
            }),
            Ty::Ptr(_) => out.push(Cell {
                offset,
                ty: ValType::I32,
                load: LoadOp::Load,
                store: StoreOp::Store,
                bool: false,
            }),
            Ty::Enum(id) => self.push_cells(self.enum_ty(id), offset, out),
            Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_) | Ty::Type => {
                let offsets = self.aggregate_layout(ty).0;
                for (member, member_offset) in self.members(ty).into_iter().zip(offsets) {
                    self.push_cells(member, offset + member_offset, out);
                }
            }
            Ty::ExternRef => unreachable!("`externref` has no pointer type"),
            Ty::Param(_) | Ty::Unit | Ty::Error => {}
        }
    }

    /// Places `bytes`, which hold `len` elements, in memory at the next
    /// multiple of `align`, or right at the end if there are none. Returns the
    /// array of them.
    fn push_data(&mut self, bytes: Vec<u8>, align: u32, len: u32) -> Value {
        let mut offset = self.data_end;
        if !bytes.is_empty() {
            offset = offset.next_multiple_of(align);
            self.data_end = offset + bytes.len() as u32;
            self.data.push(ir::Data { offset, bytes });
        }
        let consts = [len, offset].map(|x| (ValType::I32, Expr::Const(Const::I32(x as i32))));
        Value {
            pre: Vec::new(),
            scalars: consts.to_vec(),
        }
    }

    /// Evaluates each scalar of a lowered constant at compile time, reporting
    /// at `span` if it isn't constant. Stops at the first that can't be.
    fn fold_value(&mut self, value: &Value, span: Span) -> Vec<Const> {
        if !value.pre.is_empty() {
            self.error(TypeErrorKind::NotConstant, span);
            return Vec::new();
        }
        let mut consts = Vec::new();
        for (_, scalar) in &value.scalars {
            match self.fold(scalar) {
                Ok(c) => consts.push(c),
                Err(fold) => {
                    let kind = match fold {
                        Fold::NotConstant => TypeErrorKind::NotConstant,
                        Fold::Trap => TypeErrorKind::ConstTrap,
                    };
                    self.error(kind, span);
                    break;
                }
            }
        }
        consts
    }

    /// Evaluates a lowered global initializer at compile time.
    fn fold(&self, expr: &Expr) -> Result<Const, Fold> {
        match expr {
            Expr::Const(c) => Ok(*c),
            Expr::Global(id) => {
                let global = &self.ir_globals[id.0 as usize];
                if global.mutable {
                    Err(Fold::NotConstant)
                } else {
                    Ok(global.init)
                }
            }
            Expr::Unary(_, op, x) => fold_unary(*op, self.fold(x)?),
            Expr::Binary(_, op, a, b) => fold_binary(*op, self.fold(a)?, self.fold(b)?),
            Expr::If {
                cond,
                then_expr,
                else_expr,
                ..
            } => match self.fold(cond)? {
                Const::I32(0) => self.fold(else_expr),
                _ => self.fold(then_expr),
            },
            Expr::Local(_) | Expr::Call(..) | Expr::Load { .. } | Expr::Seq(..) => {
                Err(Fold::NotConstant)
            }
        }
    }
}

impl<'c> Body<'c> {
    fn new(ck: &'c mut Checker, ret: Ty) -> Self {
        Self {
            ck,
            ret,
            locals: Vec::new(),
            scopes: vec![HashMap::new()],
            labels: Vec::new(),
            global: false,
        }
    }

    fn error(&mut self, kind: TypeErrorKind, span: Span) {
        self.ck.error(kind, span);
    }

    /// Reports a mismatch unless `found` is `want` or either is an error.
    fn expect(&mut self, found: Ty, want: Ty, span: Span) {
        if found != want && found != Ty::Error && want != Ty::Error {
            let kind = TypeErrorKind::Mismatch {
                expected: self.ck.ty_name(want),
                found: self.ck.ty_name(found),
            };
            self.error(kind, span);
        }
    }

    /// Allocates one local per scalar leaf of `ty`.
    fn alloc(&mut self, name: &str, ty: Ty) -> Vec<LocalId> {
        self.ck
            .leaves(ty, name)
            .into_iter()
            .map(|(name, ty)| self.push_local(name, ty))
            .collect()
    }

    fn temp(&mut self, ty: ValType) -> LocalId {
        self.push_local("tmp".to_string(), ty)
    }

    fn push_local(&mut self, name: String, ty: ValType) -> LocalId {
        self.locals.push(ir::Local { name, ty });
        LocalId(self.locals.len() as u32 - 1)
    }

    fn bind(&mut self, name: &str, ty: Ty, mutable: bool, slots: Vec<LocalId>) {
        let var = Var { ty, mutable, slots };
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name.to_string(), var);
    }

    fn lookup(&self, name: &str) -> Option<&Var> {
        self.scopes.iter().rev().find_map(|scope| scope.get(name))
    }

    fn block(&mut self, block: &parse::Block) -> Vec<Stmt> {
        self.scopes.push(HashMap::new());
        let mut out = Vec::new();
        for stmt in block {
            self.stmt(stmt, &mut out);
        }
        self.scopes.pop();
        out
    }

    /// A block nested in a wasm label.
    fn labelled(&mut self, label: Label, block: &parse::Block) -> Vec<Stmt> {
        self.labels.push(label);
        let out = self.block(block);
        self.labels.pop();
        out
    }

    fn stmt(&mut self, stmt: &parse::Stmt, out: &mut Vec<Stmt>) {
        match &stmt.kind {
            StmtKind::Binding(binding) => {
                let (ty, value) = self.binding_value(binding);
                let bounds = self.ck.destructure(&binding.pattern, ty);
                // The local each leaf of the value goes to, if it's kept.
                let mut dests = vec![None; self.ck.val_types(ty).len()];
                let mut vars = Vec::new();
                for (i, bound) in bounds.iter().enumerate() {
                    if bounds[..i].iter().any(|prev| prev.name == bound.name) {
                        let kind = TypeErrorKind::DuplicateBinding(bound.name.to_string());
                        self.error(kind, bound.span);
                        continue;
                    }
                    let slots = self.alloc(bound.name, bound.ty);
                    for (leaf, slot) in bound.leaves.clone().zip(&slots) {
                        dests[leaf] = Some(*slot);
                    }
                    vars.push((bound.name, bound.ty, slots));
                }
                out.extend(value.pre);
                for (dest, (_, scalar)) in dests.into_iter().zip(value.scalars) {
                    match dest {
                        Some(slot) => out.push(Stmt::SetLocal(slot, scalar)),
                        None if !is_pure(&scalar) => out.push(Stmt::Drop(scalar)),
                        None => {}
                    }
                }
                let mutable = binding.mutability == Mutability::Var;
                for (name, ty, slots) in vars {
                    self.bind(name, ty, mutable, slots);
                }
            }
            StmtKind::Assign { target, op, value } => {
                let Some(mut place) = self.place(target) else {
                    self.expr(value, None);
                    return;
                };
                out.append(&mut place.pre);
                if !place.mutable {
                    self.error(
                        TypeErrorKind::ImmutableAssign(place.name.clone()),
                        target.span,
                    );
                }
                let value = match op {
                    None => self.check(value, place.ty),
                    Some(op) => {
                        let current = self.read_place(&place);
                        let rhs = self.check(value, place.ty);
                        self.binary_values(*op, place.ty, current, rhs, stmt.span).1
                    }
                };
                self.assign(&place, value, out);
            }
            StmtKind::Expr(expr) => {
                let value = self.expr(expr, None).1;
                out.extend(value.pre);
                for (_, scalar) in value.scalars {
                    if !is_pure(&scalar) {
                        out.push(Stmt::Drop(scalar));
                    }
                }
            }
            StmtKind::Return(value) => {
                let value = match value {
                    Some(value) => self.check(value, self.ret),
                    None => {
                        self.expect(Ty::Unit, self.ret, stmt.span);
                        Value::default()
                    }
                };
                out.extend(value.pre);
                out.push(Stmt::Return(exprs(value.scalars)));
            }
            StmtKind::If {
                cond,
                then_body,
                else_body,
            } => {
                let (pre, cond) = split1(self.check(cond, Ty::Prim(Prim::Bool)));
                out.extend(pre);
                let then_body = self.labelled(Label::Other, then_body);
                let else_body = match else_body {
                    Some(else_body) => self.labelled(Label::Other, else_body),
                    None => Vec::new(),
                };
                out.push(Stmt::If {
                    cond,
                    then_body,
                    else_body,
                });
            }
            StmtKind::While { cond, body } => {
                let infinite = matches!(cond.kind, ExprKind::Bool(true));
                let (mut inner, cond) = split1(self.check(cond, Ty::Prim(Prim::Bool)));
                if !infinite {
                    let exit = Expr::Unary(ValType::I32, IrUnOp::Eqz, Box::new(cond));
                    inner.push(Stmt::BrIf(1, exit));
                }
                out.push(self.loop_stmt(inner, body));
            }
            StmtKind::For { var, iter, body } => self.for_loop(var, iter, body, out),
            StmtKind::Break => match self.depth(Label::Break) {
                Some(depth) => out.push(Stmt::Br(depth)),
                None => self.error(TypeErrorKind::BreakOutsideLoop, stmt.span),
            },
            StmtKind::Continue => match self.depth(Label::Continue) {
                Some(depth) => out.push(Stmt::Br(depth)),
                None => self.error(TypeErrorKind::ContinueOutsideLoop, stmt.span),
            },
            StmtKind::Pass => {}
        }
    }

    /// `for var in iter`, which copies each element of the array `iter`, or
    /// each member of the enum `iter` names, to `var` in turn. The array's
    /// `len` and `ptr` are read once, before the first iteration.
    fn for_loop(
        &mut self,
        var: &Ident,
        iter: &parse::Expr,
        body: &parse::Block,
        out: &mut Vec<Stmt>,
    ) {
        if let Some(id) = self.enum_name(iter) {
            out.push(self.unrolled_loop(id, var, body));
            return;
        }
        let (ty, value) = self.expr(iter, None);
        let elem = match ty {
            Ty::Array(id) => self.ck.element(id),
            _ => self.invalid_operand("for", ty, iter.span).0,
        };
        let (len, ptr, index) = (
            self.temp(ValType::I32),
            self.temp(ValType::I32),
            self.temp(ValType::I32),
        );
        out.extend(value.pre);
        let mut scalars = exprs(value.scalars).into_iter();
        for dest in [len, ptr] {
            let scalar = scalars.next().unwrap_or(Expr::Const(Const::I32(0)));
            out.push(Stmt::SetLocal(dest, scalar));
        }
        out.push(Stmt::SetLocal(index, Expr::Const(Const::I32(0))));
        let i = Expr::Local(index);
        let done = binary(ValType::I32, IrBinOp::GeU, i.clone(), Expr::Local(len));
        let mut inner = vec![Stmt::BrIf(1, done)];
        let addr = element_addr(Expr::Local(ptr), i.clone(), self.ck.layout(elem).0);
        let element = self.load(scalar(ValType::I32, addr), 0, elem);
        let slots = self.alloc(&var.name, elem);
        inner.extend(element.pre);
        for (slot, (_, scalar)) in slots.iter().zip(element.scalars) {
            inner.push(Stmt::SetLocal(*slot, scalar));
        }
        // Advanced before the body, so `continue` moves on too.
        let next = binary(ValType::I32, IrBinOp::Add, i, Expr::Const(Const::I32(1)));
        inner.push(Stmt::SetLocal(index, next));
        self.scopes.push(HashMap::new());
        self.bind(&var.name, elem, false, slots);
        let stmt = self.loop_stmt(inner, body);
        self.scopes.pop();
        out.push(stmt);
    }

    /// A loop that runs `head`, which may leave with `br 1`, then `body`, and
    /// then repeats.
    fn loop_stmt(&mut self, mut head: Vec<Stmt>, body: &parse::Block) -> Stmt {
        self.labels.push(Label::Break);
        head.extend(self.labelled(Label::Continue, body));
        self.labels.pop();
        head.push(Stmt::Br(0));
        Stmt::Block(vec![Stmt::Loop(head)])
    }

    /// Branch depth of the innermost `label`.
    fn depth(&self, label: Label) -> Option<u32> {
        let depth = self.labels.iter().rev().position(|l| *l == label)?;
        Some(depth as u32)
    }

    /// Checks the value of a `let` or `var` against its annotation, if any.
    fn binding_value(&mut self, binding: &parse::Binding) -> (Ty, Value) {
        match &binding.ty {
            Some(ty) => {
                let ty = self.ck.resolve_ty(ty);
                (ty, self.check(&binding.value, ty))
            }
            None => self.expr(&binding.value, None),
        }
    }

    /// Resolves an assignment target. `None` after reporting an error.
    fn place(&mut self, target: &parse::Expr) -> Option<Place> {
        match &target.kind {
            ExprKind::Name(name) => {
                if let Some(var) = self.lookup(name) {
                    return Some(Place {
                        name: name.clone(),
                        ty: var.ty,
                        mutable: var.mutable,
                        pre: Vec::new(),
                        slots: Slots::Local(var.slots.clone()),
                    });
                }
                match self.ck.item(name) {
                    Some(item) => self.item_place(item, name, target.span),
                    None if is_builtin_type(name) || self.ck.type_param(name).is_some() => {
                        self.error(TypeErrorKind::NotAssignable, target.span);
                        None
                    }
                    None => {
                        self.error(TypeErrorKind::UnknownName(name.clone()), target.span);
                        None
                    }
                }
            }
            ExprKind::Field(inner, field) if self.names_module(inner).is_some() => {
                let item = self.member(inner, field)?;
                self.item_place(item, &field.name, target.span)
            }
            ExprKind::Field(inner, field) => {
                let mut place = match &inner.kind {
                    ExprKind::Name(_)
                    | ExprKind::Field(..)
                    | ExprKind::Deref(_)
                    | ExprKind::Index(..) => self.place(inner)?,
                    _ => match self.expr(inner, None) {
                        (Ty::Ptr(id), ptr) => self.deref_place(ptr, self.ck.pointee(id)),
                        (Ty::Error, _) => return None,
                        _ => {
                            self.error(TypeErrorKind::NotAssignable, target.span);
                            return None;
                        }
                    },
                };
                // Fields are reached through any number of pointers.
                while let Ty::Ptr(id) = place.ty {
                    let ptr = self.read_place(&place);
                    let mut deref = self.deref_place(ptr, self.ck.pointee(id));
                    place.pre.append(&mut deref.pre);
                    place = Place {
                        pre: place.pre,
                        ..deref
                    };
                }
                let (ty, range, field_offset) = self.ck.field(place.ty, field)?;
                let slots = match place.slots {
                    Slots::Local(slots) => Slots::Local(slots[range].to_vec()),
                    Slots::Global(slots) => Slots::Global(slots[range].to_vec()),
                    Slots::Memory { addr, offset } => Slots::Memory {
                        addr,
                        offset: offset + field_offset,
                    },
                };
                Some(Place { ty, slots, ..place })
            }
            ExprKind::Deref(inner) => match self.expr(inner, None) {
                (Ty::Ptr(id), ptr) => Some(self.deref_place(ptr, self.ck.pointee(id))),
                (ty, _) => {
                    self.invalid_operand(".*", ty, target.span);
                    None
                }
            },
            ExprKind::Index(array, index) => self.index_place(array, index, target.span),
            _ => {
                self.error(TypeErrorKind::NotAssignable, target.span);
                None
            }
        }
    }

    /// The global `item`, named `name` at `span`, as a place. `None` after
    /// reporting an error.
    fn item_place(&mut self, item: Item, name: &str, span: Span) -> Option<Place> {
        let Item::Global(index) = item else {
            self.error(TypeErrorKind::NotAssignable, span);
            return None;
        };
        let global = self.ck.globals[index].as_ref()?;
        Some(Place {
            name: name.to_string(),
            ty: global.ty,
            mutable: global.mutable,
            pre: Vec::new(),
            slots: Slots::Global(global.slots.clone()),
        })
    }

    /// The element `array[index]`, as a place whose `pre` traps unless
    /// `index < array.len`. `None` after reporting an error.
    fn index_place(
        &mut self,
        array: &parse::Expr,
        index: &parse::Expr,
        span: Span,
    ) -> Option<Place> {
        let (ty, array) = self.expr(array, None);
        let index = self.check(index, Ty::Prim(Prim::U32));
        let Ty::Array(id) = ty else {
            self.invalid_operand("[]", ty, span);
            return None;
        };
        let elem = self.ck.element(id);
        let mut value = self.seq(vec![array, index]);
        // The bounds check reads the index again, and everything is read
        // after the prelude.
        self.spill(&mut value, |e| matches!(e, Expr::Local(_) | Expr::Const(_)));
        // Only a mistyped index has other than one scalar.
        let [len, ptr, index] = <[_; 3]>::try_from(exprs(value.scalars)).ok()?;
        let mut pre = value.pre;
        pre.push(Stmt::If {
            cond: binary(ValType::I32, IrBinOp::GeU, index.clone(), len),
            then_body: vec![Stmt::Unreachable],
            else_body: Vec::new(),
        });
        let tmp = self.temp(ValType::I32);
        let addr = element_addr(ptr, index, self.ck.layout(elem).0);
        pre.push(Stmt::SetLocal(tmp, addr));
        Some(Place {
            name: String::new(),
            ty: elem,
            mutable: true,
            pre,
            slots: Slots::Memory {
                addr: Expr::Local(tmp),
                offset: 0,
            },
        })
    }

    /// The memory a pointer points to, as a place.
    fn deref_place(&mut self, ptr: Value, pointee: Ty) -> Place {
        let (pre, addr) = self.reusable_addr(ptr);
        Place {
            name: String::new(),
            ty: pointee,
            mutable: true,
            pre,
            slots: Slots::Memory { addr, offset: 0 },
        }
    }

    /// Splits a pointer value into its prelude and an address that can be
    /// evaluated more than once, moving it into a temporary if needed.
    fn reusable_addr(&mut self, ptr: Value) -> (Vec<Stmt>, Expr) {
        let (mut pre, addr) = split1(ptr);
        if matches!(addr, Expr::Local(_) | Expr::Const(_)) {
            return (pre, addr);
        }
        let tmp = self.temp(ValType::I32);
        pre.push(Stmt::SetLocal(tmp, addr));
        (pre, Expr::Local(tmp))
    }

    /// Reads a place, not including its `pre`.
    fn read_place(&mut self, place: &Place) -> Value {
        let reads = match &place.slots {
            Slots::Local(slots) => slots.iter().map(|l| Expr::Local(*l)).collect(),
            Slots::Global(slots) => slots.iter().map(|g| Expr::Global(*g)).collect(),
            Slots::Memory { addr, offset } => {
                let ptr = scalar(ValType::I32, addr.clone());
                return self.load(ptr, *offset, place.ty);
            }
        };
        self.scalars(place.ty, reads)
    }

    fn assign(&mut self, place: &Place, mut value: Value, out: &mut Vec<Stmt>) {
        // Every scalar is read before any slot is written, so `p = Point(x:
        // p.y, y: p.x)` swaps. Stores can't change locals.
        if value.scalars.len() > 1 {
            match place.slots {
                Slots::Memory { .. } => self.spill(&mut value, is_stable),
                _ => self.spill(&mut value, |e| matches!(e, Expr::Const(_))),
            }
        }
        out.extend(value.pre);
        let scalars = exprs(value.scalars);
        match &place.slots {
            Slots::Local(slots) => {
                for (slot, scalar) in slots.iter().zip(scalars) {
                    out.push(Stmt::SetLocal(*slot, scalar));
                }
            }
            Slots::Global(slots) => {
                for (slot, scalar) in slots.iter().zip(scalars) {
                    out.push(Stmt::SetGlobal(*slot, scalar));
                }
            }
            Slots::Memory { addr, offset } => {
                for (cell, scalar) in self.ck.cells(place.ty).into_iter().zip(scalars) {
                    out.push(Stmt::Store {
                        ty: cell.ty,
                        op: cell.store,
                        offset: offset + cell.offset,
                        addr: addr.clone(),
                        value: scalar,
                    });
                }
            }
        }
    }

    /// Checks `expr` against `want`, using it to type literals.
    fn check(&mut self, expr: &parse::Expr, want: Ty) -> Value {
        let (ty, value) = self.expr(expr, Some(want));
        self.expect(ty, want, expr.span);
        value
    }

    /// Infers the type of `expr` and lowers it. `expected` only guides the
    /// types of literals; the caller checks the result.
    fn expr(&mut self, expr: &parse::Expr, expected: Option<Ty>) -> (Ty, Value) {
        match &expr.kind {
            ExprKind::Int(n) => self.int_literal(*n as i128, expected, expr.span),
            ExprKind::Float(x) => float_literal(*x, expected),
            ExprKind::Bool(b) => (
                Ty::Prim(Prim::Bool),
                scalar(ValType::I32, Expr::Const(Const::I32(*b as i32))),
            ),
            ExprKind::Unit => (Ty::Unit, Value::default()),
            ExprKind::Str(_) | ExprKind::List(_) if !self.global => {
                self.error(TypeErrorKind::LiteralOutsideGlobal, expr.span);
                (Ty::Error, Value::default())
            }
            ExprKind::Str(s) => self.string(s),
            ExprKind::List(items) => self.list(items, expected, expr.span),
            ExprKind::Index(..) => match self.place(expr) {
                Some(place) => {
                    let value = self.read_place(&place);
                    let mut pre = place.pre;
                    pre.extend(value.pre);
                    let scalars = value.scalars;
                    (place.ty, Value { pre, scalars })
                }
                None => (Ty::Error, Value::default()),
            },
            ExprKind::Name(_) | ExprKind::Field(..) | ExprKind::AddrOf(_)
                if self.is_type_expr(expr) =>
            {
                let ty = self.expr_type(expr);
                self.type_value(ty, expr.span)
            }
            ExprKind::Name(name) => self.name(name, expr.span),
            ExprKind::Tuple(elems) => self.tuple(elems, expected),
            ExprKind::Unary(op, operand) => self.unary(*op, operand, expected, expr.span),
            ExprKind::Binary(op, lhs, rhs) => self.binary(*op, lhs, rhs, expected, expr.span),
            ExprKind::Call(callee, args) => self.call(callee, args, expr.span),
            ExprKind::Field(inner, field) if self.names_module(inner).is_some() => {
                match self.member(inner, field) {
                    Some(item) => self.item_value(item, &field.name, field.span),
                    None => (Ty::Error, Value::default()),
                }
            }
            ExprKind::Field(inner, field) => {
                if let Some(member) = self
                    .enum_name(inner)
                    .and_then(|id| self.enum_member(id, field))
                {
                    return member;
                }
                let (mut ty, mut value) = self.expr(inner, None);
                // Fields are reached through any number of pointers.
                while let Ty::Ptr(id) = ty {
                    let pointee = self.ck.pointee(id);
                    if !matches!(pointee, Ty::Ptr(_)) {
                        return match self.ck.field(pointee, field) {
                            Some((ty, _, offset)) => (ty, self.load(value, offset, ty)),
                            None => (Ty::Error, Value::default()),
                        };
                    }
                    value = self.load(value, 0, pointee);
                    ty = pointee;
                }
                match self.ck.field(ty, field) {
                    Some((ty, range, _)) => (ty, self.project(value, range)),
                    None => (Ty::Error, Value::default()),
                }
            }
            ExprKind::Deref(inner) => {
                let (ty, value) = self.expr(inner, None);
                match ty {
                    Ty::Ptr(id) => {
                        let pointee = self.ck.pointee(id);
                        (pointee, self.load(value, 0, pointee))
                    }
                    _ => self.invalid_operand(".*", ty, expr.span),
                }
            }
            ExprKind::Cast(inner, ty) => self.cast(inner, ty, expr.span),
            ExprKind::AddrOf(inner) => self.addr_of(inner, expr.span),
        }
    }

    /// A tuple literal, whose elements are typed by those of `expected` and
    /// evaluated in order.
    fn tuple(&mut self, elems: &[parse::Expr], expected: Option<Ty>) -> (Ty, Value) {
        let expected = match expected {
            Some(Ty::Tuple(id)) => self.ck.tuples[id.0 as usize].clone(),
            _ => Vec::new(),
        };
        let mut tys = Vec::new();
        let mut values = Vec::new();
        for (i, elem) in elems.iter().enumerate() {
            let (ty, value) = self.expr(elem, expected.get(i).copied());
            tys.push(ty);
            values.push(value);
        }
        if tys.contains(&Ty::Error) {
            return (Ty::Error, Value::default());
        }
        (self.ck.tuple_of(tys), self.seq(values))
    }

    /// A string literal: an array of its UTF-8 bytes.
    fn string(&mut self, s: &str) -> (Ty, Value) {
        let ty = self.ck.array_of(Ty::Prim(Prim::U8));
        (
            ty,
            self.ck.push_data(s.as_bytes().to_vec(), 1, s.len() as u32),
        )
    }

    /// An array literal, whose elements are typed like those of `expected`,
    /// or else like the first element, and must be constant. Its elements are
    /// placed in memory after any literals within them.
    fn list(&mut self, items: &[parse::Expr], expected: Option<Ty>, span: Span) -> (Ty, Value) {
        let mut elem = match expected {
            Some(Ty::Array(id)) => Some(self.ck.element(id)),
            // An array type that failed to resolve, already reported.
            Some(Ty::Error) => Some(Ty::Error),
            _ => None,
        };
        let mut consts = Vec::new();
        for item in items {
            let (ty, value) = self.expr(item, elem);
            let want = *elem.get_or_insert(ty);
            self.expect(ty, want, item.span);
            let item_consts = self.ck.fold_value(&value, item.span);
            // A mistyped element's scalars don't fit the cells.
            consts.push(if ty == want { item_consts } else { Vec::new() });
        }
        let Some(elem) = elem else {
            self.error(TypeErrorKind::UntypedEmptyArray, span);
            return (Ty::Error, Value::default());
        };
        // Nothing holding an `externref` is constant, so that's reported.
        if elem == Ty::Error || !self.ck.storable(elem) {
            return (Ty::Error, Value::default());
        }
        let (size, align) = self.ck.layout(elem);
        let cells = self.ck.cells(elem);
        let mut bytes = vec![0; size as usize * items.len()];
        for (i, consts) in consts.iter().enumerate() {
            let start = i * size as usize;
            for (cell, c) in cells.iter().zip(consts) {
                write_const(&mut bytes[start + cell.offset as usize..], cell.store, *c);
            }
        }
        let value = self.ck.push_data(bytes, align, items.len() as u32);
        (self.ck.array_of(elem), value)
    }

    /// An integer literal, typed by `expected` and defaulting to `i32`. Where
    /// a pointer is expected, it is an address.
    fn int_literal(&mut self, n: i128, expected: Option<Ty>, span: Span) -> (Ty, Value) {
        if let Some(ptr @ Ty::Ptr(_)) = expected {
            let (min, max) = Prim::U32.range();
            if n < min || n > max {
                self.error(TypeErrorKind::IntOutOfRange(self.ck.ty_name(ptr)), span);
            }
            return (ptr, scalar(ValType::I32, Expr::Const(Const::I32(n as i32))));
        }
        let prim = match expected {
            Some(Ty::Prim(prim)) if prim.is_numeric() => prim,
            _ => Prim::I32,
        };
        if prim.is_float() {
            return float_literal(n as f64, expected);
        }
        let (min, max) = prim.range();
        if n < min || n > max {
            self.error(TypeErrorKind::IntOutOfRange(prim.name().to_string()), span);
        }
        let value = match prim.val_type() {
            ValType::I64 => Const::I64(n as i64),
            _ => Const::I32(n as i32),
        };
        (Ty::Prim(prim), scalar(prim.val_type(), Expr::Const(value)))
    }

    fn name(&mut self, name: &str, span: Span) -> (Ty, Value) {
        if let Some(var) = self.lookup(name) {
            let ty = var.ty;
            let reads = var.slots.iter().map(|l| Expr::Local(*l)).collect();
            return (ty, self.scalars(ty, reads));
        }
        match self.ck.item(name) {
            Some(item) => self.item_value(item, name, span),
            None => {
                self.error(TypeErrorKind::UnknownName(name.to_string()), span);
                (Ty::Error, Value::default())
            }
        }
    }

    /// The value of `item`, named `name` at `span`.
    fn item_value(&mut self, item: Item, name: &str, span: Span) -> (Ty, Value) {
        match item {
            Item::Global(index) => match &self.ck.globals[index] {
                Some(global) => {
                    let ty = global.ty;
                    let reads = global.slots.iter().map(|g| Expr::Global(*g)).collect();
                    (ty, self.scalars(ty, reads))
                }
                // Only reachable from an earlier global's initializer.
                None => {
                    self.error(TypeErrorKind::NotConstant, span);
                    (Ty::Error, Value::default())
                }
            },
            // Struct and enum names are types, which `expr` makes values.
            Item::Func(_)
            | Item::GenericFn(_)
            | Item::Struct(_)
            | Item::Enum(_)
            | Item::Module(_) => {
                self.error(TypeErrorKind::NotAValue(name.to_string()), span);
                (Ty::Error, Value::default())
            }
        }
    }

    /// The item `expr` names, without reporting anything: a name that no
    /// variable shadows, or `module.name`, an item another module lets this
    /// one see.
    fn named(&self, expr: &parse::Expr) -> Option<Item> {
        match &expr.kind {
            ExprKind::Name(name) if self.lookup(name).is_none() => self.ck.item(name),
            ExprKind::Field(inner, field) => match self.named(inner)? {
                Item::Module(module) => self.ck.member_of(module, &field.name).ok(),
                _ => None,
            },
            _ => None,
        }
    }

    /// The module `expr` names, as [`Self::named`] finds it.
    fn names_module(&self, expr: &parse::Expr) -> Option<FileId> {
        match self.named(expr)? {
            Item::Module(module) => Some(module),
            _ => None,
        }
    }

    /// The item `field` names in the module `module` names. `None` after
    /// reporting why it can't be reached.
    fn member(&mut self, module: &parse::Expr, field: &Ident) -> Option<Item> {
        let id = self.names_module(module).unwrap();
        self.ck.reach(id, &path_text(module), field)
    }

    /// Whether `expr` is a type written where a value belongs: the name of a
    /// type that no variable or item shadows, a type given type arguments,
    /// or a pointer to one of those.
    fn is_type_expr(&self, expr: &parse::Expr) -> bool {
        match &expr.kind {
            ExprKind::Name(name) if self.lookup(name).is_none() => match self.ck.item(name) {
                Some(item) => matches!(item, Item::Struct(_) | Item::Enum(_)),
                None => is_builtin_type(name) || self.ck.type_param(name).is_some(),
            },
            ExprKind::Field(..) => {
                matches!(self.named(expr), Some(Item::Struct(_) | Item::Enum(_)))
            }
            ExprKind::Call(callee, args) => self.names_type(callee, args),
            ExprKind::AddrOf(pointee) => self.is_type_expr(pointee),
            _ => false,
        }
    }

    /// The `type` value describing `ty`, which must be storable to have a
    /// size in memory.
    fn type_value(&mut self, ty: Ty, span: Span) -> (Ty, Value) {
        if ty == Ty::Error {
            return (Ty::Error, Value::default());
        }
        if !self.ck.storable(ty) {
            self.error(TypeErrorKind::NotStorable(self.ck.ty_name(ty)), span);
            return (Ty::Error, Value::default());
        }
        let (size, align) = self.ck.layout(ty);
        let consts = [size, align].map(|x| (ValType::I32, Expr::Const(Const::I32(x as i32))));
        let value = Value {
            pre: Vec::new(),
            scalars: consts.to_vec(),
        };
        (Ty::Type, value)
    }

    /// Pairs `exprs`, one per leaf of `ty`, with their wasm types.
    fn scalars(&self, ty: Ty, exprs: Vec<Expr>) -> Value {
        Value {
            pre: Vec::new(),
            scalars: self.ck.val_types(ty).into_iter().zip(exprs).collect(),
        }
    }

    fn unary(
        &mut self,
        op: UnaryOp,
        operand: &parse::Expr,
        expected: Option<Ty>,
        span: Span,
    ) -> (Ty, Value) {
        match (op, &operand.kind) {
            (UnaryOp::Neg, ExprKind::Int(n)) => {
                match expected {
                    Some(Ty::Prim(prim)) if prim.is_int() && !prim.is_signed() => {
                        return self.invalid_operand("-", Ty::Prim(prim), span);
                    }
                    // Addresses are unsigned.
                    Some(ptr @ Ty::Ptr(_)) => return self.invalid_operand("-", ptr, span),
                    _ => {}
                }
                return self.int_literal(-(*n as i128), expected, span);
            }
            (UnaryOp::Neg, ExprKind::Float(x)) => return float_literal(-x, expected),
            _ => {}
        }
        let (ty, value) = match op {
            UnaryOp::Not => (
                Ty::Prim(Prim::Bool),
                self.check(operand, Ty::Prim(Prim::Bool)),
            ),
            UnaryOp::Neg | UnaryOp::BitNot => self.expr(operand, expected),
        };
        let Ty::Prim(prim) = ty else {
            let symbol = if op == UnaryOp::Neg { "-" } else { "~" };
            return self.invalid_operand(symbol, ty, span);
        };
        let vt = prim.val_type();
        let lowered = match op {
            UnaryOp::Not => |e| Expr::Unary(ValType::I32, IrUnOp::Eqz, Box::new(e)),
            UnaryOp::Neg if prim.is_float() => {
                return (
                    ty,
                    map1(value, vt, |e| Expr::Unary(vt, IrUnOp::Neg, Box::new(e))),
                );
            }
            UnaryOp::Neg if prim.is_signed() => {
                let neg = |e| binary(vt, IrBinOp::Sub, Expr::Const(zero(vt)), e);
                return (ty, map1(value, vt, |e| normalize(prim, neg(e))));
            }
            UnaryOp::BitNot if prim.is_int() => {
                let not = |e| binary(vt, IrBinOp::Xor, e, Expr::Const(ones(vt)));
                return (ty, map1(value, vt, |e| normalize(prim, not(e))));
            }
            UnaryOp::Neg => return self.invalid_operand("-", ty, span),
            UnaryOp::BitNot => return self.invalid_operand("~", ty, span),
        };
        (ty, map1(value, vt, lowered))
    }

    fn invalid_operand(&mut self, op: &'static str, ty: Ty, span: Span) -> (Ty, Value) {
        if ty != Ty::Error {
            let kind = TypeErrorKind::InvalidOperand {
                op,
                ty: self.ck.ty_name(ty),
            };
            self.error(kind, span);
        }
        (Ty::Error, Value::default())
    }

    fn binary(
        &mut self,
        op: BinOp,
        lhs: &parse::Expr,
        rhs: &parse::Expr,
        expected: Option<Ty>,
        span: Span,
    ) -> (Ty, Value) {
        let (ty, lhs, rhs) = if matches!(op, BinOp::And | BinOp::Or) {
            let bool = Ty::Prim(Prim::Bool);
            (bool, self.check(lhs, bool), self.check(rhs, bool))
        } else {
            let expected = if is_comparison(op) { None } else { expected };
            // A literal operand takes the type of the other side, so both
            // `x + 1` and `1 + x` work for any integer `x`.
            if is_literal(lhs) && !is_literal(rhs) {
                let (ty, rhs) = self.expr(rhs, expected);
                (ty, self.check(lhs, ty), rhs)
            } else {
                let (ty, lhs) = self.expr(lhs, expected);
                (ty, lhs, self.check(rhs, ty))
            }
        };
        self.binary_values(op, ty, lhs, rhs, span)
    }

    /// Applies `op` to operands that both have type `ty`.
    fn binary_values(
        &mut self,
        op: BinOp,
        ty: Ty,
        lhs: Value,
        rhs: Value,
        span: Span,
    ) -> (Ty, Value) {
        let bool = Ty::Prim(Prim::Bool);
        let prim = match ty {
            Ty::Prim(prim) => prim,
            // Pointers compare as unsigned addresses.
            Ty::Ptr(_) if is_comparison(op) => Prim::U32,
            _ if matches!(op, BinOp::Eq | BinOp::NotEq) => {
                return self.eq_values(op, ty, lhs, rhs, span);
            }
            _ => return self.invalid_operand(binop_symbol(op), ty, span),
        };
        if matches!(op, BinOp::And | BinOp::Or) {
            if prim != Prim::Bool {
                return self.invalid_operand(binop_symbol(op), ty, span);
            }
            return (bool, self.short_circuit(op, lhs, rhs));
        }
        let (float, signed, int) = (prim.is_float(), prim.is_signed(), prim.is_int());
        let pick = |f, s, u| {
            if float {
                f
            } else if signed {
                s
            } else {
                u
            }
        };
        let (ir_op, result) = match op {
            BinOp::Add if prim.is_numeric() => (IrBinOp::Add, ty),
            BinOp::Sub if prim.is_numeric() => (IrBinOp::Sub, ty),
            BinOp::Mul if prim.is_numeric() => (IrBinOp::Mul, ty),
            BinOp::Div if prim.is_numeric() => {
                (pick(IrBinOp::Div, IrBinOp::DivS, IrBinOp::DivU), ty)
            }
            BinOp::Rem if int => (pick(IrBinOp::Div, IrBinOp::RemS, IrBinOp::RemU), ty),
            BinOp::BitAnd if int => (IrBinOp::And, ty),
            BinOp::BitOr if int => (IrBinOp::Or, ty),
            BinOp::BitXor if int => (IrBinOp::Xor, ty),
            BinOp::Shl if int => (IrBinOp::Shl, ty),
            BinOp::Shr if int => (pick(IrBinOp::ShrS, IrBinOp::ShrS, IrBinOp::ShrU), ty),
            BinOp::Eq => (IrBinOp::Eq, bool),
            BinOp::NotEq => (IrBinOp::Ne, bool),
            BinOp::Lt if prim.is_numeric() => (pick(IrBinOp::Lt, IrBinOp::LtS, IrBinOp::LtU), bool),
            BinOp::Le if prim.is_numeric() => (pick(IrBinOp::Le, IrBinOp::LeS, IrBinOp::LeU), bool),
            BinOp::Gt if prim.is_numeric() => (pick(IrBinOp::Gt, IrBinOp::GtS, IrBinOp::GtU), bool),
            BinOp::Ge if prim.is_numeric() => (pick(IrBinOp::Ge, IrBinOp::GeS, IrBinOp::GeU), bool),
            _ => return self.invalid_operand(binop_symbol(op), ty, span),
        };
        let vt = prim.val_type();
        let value = self.seq(vec![lhs, rhs]);
        let mut operands = exprs(value.scalars).into_iter();
        let (a, b) = match (operands.next(), operands.next()) {
            (Some(a), Some(b)) => (a, b),
            _ => (Expr::Const(zero(vt)), Expr::Const(zero(vt))),
        };
        let b = match ir_op {
            IrBinOp::Shl | IrBinOp::ShrS | IrBinOp::ShrU => wrap_shift_amount(prim, b),
            _ => b,
        };
        let mut expr = binary(vt, ir_op, a, b);
        if matches!(
            ir_op,
            IrBinOp::Add | IrBinOp::Sub | IrBinOp::Mul | IrBinOp::DivS | IrBinOp::Shl
        ) {
            expr = normalize(prim, expr);
        }
        let result_vt = if result == bool { ValType::I32 } else { vt };
        let value = Value {
            pre: value.pre,
            scalars: vec![(result_vt, expr)],
        };
        (result, value)
    }

    /// `and` and `or`, which only evaluate `rhs` when needed.
    fn short_circuit(&mut self, op: BinOp, lhs: Value, rhs: Value) -> Value {
        let (pre, cond) = split1(lhs);
        let rhs = single(rhs);
        let (then_expr, else_expr) = match op {
            BinOp::And => (rhs, Expr::Const(Const::I32(0))),
            _ => (Expr::Const(Const::I32(1)), rhs),
        };
        let expr = Expr::If {
            ty: ValType::I32,
            cond: Box::new(cond),
            then_expr: Box::new(then_expr),
            else_expr: Box::new(else_expr),
        };
        Value {
            pre,
            scalars: vec![(ValType::I32, expr)],
        }
    }

    fn cast(&mut self, operand: &parse::Expr, ty: &parse::Type, span: Span) -> (Ty, Value) {
        let to = self.ck.resolve_ty(ty);
        let expected = match to {
            // An integer literal cast to a pointer is an address.
            Ty::Ptr(_) => Some(Ty::Prim(Prim::U32)),
            _ => None,
        };
        let (from, value) = self.expr(operand, expected);
        if from == Ty::Error || to == Ty::Error {
            return (Ty::Error, Value::default());
        }
        match self.ck.cast_value(from, to, value) {
            Some(cast) => cast,
            None => {
                let kind = TypeErrorKind::InvalidCast {
                    from: self.ck.ty_name(from),
                    to: self.ck.ty_name(to),
                };
                self.error(kind, span);
                (Ty::Error, Value::default())
            }
        }
    }

    /// `&place`, the address of memory reached through a pointer or array.
    fn addr_of(&mut self, inner: &parse::Expr, span: Span) -> (Ty, Value) {
        if !matches!(
            inner.kind,
            ExprKind::Field(..) | ExprKind::Deref(_) | ExprKind::Index(..)
        ) {
            self.error(TypeErrorKind::NotAddressable, span);
            return (Ty::Error, Value::default());
        }
        let Some(place) = self.place(inner) else {
            return (Ty::Error, Value::default());
        };
        let Slots::Memory { addr, offset } = place.slots else {
            self.error(TypeErrorKind::NotAddressable, span);
            return (Ty::Error, Value::default());
        };
        if place.ty == Ty::Error {
            return (Ty::Error, Value::default());
        }
        let addr = match offset {
            0 => addr,
            _ => binary(
                ValType::I32,
                IrBinOp::Add,
                addr,
                Expr::Const(Const::I32(offset as i32)),
            ),
        };
        let value = Value {
            pre: place.pre,
            scalars: vec![(ValType::I32, addr)],
        };
        (self.ck.ptr_to(place.ty), value)
    }

    fn call(&mut self, callee: &parse::Expr, args: &[Arg], span: Span) -> (Ty, Value) {
        // `Err(None)` once the callee has been reported.
        let item = match &callee.kind {
            ExprKind::Name(name) if self.lookup(name).is_some() => {
                Err(Some(TypeErrorKind::NotCallable(name.clone())))
            }
            ExprKind::Name(name) if self.ck.takes_type_args(name) => {
                return self.generic_call(callee, args, span);
            }
            ExprKind::Name(name) if name == TYPE => return self.construct(Ty::Type, args, span),
            ExprKind::Name(name) => match self.ck.item(name) {
                Some(item) => Ok(item),
                None if is_builtin_type(name) => {
                    Err(Some(TypeErrorKind::NotCallable(name.clone())))
                }
                None => match self.ck.type_param(name) {
                    Some(ty) => return self.construct(ty, args, span),
                    None => Err(Some(TypeErrorKind::UnknownName(name.clone()))),
                },
            },
            ExprKind::Field(inner, field) if self.names_module(inner).is_some() => {
                match self.member(inner, field) {
                    Some(item) if self.ck.item_arity(item).is_some_and(Arity::takes_args) => {
                        return self.generic_call(callee, args, span);
                    }
                    Some(item) => Ok(item),
                    None => Err(None),
                }
            }
            // A type given type arguments, such as `array(u8)`.
            ExprKind::Call(inner, targs) if self.names_type(inner, targs) => {
                let ty = self.expr_type(callee);
                return self.construct(ty, args, span);
            }
            // A function given type arguments, such as `id(u8)`.
            ExprKind::Call(inner, targs) if self.names_fn(inner) => {
                return self.explicit_call(callee, inner, targs, args, span);
            }
            _ => Err(Some(TypeErrorKind::NotCallable("expression".to_string()))),
        };
        match item {
            Ok(Item::Func(id)) => {
                let sig = self.ck.funcs[id.0 as usize].clone();
                let value = self.args(&sig.params, args, false, span);
                self.call_func(id, value)
            }
            Ok(Item::GenericFn(generic)) => self.generic_fn_call(generic, None, args, span),
            Ok(Item::Struct(id)) => self.construct(Ty::Struct(id), args, span),
            Ok(Item::Enum(_) | Item::Global(_) | Item::Module(_)) | Err(_) => {
                let error = match item {
                    Ok(_) => Some(TypeErrorKind::NotCallable(path_text(callee))),
                    Err(error) => error,
                };
                if let Some(kind) = error {
                    self.error(kind, callee.span);
                }
                for arg in args {
                    self.expr(&arg.value, None);
                }
                (Ty::Error, Value::default())
            }
        }
    }

    /// A call of function `id` with the scalars of its arguments, in
    /// parameter order.
    fn call_func(&mut self, id: FuncId, value: Value) -> (Ty, Value) {
        let ret = self.ck.funcs[id.0 as usize].ret;
        let results = self.ck.val_types(ret);
        let mut pre = value.pre;
        let args = exprs(value.scalars);
        let mut scalars = if let [result] = results[..] {
            vec![(result, Expr::Call(id, args))]
        } else {
            let dests: Vec<_> = results.iter().map(|vt| self.temp(*vt)).collect();
            let scalars = results
                .iter()
                .zip(&dests)
                .map(|(vt, dest)| (*vt, Expr::Local(*dest)))
                .collect();
            pre.push(Stmt::Call {
                func: id,
                args,
                dests,
            });
            scalars
        };
        // The host may return any `i32` for a narrow integer or `bool`.
        if id.0 < self.ck.import_count {
            let prims = self.ck.leaf_prims(ret);
            for ((_, scalar), prim) in scalars.iter_mut().zip(prims) {
                if let Some(prim) = prim {
                    let expr = mem::replace(scalar, Expr::Const(Const::I32(0)));
                    *scalar = into_range(prim, expr);
                }
            }
        }
        (ret, Value { pre, scalars })
    }

    /// A value of a struct, array, or `type` type `ty`, built from its
    /// labelled fields.
    fn construct(&mut self, ty: Ty, args: &[Arg], span: Span) -> (Ty, Value) {
        let fields: Vec<_> = match ty {
            Ty::Struct(id) => {
                let def = &self.ck.structs[id.0 as usize];
                let private = def.fields.iter().find(|f| !f.is_pub);
                if let Some(field) = private.filter(|_| def.module != self.ck.module) {
                    let kind = TypeErrorKind::PrivateField {
                        ty: def.name.clone(),
                        field: field.name.clone(),
                    };
                    self.error(kind, span);
                }
                let def = &self.ck.structs[id.0 as usize];
                def.fields.iter().map(|f| (f.name.clone(), f.ty)).collect()
            }
            Ty::Array(_) | Ty::Type => builtin_fields(ty)
                .iter()
                .map(|name| name.to_string())
                .zip(self.ck.members(ty))
                .collect(),
            _ => {
                if ty != Ty::Error {
                    self.error(TypeErrorKind::NotCallable(self.ck.ty_name(ty)), span);
                }
                for arg in args {
                    self.expr(&arg.value, None);
                }
                return (Ty::Error, Value::default());
            }
        };
        (ty, self.args(&fields, args, true, span))
    }

    /// Checks call arguments against `params`. They are evaluated in source
    /// order, and their scalars are returned in parameter order.
    fn args(
        &mut self,
        params: &[(String, Ty)],
        args: &[Arg],
        require_labels: bool,
        span: Span,
    ) -> Value {
        let binding = self.bind_args(params, args, require_labels, span);
        let checked = args.iter().map(|_| None).collect();
        self.bound_args(params, args, binding, checked)
    }

    /// Checks call arguments against the parameters `binding` matches them
    /// with, as [`Self::args`] does. Those `checked` already, with their
    /// types, are only compared with their parameter's.
    fn bound_args(
        &mut self,
        params: &[(String, Ty)],
        args: &[Arg],
        binding: Vec<Option<usize>>,
        checked: Vec<Option<(Ty, Value)>>,
    ) -> Value {
        let mut values = Vec::new();
        // Parameter index and scalar count of each value.
        let mut groups = Vec::new();
        for ((arg, param), checked) in args.iter().zip(binding).zip(checked) {
            match param {
                Some(i) => {
                    let value = match checked {
                        Some((ty, value)) => {
                            self.expect(ty, params[i].1, arg.value.span);
                            value
                        }
                        None => self.check(&arg.value, params[i].1),
                    };
                    groups.push((i, value.scalars.len()));
                    values.push(value);
                }
                None => {
                    self.expr(&arg.value, None);
                }
            }
        }
        let mut value = self.seq(values);
        // Pure scalars can be reordered freely; anything with side effects
        // must be evaluated before the reordering.
        let reordered = groups.windows(2).any(|pair| pair[0].0 > pair[1].0);
        if reordered && !value.scalars.iter().all(|(_, e)| is_pure(e)) {
            self.spill(&mut value, is_stable);
        }
        let mut by_param = vec![Vec::new(); params.len()];
        let mut scalars = value.scalars.into_iter();
        for (i, count) in groups {
            by_param[i] = scalars.by_ref().take(count).collect();
        }
        value.scalars = by_param.into_iter().flatten().collect();
        value
    }

    /// Matches each argument to a parameter, returning its index. Positional
    /// arguments fill parameters in order, then labels fill the rest.
    fn bind_args(
        &mut self,
        params: &[(String, Ty)],
        args: &[Arg],
        require_labels: bool,
        span: Span,
    ) -> Vec<Option<usize>> {
        let mut bound = vec![false; params.len()];
        let mut labelled = false;
        let mut next = 0;
        let mut binding = Vec::new();
        for arg in args {
            let param = match &arg.label {
                None if labelled => Err(TypeErrorKind::PositionalAfterLabel),
                None if require_labels => Err(TypeErrorKind::UnlabelledField),
                None => {
                    next += 1;
                    if next <= params.len() {
                        Ok(next - 1)
                    } else if next == params.len() + 1 {
                        Err(TypeErrorKind::TooManyArgs {
                            expected: params.len(),
                            found: args.len(),
                        })
                    } else {
                        binding.push(None);
                        continue;
                    }
                }
                Some(label) => {
                    labelled = true;
                    params
                        .iter()
                        .position(|(name, _)| *name == label.name)
                        .ok_or_else(|| TypeErrorKind::UnknownLabel(label.name.clone()))
                }
            };
            let param = param.and_then(|i| {
                if bound[i] {
                    Err(TypeErrorKind::DuplicateArg(params[i].0.clone()))
                } else {
                    Ok(i)
                }
            });
            match param {
                Ok(i) => {
                    bound[i] = true;
                    binding.push(Some(i));
                }
                Err(kind) => {
                    self.error(kind, arg.value.span);
                    binding.push(None);
                }
            }
        }
        for (i, bound) in bound.into_iter().enumerate() {
            if !bound {
                self.error(TypeErrorKind::MissingArg(params[i].0.clone()), span);
            }
        }
        binding
    }

    /// Reads a `ty` at `offset` bytes past the address in `ptr`.
    fn load(&mut self, ptr: Value, offset: u32, ty: Ty) -> Value {
        let cells = self.ck.cells(ty);
        let (pre, addr) = if cells.len() > 1 {
            self.reusable_addr(ptr)
        } else {
            split1(ptr)
        };
        let scalars = cells
            .into_iter()
            .map(|cell| {
                let load = Expr::Load {
                    ty: cell.ty,
                    op: cell.load,
                    offset: offset + cell.offset,
                    addr: Box::new(addr.clone()),
                };
                // Any nonzero byte is `true`.
                let load = match cell.bool {
                    true => into_range(Prim::Bool, load),
                    false => load,
                };
                (cell.ty, load)
            })
            .collect();
        Value { pre, scalars }
    }

    /// Keeps the scalars in `range`, preserving the side effects of the rest.
    fn project(&mut self, mut value: Value, range: Range<usize>) -> Value {
        let drops_effects = value
            .scalars
            .iter()
            .enumerate()
            .any(|(i, (_, e))| !range.contains(&i) && !is_pure(e));
        if drops_effects {
            self.spill(&mut value, is_stable);
        }
        value.scalars = value.scalars.drain(range).collect();
        value
    }

    /// Concatenates values, preserving evaluation order: each value's `pre`
    /// must run after the scalars of the values before it.
    fn seq(&mut self, values: Vec<Value>) -> Value {
        let mut out = Value::default();
        for value in values {
            if !value.pre.is_empty() {
                self.spill(&mut out, is_stable);
            }
            out.pre.extend(value.pre);
            out.scalars.extend(value.scalars);
        }
        out
    }

    /// Moves each scalar that doesn't satisfy `keep` into a temporary, set at
    /// the end of `pre`.
    fn spill(&mut self, value: &mut Value, keep: fn(&Expr) -> bool) {
        for (vt, scalar) in &mut value.scalars {
            if !keep(scalar) {
                let tmp = self.temp(*vt);
                let expr = mem::replace(scalar, Expr::Local(tmp));
                value.pre.push(Stmt::SetLocal(tmp, expr));
            }
        }
    }
}

fn scalar(ty: ValType, expr: Expr) -> Value {
    Value {
        pre: Vec::new(),
        scalars: vec![(ty, expr)],
    }
}

fn exprs(scalars: Vec<(ValType, Expr)>) -> Vec<Expr> {
    scalars.into_iter().map(|(_, e)| e).collect()
}

/// Splits a single-scalar value into its prelude and scalar.
fn split1(value: Value) -> (Vec<Stmt>, Expr) {
    let expr = match <[_; 1]>::try_from(value.scalars) {
        Ok([(_, expr)]) => expr,
        // Only after a type error.
        Err(_) => Expr::Const(Const::I32(0)),
    };
    (value.pre, expr)
}

/// A single-scalar value as one expression.
fn single(value: Value) -> Expr {
    let (pre, expr) = split1(value);
    if pre.is_empty() {
        expr
    } else {
        Expr::Seq(pre, Box::new(expr))
    }
}

/// Replaces the single scalar of `value` with `f` applied to it.
fn map1(value: Value, ty: ValType, f: impl FnOnce(Expr) -> Expr) -> Value {
    let expr = match <[_; 1]>::try_from(value.scalars) {
        Ok([(_, expr)]) => f(expr),
        Err(_) => Expr::Const(zero(ty)),
    };
    Value {
        pre: value.pre,
        scalars: vec![(ty, expr)],
    }
}

/// A float literal, typed by `expected` and defaulting to `f64`.
fn float_literal(x: f64, expected: Option<Ty>) -> (Ty, Value) {
    if expected == Some(Ty::Prim(Prim::F32)) {
        let value = scalar(ValType::F32, Expr::Const(Const::F32(x as f32)));
        (Ty::Prim(Prim::F32), value)
    } else {
        let value = scalar(ValType::F64, Expr::Const(Const::F64(x)));
        (Ty::Prim(Prim::F64), value)
    }
}

fn is_literal(expr: &parse::Expr) -> bool {
    match &expr.kind {
        ExprKind::Int(_) | ExprKind::Float(_) => true,
        ExprKind::Unary(UnaryOp::Neg, operand) => {
            matches!(operand.kind, ExprKind::Int(_) | ExprKind::Float(_))
        }
        _ => false,
    }
}

fn is_comparison(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
    )
}

fn binop_symbol(op: BinOp) -> &'static str {
    match op {
        BinOp::Or => "or",
        BinOp::And => "and",
        BinOp::Eq => "==",
        BinOp::NotEq => "!=",
        BinOp::Lt => "<",
        BinOp::Le => "<=",
        BinOp::Gt => ">",
        BinOp::Ge => ">=",
        BinOp::BitOr => "|",
        BinOp::BitXor => "^",
        BinOp::BitAnd => "&",
        BinOp::Shl => "<<",
        BinOp::Shr => ">>",
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::Rem => "%",
    }
}

fn binary(ty: ValType, op: IrBinOp, a: Expr, b: Expr) -> Expr {
    Expr::Binary(ty, op, Box::new(a), Box::new(b))
}

/// Writes `c` to the start of `out` as `store` would.
fn write_const(out: &mut [u8], store: StoreOp, c: Const) {
    let bytes = match c {
        Const::I32(x) => x.to_le_bytes().to_vec(),
        Const::I64(x) => x.to_le_bytes().to_vec(),
        Const::F32(x) => x.to_le_bytes().to_vec(),
        Const::F64(x) => x.to_le_bytes().to_vec(),
    };
    let width = match store {
        StoreOp::Store8 => 1,
        StoreOp::Store16 => 2,
        StoreOp::Store => bytes.len(),
    };
    out[..width].copy_from_slice(&bytes[..width]);
}

/// The address of element `index` of an array whose elements start at `ptr`
/// and are `stride` bytes apart.
fn element_addr(ptr: Expr, index: Expr, stride: u32) -> Expr {
    let offset = match stride {
        1 => index,
        _ => binary(
            ValType::I32,
            IrBinOp::Mul,
            index,
            Expr::Const(Const::I32(stride as i32)),
        ),
    };
    binary(ValType::I32, IrBinOp::Add, ptr, offset)
}

fn zero(ty: ValType) -> Const {
    match ty {
        // Only after a type error: nothing constant has this type.
        ValType::I32 | ValType::ExternRef => Const::I32(0),
        ValType::I64 => Const::I64(0),
        ValType::F32 => Const::F32(0.0),
        ValType::F64 => Const::F64(0.0),
    }
}

/// An integer with every bit set.
fn ones(ty: ValType) -> Const {
    match ty {
        ValType::I64 => Const::I64(-1),
        _ => Const::I32(-1),
    }
}

/// Wraps an `i32` holding a result of a narrower type back into its range:
/// sign-extended for signed types and zero-extended for unsigned ones.
fn normalize(prim: Prim, expr: Expr) -> Expr {
    let extend = |op| Expr::Unary(ValType::I32, op, Box::new(expr.clone()));
    let mask = |m| {
        binary(
            ValType::I32,
            IrBinOp::And,
            expr.clone(),
            Expr::Const(Const::I32(m)),
        )
    };
    match prim {
        Prim::I8 => extend(IrUnOp::Extend8S),
        Prim::I16 => extend(IrUnOp::Extend16S),
        Prim::U8 => mask(0xff),
        Prim::U16 => mask(0xffff),
        _ => expr,
    }
}

/// Brings a value of type `prim` returned by the host or loaded from memory
/// into range, as either may hold any `i32` for a narrow integer or `bool`.
fn into_range(prim: Prim, expr: Expr) -> Expr {
    match prim {
        Prim::Bool => binary(ValType::I32, IrBinOp::Ne, expr, Expr::Const(Const::I32(0))),
        prim => normalize(prim, expr),
    }
}

/// Wraps a shift amount to the bit width of a narrow `prim`, so every integer
/// type shifts by its amount modulo its width, as wasm does for 32 and 64 bits.
fn wrap_shift_amount(prim: Prim, amount: Expr) -> Expr {
    let mask = match prim {
        Prim::I8 | Prim::U8 => 7,
        Prim::I16 | Prim::U16 => 15,
        _ => return amount,
    };
    match amount {
        Expr::Const(Const::I32(n)) => Expr::Const(Const::I32(n & mask)),
        amount => binary(
            ValType::I32,
            IrBinOp::And,
            amount,
            Expr::Const(Const::I32(mask)),
        ),
    }
}

/// Whether `from as to` is allowed between distinct primitives: any numeric
/// conversion, and `bool` to an integer.
fn convertible(from: Prim, to: Prim) -> bool {
    (from.is_numeric() && to.is_numeric()) || (from == Prim::Bool && to.is_int())
}

/// Lowers `expr as to`. Float to integer conversions saturate.
fn convert(from: Prim, to: Prim, expr: Expr) -> Expr {
    let (fvt, tvt) = (from.val_type(), to.val_type());
    let unary = |op, e| Expr::Unary(fvt, op, Box::new(e));
    if from.is_float() && to.is_float() {
        let op = if from == Prim::F32 {
            IrUnOp::Promote
        } else {
            IrUnOp::Demote
        };
        return unary(op, expr);
    }
    if to.is_float() {
        let op = if from.is_signed() {
            IrUnOp::ConvertS(tvt)
        } else {
            IrUnOp::ConvertU(tvt)
        };
        return unary(op, expr);
    }
    if from.is_float() {
        let (min, max) = to.range();
        let expr = if tvt == ValType::I32 && to != Prim::I32 && to != Prim::U32 {
            // Clamp to the narrow range first; NaN stays NaN and truncates to 0.
            let bound = |x: i128| {
                Expr::Const(if fvt == ValType::F32 {
                    Const::F32(x as f32)
                } else {
                    Const::F64(x as f64)
                })
            };
            let upper = binary(fvt, IrBinOp::Min, expr, bound(max));
            binary(fvt, IrBinOp::Max, upper, bound(min))
        } else {
            expr
        };
        let op = if to.is_signed() {
            IrUnOp::TruncSatS(tvt)
        } else {
            IrUnOp::TruncSatU(tvt)
        };
        return unary(op, expr);
    }
    // Integer (or bool) to integer.
    match (fvt, tvt) {
        (ValType::I32, ValType::I64) if from.is_signed() => unary(IrUnOp::ExtendS, expr),
        (ValType::I32, ValType::I64) => unary(IrUnOp::ExtendU, expr),
        (ValType::I64, ValType::I32) => normalize(to, unary(IrUnOp::Wrap, expr)),
        _ => normalize(to, expr),
    }
}

/// Whether evaluating `expr` has no side effects.
fn is_pure(expr: &Expr) -> bool {
    match expr {
        Expr::Const(_) | Expr::Local(_) | Expr::Global(_) => true,
        Expr::Unary(_, _, x) | Expr::Load { addr: x, .. } => is_pure(x),
        Expr::Binary(_, _, a, b) => is_pure(a) && is_pure(b),
        Expr::If {
            cond,
            then_expr,
            else_expr,
            ..
        } => is_pure(cond) && is_pure(then_expr) && is_pure(else_expr),
        Expr::Call(..) | Expr::Seq(..) => false,
    }
}

/// Whether `expr` is pure and its value can't be changed by side effects, so
/// it may be evaluated later than written. Calls can change globals and memory
/// but not the caller's locals.
fn is_stable(expr: &Expr) -> bool {
    match expr {
        Expr::Const(_) | Expr::Local(_) => true,
        Expr::Unary(_, _, x) => is_stable(x),
        Expr::Binary(_, _, a, b) => is_stable(a) && is_stable(b),
        Expr::If {
            cond,
            then_expr,
            else_expr,
            ..
        } => is_stable(cond) && is_stable(then_expr) && is_stable(else_expr),
        Expr::Global(_) | Expr::Call(..) | Expr::Load { .. } | Expr::Seq(..) => false,
    }
}

/// `expr` as written, if it's a name or a path of names, like `a.b.c`.
fn path_text(expr: &parse::Expr) -> String {
    match &expr.kind {
        ExprKind::Name(name) => name.clone(),
        ExprKind::Field(inner, field) => format!("{}.{}", path_text(inner), field.name),
        _ => "expression".to_string(),
    }
}

/// The names in `expr`, a path of names like `a.b`, in order. `None` for
/// any other expression.
fn module_path(expr: &parse::Expr) -> Option<Vec<Ident>> {
    match &expr.kind {
        ExprKind::Name(name) => Some(vec![Ident {
            name: name.clone(),
            span: expr.span,
        }]),
        ExprKind::Field(inner, field) => {
            let mut path = module_path(inner)?;
            path.push(field.clone());
            Some(path)
        }
        _ => None,
    }
}

/// Whether `name` is a type the language defines, which no type parameter
/// may take.
fn is_builtin_type(name: &str) -> bool {
    [ARRAY, TUPLE, EXTERNREF, TYPE].contains(&name) || Prim::from_name(name).is_some()
}

/// The names of the fields of an array or `type`, in order. Empty for any
/// other type.
fn builtin_fields(ty: Ty) -> &'static [&'static str] {
    match ty {
        Ty::Array(_) => &ARRAY_FIELDS,
        Ty::Type => &TYPE_FIELDS,
        _ => &[],
    }
}

/// The names `pattern` binds, in source order.
fn pattern_names(pattern: &Pattern) -> Vec<Ident> {
    fn push(pattern: &Pattern, out: &mut Vec<Ident>) {
        match &pattern.kind {
            PatternKind::Name(name) => out.push(Ident {
                name: name.clone(),
                span: pattern.span,
            }),
            PatternKind::Discard => {}
            PatternKind::Tuple(elems) => {
                for elem in elems {
                    push(elem, out);
                }
            }
        }
    }
    let mut out = Vec::new();
    push(pattern, &mut out);
    out
}

/// Every imported function, with the block that declares it.
fn extern_fns(program: &Program) -> impl Iterator<Item = (&ExternBlock, &ExternFn)> {
    let blocks = program.items.iter().filter_map(|item| match &item.kind {
        ItemKind::Extern(block) => Some(block),
        _ => None,
    });
    blocks.flat_map(|block| block.fns.iter().map(move |f| (block, f)))
}

/// Every defined function that isn't generic, with the item that declares
/// it.
fn fn_decls(program: &Program) -> impl Iterator<Item = (&parse::Item, &parse::FnDecl)> {
    program.items.iter().filter_map(|item| match &item.kind {
        ItemKind::Fn(f) if f.sig.type_params.is_empty() => Some((item, f)),
        _ => None,
    })
}

/// Every generic function, in [`Item::GenericFn`] order, with the item that
/// declares it.
fn generic_fn_decls(program: &Program) -> impl Iterator<Item = (&parse::Item, &parse::FnDecl)> {
    program.items.iter().filter_map(|item| match &item.kind {
        ItemKind::Fn(f) if !f.sig.type_params.is_empty() => Some((item, f)),
        _ => None,
    })
}

/// Every function signature in [`FuncId`] order, imports then definitions,
/// with whether it's `pub`.
fn fn_sigs(program: &Program) -> impl Iterator<Item = (bool, &FnSig)> {
    let imports = extern_fns(program).map(|(_, f)| (f.is_pub, &f.sig));
    imports.chain(fn_decls(program).map(|(item, f)| (item.is_pub, &f.sig)))
}

/// Whether control can never reach the end of `block`.
fn diverges(block: &[parse::Stmt]) -> bool {
    block.iter().any(|stmt| match &stmt.kind {
        StmtKind::Return(_) => true,
        StmtKind::If {
            then_body,
            else_body: Some(else_body),
            ..
        } => diverges(then_body) && diverges(else_body),
        StmtKind::While { cond, body } => {
            matches!(cond.kind, ExprKind::Bool(true)) && !breaks(body)
        }
        _ => false,
    })
}

/// Whether `block` can break out of the loop it's directly in.
fn breaks(block: &[parse::Stmt]) -> bool {
    block.iter().any(|stmt| match &stmt.kind {
        StmtKind::Break => true,
        StmtKind::If {
            then_body,
            else_body,
            ..
        } => breaks(then_body) || else_body.as_deref().is_some_and(breaks),
        _ => false,
    })
}

fn fold_unary(op: IrUnOp, c: Const) -> Result<Const, Fold> {
    use Const::*;
    Ok(match (op, c) {
        (IrUnOp::Eqz, I32(x)) => I32((x == 0) as i32),
        (IrUnOp::Eqz, I64(x)) => I32((x == 0) as i32),
        (IrUnOp::Neg, F32(x)) => F32(-x),
        (IrUnOp::Neg, F64(x)) => F64(-x),
        (IrUnOp::Extend8S, I32(x)) => I32(x as i8 as i32),
        (IrUnOp::Extend16S, I32(x)) => I32(x as i16 as i32),
        (IrUnOp::Extend8S, I64(x)) => I64(x as i8 as i64),
        (IrUnOp::Extend16S, I64(x)) => I64(x as i16 as i64),
        (IrUnOp::Wrap, I64(x)) => I32(x as i32),
        (IrUnOp::ExtendS, I32(x)) => I64(x as i64),
        (IrUnOp::ExtendU, I32(x)) => I64(x as u32 as i64),
        (IrUnOp::Demote, F64(x)) => F32(x as f32),
        (IrUnOp::Promote, F32(x)) => F64(x as f64),
        (IrUnOp::Reinterpret, F32(x)) => I32(x.to_bits() as i32),
        (IrUnOp::Reinterpret, F64(x)) => I64(x.to_bits() as i64),
        // Rust's float to int `as` saturates and maps NaN to 0, like wasm's
        // `trunc_sat`.
        (IrUnOp::TruncSatS(to), F32(_) | F64(_)) => {
            let x = float(c);
            match to {
                ValType::I64 => I64(x as i64),
                _ => I32(x as i32),
            }
        }
        (IrUnOp::TruncSatU(to), F32(_) | F64(_)) => {
            let x = float(c);
            match to {
                ValType::I64 => I64(x as u64 as i64),
                _ => I32(x as u32 as i32),
            }
        }
        (IrUnOp::ConvertS(to), I32(_) | I64(_)) => {
            let x = match c {
                I32(x) => x as i64,
                I64(x) => x,
                _ => unreachable!(),
            };
            match to {
                ValType::F32 => F32(x as f32),
                _ => F64(x as f64),
            }
        }
        (IrUnOp::ConvertU(to), I32(_) | I64(_)) => {
            let x = match c {
                I32(x) => x as u32 as u64,
                I64(x) => x as u64,
                _ => unreachable!(),
            };
            match to {
                ValType::F32 => F32(x as f32),
                _ => F64(x as f64),
            }
        }
        _ => return Err(Fold::NotConstant),
    })
}

fn fold_binary(op: IrBinOp, a: Const, b: Const) -> Result<Const, Fold> {
    Ok(match (a, b) {
        (Const::I32(a), Const::I32(b)) => fold_int_binary!(op, a, b, i32, u32, I32),
        (Const::I64(a), Const::I64(b)) => fold_int_binary!(op, a, b, i64, u64, I64),
        (Const::F32(a), Const::F32(b)) => fold_float_binary!(op, a, b, f32, F32),
        (Const::F64(a), Const::F64(b)) => fold_float_binary!(op, a, b, f64, F64),
        _ => return Err(Fold::NotConstant),
    })
}

/// A float constant widened to `f64`, which is exact.
fn float(c: Const) -> f64 {
    match c {
        Const::F32(x) => x as f64,
        Const::F64(x) => x,
        Const::I32(x) => x as f64,
        Const::I64(x) => x as f64,
    }
}

/// `fN.min`: NaN if either operand is, and `-0 < +0`.
fn wasm_min(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a == b {
        if a.is_sign_negative() { a } else { b }
    } else {
        a.min(b)
    }
}

/// `fN.max`: NaN if either operand is, and `-0 < +0`.
fn wasm_max(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a == b {
        if a.is_sign_negative() { b } else { a }
    } else {
        a.max(b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::{DummyManager, FileManager, MemoryLimits};
    use crate::ir::{Const, Expr, Func, Module, Stmt, ValType};
    use crate::lex::tokenize;

    fn check_src(src: &str) -> Result<Module, Vec<TypeError>> {
        check_with(src, &Settings::default())
    }

    fn check_with(src: &str, settings: &Settings) -> Result<Module, Vec<TypeError>> {
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        check(
            &Program::single(entry, parse::parse(&tokens).unwrap()),
            settings,
        )
    }

    fn lower(src: &str) -> Module {
        match check_src(src) {
            Ok(module) => module,
            Err(errors) => panic!("unexpected type errors: {errors:#?}"),
        }
    }

    fn errors(src: &str) -> Vec<TypeErrorKind> {
        check_src(src)
            .unwrap_err()
            .into_iter()
            .map(|e| e.kind)
            .collect()
    }

    /// Renders the body of the function `name` as s-expressions.
    fn body(module: &Module, name: &str) -> String {
        let func = module.funcs.iter().find(|f| f.name == name).unwrap();
        stmts(module, func, &func.body)
    }

    /// The source name of an imported or defined function.
    fn func_name(module: &Module, id: FuncId) -> &str {
        let index = id.0 as usize;
        match module.imports.get(index) {
            Some(import) => &import.name,
            None => &module.funcs[index - module.imports.len()].name,
        }
    }

    fn stmts(module: &Module, func: &Func, body: &[Stmt]) -> String {
        body.iter()
            .map(|s| stmt(module, func, s))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn stmt(m: &Module, f: &Func, s: &Stmt) -> String {
        let e = |e: &Expr| expr(m, f, e);
        let list = |es: &[Expr]| es.iter().map(e).collect::<Vec<_>>().join(" ");
        match s {
            Stmt::SetLocal(l, v) => format!("(set {} {})", local(f, *l), e(v)),
            Stmt::SetGlobal(g, v) => format!("(set @{} {})", m.globals[g.0 as usize].name, e(v)),
            Stmt::Store {
                ty,
                op,
                offset,
                addr,
                value,
            } => format!("({ty:?}.{op:?} offset={offset} {} {})", e(addr), e(value)),
            Stmt::Drop(v) => format!("(drop {})", e(v)),
            Stmt::Call { func, args, dests } => {
                let dests: Vec<_> = dests.iter().map(|d| local(f, *d)).collect();
                let name = func_name(m, *func);
                format!("(call {name} [{}] -> [{}])", list(args), dests.join(" "))
            }
            Stmt::Block(b) => format!("(block {})", stmts(m, f, b)),
            Stmt::Loop(b) => format!("(loop {})", stmts(m, f, b)),
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => format!(
                "(if {} (then {}) (else {}))",
                e(cond),
                stmts(m, f, then_body),
                stmts(m, f, else_body)
            ),
            Stmt::Br(depth) => format!("(br {depth})"),
            Stmt::BrIf(depth, cond) => format!("(br_if {depth} {})", e(cond)),
            Stmt::Return(values) => format!("(return {})", list(values)),
            Stmt::Unreachable => "unreachable".to_string(),
        }
    }

    fn expr(m: &Module, f: &Func, e: &Expr) -> String {
        let ex = |e: &Expr| expr(m, f, e);
        match e {
            Expr::Const(c) => konst(*c),
            Expr::Local(l) => local(f, *l),
            Expr::Global(g) => format!("@{}", m.globals[g.0 as usize].name),
            Expr::Unary(ty, op, x) => format!("({ty:?}.{op:?} {})", ex(x)),
            Expr::Load {
                ty,
                op,
                offset,
                addr,
            } => format!("({ty:?}.{op:?} offset={offset} {})", ex(addr)),
            Expr::Binary(ty, op, a, b) => format!("({ty:?}.{op:?} {} {})", ex(a), ex(b)),
            Expr::Call(func, args) => {
                let args: Vec<_> = args.iter().map(ex).collect();
                format!("(call {} {})", func_name(m, *func), args.join(" "))
            }
            Expr::If {
                cond,
                then_expr,
                else_expr,
                ..
            } => format!("(if {} {} {})", ex(cond), ex(then_expr), ex(else_expr)),
            Expr::Seq(body, value) => format!("(seq {} {})", stmts(m, f, body), ex(value)),
        }
    }

    fn konst(c: Const) -> String {
        match c {
            Const::I32(x) => x.to_string(),
            Const::I64(x) => format!("{x}i64"),
            Const::F32(x) => format!("{x}f32"),
            Const::F64(x) => format!("{x}f64"),
        }
    }

    /// The offset and bytes of each data segment.
    fn data(module: &Module) -> Vec<(u32, &[u8])> {
        module
            .data
            .iter()
            .map(|d| (d.offset, &d.bytes[..]))
            .collect()
    }

    /// Temporaries are numbered so that tests can tell them apart.
    fn local(f: &Func, l: ir::LocalId) -> String {
        match f.locals[l.0 as usize].name.as_str() {
            "tmp" => format!("tmp{}", l.0),
            name => name.to_string(),
        }
    }

    #[test]
    fn example_program() {
        let module = lower(include_str!("../example.duck"));
        let exports: Vec<_> = module.funcs.iter().map(|f| f.export.as_deref()).collect();
        assert_eq!(exports, vec![Some("add"), Some("main")]);
        assert_eq!(body(&module, "add"), "(return (I32.Add a b))");
        let imports: Vec<_> = module
            .imports
            .iter()
            .map(|i| (i.name.as_str(), i.module.as_str(), i.field.as_str()))
            .collect();
        assert_eq!(
            imports,
            vec![
                ("logi", "env", "logi"),
                ("logf", "env", "log_f32"),
                ("logs", "env", "log_str")
            ]
        );
        let main = body(&module, "main");
        assert!(
            main.contains(
                "(call logi [c] -> []) (call logf [1.5f32] -> []) \
                 (call logs [@greeting.len @greeting.ptr] -> [])"
            ),
            "{main}"
        );
        assert_eq!(
            data(&module),
            [(0, &b"Hello, duck!"[..]), (12, &[2, 3, 5, 7])]
        );
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.mutable, g.init))
            .collect();
        assert_eq!(
            globals,
            vec![
                ("global", false, Const::I32(1)),
                ("counter", true, Const::I32(0)),
                ("greeting.len", false, Const::I32(12)),
                ("greeting.ptr", false, Const::I32(0)),
                ("primes.len", false, Const::I32(4)),
                ("primes.ptr", false, Const::I32(12)),
                ("data_end", false, Const::I32(16)),
            ]
        );
    }

    #[test]
    fn while_loops_become_block_loop() {
        let module = lower("fn f():\n    var i = 0\n    while i < 3:\n        i += 1\n");
        assert_eq!(
            body(&module, "f"),
            "(set i 0) (block (loop (br_if 1 (I32.Eqz (I32.LtS i 3))) \
             (set i (I32.Add i 1)) (br 0)))"
        );
    }

    #[test]
    fn break_and_continue_count_enclosing_labels() {
        let src = "\
fn f(a: bool):
    while a:
        if a:
            break
        else:
            continue
        while true:
            if a:
                continue
            break
";
        assert_eq!(
            body(&lower(src), "f"),
            "(block (loop (br_if 1 (I32.Eqz a)) \
             (if a (then (br 2)) (else (br 1))) \
             (block (loop (if a (then (br 1)) (else )) (br 1) (br 0))) \
             (br 0)))"
        );
    }

    #[test]
    fn and_or_short_circuit() {
        let src = "fn f(a: bool, b: bool) -> bool:\n    return a and b or not a\n";
        assert_eq!(
            body(&lower(src), "f"),
            "(return (if (if a b 0) 1 (I32.Eqz a)))"
        );
    }

    #[test]
    fn structs_are_split_into_scalars() {
        let src = "\
struct Point:
    x: f32
    y: f32

fn make(x: f32) -> Point:
    return Point(y: 2.0, x: x)

fn get(p: Point) -> f32:
    return p.y

fn f() -> f32:
    let p = make(1.0)
    return make(3.0).x + get(p)
";
        let module = lower(src);
        let make = &module.funcs[0];
        assert_eq!(make.params, vec![ValType::F32]);
        assert_eq!(make.results, vec![ValType::F32, ValType::F32]);
        assert_eq!(body(&module, "make"), "(return x 2f32)");
        assert_eq!(module.funcs[1].params, vec![ValType::F32, ValType::F32]);
        assert_eq!(body(&module, "get"), "(return p.y)");
        assert_eq!(
            body(&module, "f"),
            "(call make [1f32] -> [tmp0 tmp1]) (set p.x tmp0) (set p.y tmp1) \
             (call make [3f32] -> [tmp4 tmp5]) (return (F32.Add tmp4 (call get p.x p.y)))"
        );
    }

    #[test]
    fn imports_come_first() {
        let src = "\
struct P:
    x: f32
    y: i64
fn first() -> i32:
    return now(scale: 2) + second()
extern \"js\":
    fn now(scale: i32) -> i32 = \"Date.now\"
fn second() -> i32:
    return 0
extern:
    fn put(p: &P, value: P) -> P
";
        let module = lower(src);
        let imports: Vec<_> = module
            .imports
            .iter()
            .map(|i| {
                let (params, results) = (i.params.clone(), i.results.clone());
                (
                    i.name.as_str(),
                    i.module.as_str(),
                    i.field.as_str(),
                    params,
                    results,
                )
            })
            .collect();
        use ValType::*;
        assert_eq!(
            imports,
            vec![
                ("now", "js", "Date.now", vec![I32], vec![I32]),
                ("put", "env", "put", vec![I32, F32, I64], vec![F32, I64]),
            ]
        );
        let funcs: Vec<_> = module.funcs.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(funcs, vec!["first", "second"]);
        assert_eq!(
            body(&module, "first"),
            "(return (I32.Add (call now 2) (call second )))"
        );
    }

    #[test]
    fn host_results_are_brought_into_range() {
        let src = "\
struct S:
    a: u8
    b: &i8
    c: bool
extern:
    fn u() -> u8
    fn i() -> i16
    fn b() -> bool
    fn p() -> &u8
    fn s() -> S
fn f():
    let x = u()
    let y = i()
    let z = b()
    let w = p()
    let v = s()
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set x (I32.And (call u ) 255)) \
             (set y (I32.Extend16S (call i ))) \
             (set z (I32.Ne (call b ) 0)) \
             (set w (call p )) \
             (call s [] -> [tmp4 tmp5 tmp6]) \
             (set v.a (I32.And tmp4 255)) (set v.b tmp5) (set v.c (I32.Ne tmp6 0))"
        );
    }

    #[test]
    fn reordered_labels_evaluate_in_source_order() {
        let src = "\
var g = 0
fn tick() -> i32:
    g += 1
    return g
fn sub(a: i32, b: i32) -> i32:
    return a - b
fn f() -> i32:
    return sub(b: tick(), a: g)
fn h() -> i32:
    return sub(g, b: 1)
";
        let module = lower(src);
        assert_eq!(body(&module, "tick"), "(set @g (I32.Add @g 1)) (return @g)");
        assert_eq!(
            body(&module, "f"),
            "(set tmp0 (call tick )) (set tmp1 @g) (return (call sub tmp1 tmp0))"
        );
        assert_eq!(body(&module, "h"), "(return (call sub @g 1))");
    }

    #[test]
    fn struct_assignment_reads_before_writing() {
        let src = "\
struct P:
    x: i32
    y: i32
fn f(q: P) -> P:
    var p = q
    p = P(x: p.y, y: p.x)
    p.x = 1
    return p
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set p.x q.x) (set p.y q.y) \
             (set tmp4 p.y) (set tmp5 p.x) (set p.x tmp4) (set p.y tmp5) \
             (set p.x 1) (return p.x p.y)"
        );
    }

    #[test]
    fn narrow_integers_wrap_to_their_width() {
        let src = "\
fn f(a: u8, b: i8):
    let s = a + 1
    let t = -b
    let u = ~a
    let k = a / 2
    let m = b / 2
    let n = b & 3
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set s (I32.And (I32.Add a 1) 255)) \
             (set t (I32.Extend8S (I32.Sub 0 b))) \
             (set u (I32.And (I32.Xor a -1) 255)) \
             (set k (I32.DivU a 2)) \
             (set m (I32.Extend8S (I32.DivS b 2))) \
             (set n (I32.And b 3))"
        );
    }

    #[test]
    fn casts() {
        let src = "\
fn f(a: u8, b: i8, c: i64, x: f32):
    let w = a as i64
    let v = b as u16
    let y = c as i8
    let z = x as u8
    let i = x as i64
    let q = c as f64
    let r = true as u64
    let p = x as f64
    let same = a as u8
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set w (I32.ExtendU a)) \
             (set v (I32.And b 65535)) \
             (set y (I32.Extend8S (I64.Wrap c))) \
             (set z (F32.TruncSatU(I32) (F32.Max (F32.Min x 255f32) 0f32))) \
             (set i (F32.TruncSatS(I64) x)) \
             (set q (I64.ConvertS(F64) c)) \
             (set r (I32.ExtendU 1)) \
             (set p (F32.Promote x)) \
             (set same a)"
        );
    }

    #[test]
    fn every_type_casts_to_itself() {
        let src = "\
struct S:
    a: i32
    e: externref
fn u():
    pass
fn f(b: bool, p: &i32, e: externref, s: S):
    let b2 = b as bool
    let p2 = p as &i32
    let e2 = e as externref
    let s2 = s as S
    let u2 = u() as tuple()
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set b2 b) (set p2 p) (set e2 e) (set s2.a s.a) (set s2.e s.e) (call u [] -> [])"
        );
    }

    #[test]
    fn literals_take_the_expected_type() {
        let src = "\
fn f(x: i64, y: f32):
    let a = 1
    let b = x + 1
    let c = 1 + x
    let d = y * 2
    let e: u64 = 18446744073709551615
    let g: i8 = -128
    let h = 1.5
    let i: f32 = -1
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(set a 1) (set b (I64.Add x 1i64)) (set c (I64.Add 1i64 x)) \
             (set d (F32.Mul y 2f32)) (set e -1i64) (set g -128) (set h 1.5f64) (set i -1f32)"
        );
        let a = module.funcs[0]
            .locals
            .iter()
            .find(|l| l.name == "a")
            .unwrap();
        assert_eq!(a.ty, ValType::I32);
    }

    #[test]
    fn global_initializers_are_folded() {
        let src = "\
struct P:
    x: i32
    y: i32
let a: u8 = 200 + 100
let b = a as i64 * 2
let origin = P(y: 2, x: -1)
let flag = a > 3 and not false
var v = 1.5 as f32
";
        let globals: Vec<_> = lower(src)
            .globals
            .into_iter()
            .map(|g| (g.name, g.mutable, konst(g.init)))
            .collect();
        let expected = [
            ("a", false, "44"),
            ("b", false, "88i64"),
            ("origin.x", false, "-1"),
            ("origin.y", false, "2"),
            ("flag", false, "1"),
            ("v", true, "1.5f32"),
            ("data_end", false, "0"),
        ];
        let expected: Vec<_> = expected
            .into_iter()
            .map(|(n, m, i)| (n.to_string(), m, i.to_string()))
            .collect();
        assert_eq!(globals, expected);
    }

    #[test]
    fn global_initializers_must_be_constant() {
        let src = "\
fn f() -> i32:
    return 1
let c = f()
let d = 1 / 0
var m = 1
let n = m
let p = q
let q = 1
";
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::NotConstant,
                TypeErrorKind::ConstTrap,
                TypeErrorKind::NotConstant,
                TypeErrorKind::NotConstant,
            ]
        );
    }

    #[test]
    fn every_path_must_return() {
        let src = "\
fn a(x: bool) -> i32:
    if x:
        return 1
    else:
        return 2
fn b() -> i32:
    while true:
        while true:
            break
fn c(x: bool) -> i32:
    if x:
        return 1
fn d() -> i32:
    while true:
        if true:
            break
fn e():
    pass
";
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::MissingReturn("c".into()),
                TypeErrorKind::MissingReturn("d".into())
            ]
        );
        let module = lower(&src[..src.find("fn c").unwrap()]);
        assert_eq!(
            body(&module, "a"),
            "(if x (then (return 1)) (else (return 2))) unreachable"
        );
        assert_eq!(
            body(&module, "b"),
            "(block (loop (block (loop (br 1) (br 0))) (br 0))) unreachable"
        );
    }

    #[test]
    fn locals_are_block_scoped_and_shadow() {
        let src = "\
fn f(x: i32) -> i32:
    let y = x
    if true:
        let y = y + 1
        let x = true
    let x = x + 1
    return y + x
";
        let module = lower(src);
        let names: Vec<_> = module.funcs[0].locals.iter().map(|l| &l.name[..]).collect();
        assert_eq!(names, vec!["x", "y", "y", "x", "x"]);
        let [.., set_x, Stmt::Return(ret)] = &module.funcs[0].body[..] else {
            panic!()
        };
        let local = |i| Box::new(Expr::Local(ir::LocalId(i)));
        let add = |a, b| Expr::Binary(ValType::I32, ir::BinOp::Add, a, b);
        let one = Box::new(Expr::Const(Const::I32(1)));
        assert_eq!(*set_x, Stmt::SetLocal(ir::LocalId(4), add(local(0), one)));
        assert_eq!(*ret, vec![add(local(1), local(4))]);
        let Stmt::If { then_body, .. } = &module.funcs[0].body[1] else {
            panic!()
        };
        let one = Box::new(Expr::Const(Const::I32(1)));
        assert_eq!(
            then_body[0],
            Stmt::SetLocal(ir::LocalId(2), add(local(1), one))
        );
    }

    fn mismatch(expected: &str, found: &str) -> TypeErrorKind {
        TypeErrorKind::Mismatch {
            expected: expected.into(),
            found: found.into(),
        }
    }

    fn invalid_operand(op: &'static str, ty: &str) -> TypeErrorKind {
        TypeErrorKind::InvalidOperand { op, ty: ty.into() }
    }

    #[test]
    fn imports_share_the_item_namespace() {
        use TypeErrorKind::*;
        let src = "\
fn a():
    pass
extern:
    fn a()
    fn b(x: i32, x: Nope)
    fn b() = \"b2\"
    fn c(x: i32)
fn f():
    c(y: 1)
";
        let errors = check_src(src).unwrap_err();
        let kinds: Vec<_> = errors.iter().map(|e| e.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                DuplicateItem("a".into()),
                DuplicateItem("b".into()),
                DuplicateParam("x".into()),
                UnknownType("Nope".into()),
                UnknownLabel("y".into()),
                MissingArg("x".into()),
            ]
        );
        // The later declaration, the import, is the duplicate.
        assert_eq!(
            errors[0].span.unwrap().start,
            src.find("a()\n    fn b").unwrap()
        );
    }

    #[test]
    fn name_errors() {
        use TypeErrorKind::*;
        let src = "\
struct P:
    x: i32
    x: i32
struct A:
    b: B
struct B:
    a: A
fn f(a: i32, a: i32, t: Foo):
    let b = y + 1
    let c = f
    a()
    f = 1
    f().x = 2
    let d = a.x
fn P():
    pass
";
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("P".into()),
                DuplicateField("x".into()),
                RecursiveStruct("B".into()),
                DuplicateParam("a".into()),
                UnknownType("Foo".into()),
                UnknownName("y".into()),
                NotAValue("f".into()),
                NotCallable("a".into()),
                NotAssignable,
                MissingArg("a".into()),
                MissingArg("a".into()),
                MissingArg("t".into()),
                NotAssignable,
                NoField {
                    ty: "i32".into(),
                    field: "x".into()
                },
            ]
        );
    }

    #[test]
    fn type_errors() {
        use TypeErrorKind::*;
        let src = "\
struct P:
    x: i32
fn f(a: u32, p: P) -> i32:
    let b = -a
    let c = 1.0 % 2.0
    let d = true + true
    let g = 1 as bool
    let h = p as i32
    let i: u8 = 256
    let j: i8 = -129
    let k: u8 = -1
    if 1:
        return
    return true
";
        assert_eq!(
            errors(src),
            vec![
                invalid_operand("-", "u32"),
                invalid_operand("%", "f64"),
                invalid_operand("+", "bool"),
                InvalidCast {
                    from: "i32".into(),
                    to: "bool".into()
                },
                InvalidCast {
                    from: "P".into(),
                    to: "i32".into()
                },
                IntOutOfRange("u8".into()),
                IntOutOfRange("i8".into()),
                invalid_operand("-", "u8"),
                mismatch("bool", "i32"),
                mismatch("i32", "tuple()"),
                mismatch("i32", "bool"),
            ]
        );
    }

    #[test]
    fn argument_errors() {
        use TypeErrorKind::*;
        let src = "\
struct P:
    x: i32
    y: i32
fn g(a: i32, b: i32):
    pass
fn f():
    g(1)
    g(1, 2, 3, 4)
    g(1, c: 2)
    g(a: 1, 2)
    g(1, a: 2)
    let p = P(1, y: 2)
    let q = P(x: 1, y: true)
";
        assert_eq!(
            errors(src),
            vec![
                MissingArg("b".into()),
                TooManyArgs {
                    expected: 2,
                    found: 4
                },
                UnknownLabel("c".into()),
                MissingArg("b".into()),
                PositionalAfterLabel,
                MissingArg("b".into()),
                DuplicateArg("a".into()),
                MissingArg("b".into()),
                UnlabelledField,
                MissingArg("x".into()),
                mismatch("i32", "bool"),
            ]
        );
    }

    #[test]
    fn statement_errors() {
        use TypeErrorKind::*;
        let src = "\
fn f(a: i32):
    a = 1
    let b = 1
    b += 1
    break
    continue
    for x in [1]:
        pass
    let s = \"hi\"
    let l: array(i32) = a
";
        assert_eq!(
            errors(src),
            vec![
                ImmutableAssign("a".into()),
                ImmutableAssign("b".into()),
                BreakOutsideLoop,
                ContinueOutsideLoop,
                LiteralOutsideGlobal,
                LiteralOutsideGlobal,
                mismatch("array(i32)", "i32"),
            ]
        );
    }

    #[test]
    fn side_effects_are_kept_in_order() {
        let src = "\
var g = 0
struct P:
    x: i32
    y: i32
fn tick() -> i32:
    g += 1
    return g
fn make() -> P:
    return P(x: 1, y: 2)
fn unit():
    pass
fn f(b: bool) -> i32:
    unit()
    tick()
    let a = P(x: 1, y: tick()).x
    let c = g + make().x
    let d = b and make().y == 2
    return a
";
        assert_eq!(
            body(&lower(src), "f"),
            "(call unit [] -> []) (drop (call tick )) \
             (set tmp1 (call tick )) (set a 1) \
             (set tmp5 @g) (call make [] -> [tmp3 tmp4]) (set c (I32.Add tmp5 tmp3)) \
             (set d (if b (seq (call make [] -> [tmp7 tmp8]) (I32.Eq tmp8 2)) 0)) \
             (return a)"
        );
    }

    #[test]
    fn reordered_pure_arguments_stay_constant() {
        let src = "\
struct P:
    x: f32
    y: f32
let g: f32 = 1.0
let p = P(y: g, x: 2.0)
";
        let inits: Vec<_> = lower(src).globals.iter().map(|g| konst(g.init)).collect();
        assert_eq!(inits, vec!["1f32", "2f32", "1f32", "0"]);
    }

    #[test]
    fn unit_is_a_primitive_without_storage() {
        let src = "\
fn u():
    pass
fn g(a: tuple(), b: i32) -> tuple():
    return a
fn f() -> i32:
    let x: tuple() = u()
    let y = g(x, 1)
    return 1
";
        let module = lower(src);
        assert_eq!(module.funcs[1].params, vec![ValType::I32]);
        assert_eq!(module.funcs[1].results, vec![]);
        assert_eq!(body(&module, "g"), "(return )");
        assert_eq!(
            body(&module, "f"),
            "(call u [] -> []) (call g [1] -> []) (return 1)"
        );
        assert_eq!(
            errors("fn u():\n    let b = 1 as tuple()\n    let c = -u()\n"),
            vec![
                TypeErrorKind::InvalidCast {
                    from: "i32".into(),
                    to: "tuple()".into()
                },
                invalid_operand("-", "tuple()"),
            ]
        );
    }

    #[test]
    fn unit_literals() {
        let src = "\
let g = ()
fn u() -> tuple():
    return ()
fn f():
    let a = ()
    let b: tuple() = a
    return b
";
        let module = lower(src);
        let globals: Vec<_> = module.globals.iter().map(|g| g.name.as_str()).collect();
        assert_eq!(globals, ["data_end"]);
        assert!(module.funcs[1].locals.is_empty());
        assert_eq!(body(&module, "u"), "(return )");
        assert_eq!(body(&module, "f"), "(return )");
        assert_eq!(
            errors("fn f():\n    let b: i32 = ()\n    let c: unit = ()\n"),
            vec![
                mismatch("i32", "tuple()"),
                TypeErrorKind::UnknownType("unit".into()),
            ]
        );
    }

    #[test]
    fn pub_globals_are_exported() {
        let src = "\
pub struct P:
    x: i32
    y: i32
pub let a = 1
pub var origin = P(x: 0, y: 0)
let hidden = 2
";
        let exports: Vec<_> = lower(src)
            .globals
            .into_iter()
            .map(|g| (g.name, g.export))
            .collect();
        let named = |name: &str| (name.to_string(), Some(name.to_string()));
        assert_eq!(
            exports,
            vec![
                named("a"),
                named("origin.x"),
                named("origin.y"),
                ("hidden".to_string(), None),
                named("data_end"),
            ]
        );
    }

    #[test]
    fn pointers_are_i32_addresses() {
        let src = "\
pub struct P:
    x: f64
var null = 0 as &u32
let top = 4294967295 as &&P
pub fn f(p: &P, a: u32, n: i32) -> &u32:
    let q = a as &P
    let b = p as u32
    let s = p as i32
    let c = p as &u32
    let d = p == q
    let e = p != q
    let g = p < q
    let h = p >= q
    let r = n as &P
    return c
";
        let module = lower(src);
        assert_eq!(
            module.memory,
            ir::Memory {
                min_pages: 1,
                max_pages: None,
                export: "memory".to_string()
            }
        );
        let globals: Vec<_> = module.globals.iter().map(|g| (g.ty, g.init)).collect();
        assert_eq!(
            globals,
            vec![
                (ValType::I32, Const::I32(0)),
                (ValType::I32, Const::I32(-1)),
                (ValType::I32, Const::I32(0)),
            ]
        );
        assert_eq!(
            module.funcs[0].params,
            vec![ValType::I32, ValType::I32, ValType::I32]
        );
        assert_eq!(module.funcs[0].results, vec![ValType::I32]);
        assert_eq!(
            body(&module, "f"),
            "(set q a) (set b p) (set s p) (set c p) (set d (I32.Eq p q)) (set e (I32.Ne p q)) \
             (set g (I32.LtU p q)) (set h (I32.GeU p q)) (set r n) (return c)"
        );
        let src = "\
fn f(p: &u8, q: &i8, a: i64):
    let b = p as &i8 == q
    let c = p == q
    let d = p < q
    let e = p + 1
    let g = a as &u8
    let i = p as u64
";
        let cast = |from: &str, to: &str| TypeErrorKind::InvalidCast {
            from: from.into(),
            to: to.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                mismatch("&u8", "&i8"),
                mismatch("&u8", "&i8"),
                invalid_operand("+", "&u8"),
                cast("i64", "&u8"),
                cast("&u8", "u64"),
            ]
        );
    }

    #[test]
    fn reads_through_pointers_load_from_c_layout() {
        let src = "\
struct Inner:
    a: u8
    b: f64
struct S:
    flag: bool
    n: i16
    inner: Inner
    next: &S
    k: i8
    u: u16
fn f(p: &S, q: &tuple()) -> f64:
    let flag = p.flag
    let n = p.n
    let b = p.inner.b
    let k = p.next.k
    let u = p.u
    let s = p.next.*
    let v = q.*
    return p.*.inner.b
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set flag (I32.Ne (I32.Load8U offset=0 p) 0)) \
             (set n (I32.Load16S offset=2 p)) \
             (set b (F64.Load offset=16 p)) \
             (set k (I32.Load8S offset=28 (I32.Load offset=24 p))) \
             (set u (I32.Load16U offset=30 p)) \
             (set tmp7 (I32.Load offset=24 p)) \
             (set s.flag (I32.Ne (I32.Load8U offset=0 tmp7) 0)) \
             (set s.n (I32.Load16S offset=2 tmp7)) \
             (set s.inner.a (I32.Load8U offset=8 tmp7)) \
             (set s.inner.b (F64.Load offset=16 tmp7)) \
             (set s.next (I32.Load offset=24 tmp7)) \
             (set s.k (I32.Load8S offset=28 tmp7)) \
             (set s.u (I32.Load16U offset=30 tmp7)) \
             (return (F64.Load offset=16 p))"
        );
        let src = "\
struct S:
    x: i32
    next: &&S
fn f(p: &&&S) -> i32:
    let a = p.x
    let b = p.*.x
    return p.next.x
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set a (I32.Load offset=0 (I32.Load offset=0 (I32.Load offset=0 p)))) \
             (set b (I32.Load offset=0 (I32.Load offset=0 (I32.Load offset=0 p)))) \
             (return (I32.Load offset=0 (I32.Load offset=0 (I32.Load offset=4 \
             (I32.Load offset=0 (I32.Load offset=0 p))))))"
        );
        let src = "\
struct S:
    x: i32
fn f(p: &&S, q: &&i32, a: i32):
    let b = p.y
    let c = q.x
    let d = a.*
";
        let no_field = |ty: &str, field: &str| TypeErrorKind::NoField {
            ty: ty.into(),
            field: field.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                no_field("S", "y"),
                no_field("i32", "x"),
                invalid_operand(".*", "i32"),
            ]
        );
    }

    #[test]
    fn writes_through_pointers_store_left_to_right() {
        let src = "\
struct P:
    x: i32
    y: u8
    z: i64
var q = 0 as &P
fn make() -> P:
    return P(x: 1, y: 2, z: 3)
fn tick() -> i32:
    return 1
fn f(p: &P, pp: &&P):
    p.x = 1
    p.y += 1
    p.z = 5
    p.* = P(x: p.y as i32, y: 3, z: 6)
    pp.*.x = tick()
    p.x += tick()
    p.x += make().x
    q.x = 1
    pp.z = 2
";
        assert_eq!(
            body(&lower(src), "f"),
            "(I32.Store offset=0 p 1) \
             (I32.Store8 offset=4 p (I32.And (I32.Add (I32.Load8U offset=4 p) 1) 255)) \
             (I64.Store offset=8 p 5i64) \
             (set tmp2 (I32.Load8U offset=4 p)) \
             (I32.Store offset=0 p tmp2) (I32.Store8 offset=4 p 3) (I64.Store offset=8 p 6i64) \
             (set tmp3 (I32.Load offset=0 pp)) (I32.Store offset=0 tmp3 (call tick )) \
             (I32.Store offset=0 p (I32.Add (I32.Load offset=0 p) (call tick ))) \
             (set tmp7 (I32.Load offset=0 p)) (call make [] -> [tmp4 tmp5 tmp6]) \
             (I32.Store offset=0 p (I32.Add tmp7 tmp4)) \
             (set tmp8 @q) (I32.Store offset=0 tmp8 1) \
             (set tmp9 (I32.Load offset=0 pp)) (I64.Store offset=8 tmp9 2i64)"
        );
    }

    #[test]
    fn address_of_memory_behind_a_pointer() {
        let src = "\
struct Node:
    val: i32
    pair: Pair
    next: &Node
struct Pair:
    a: u8
    b: i64
fn f(n: &Node, nn: &&Node) -> &i64:
    let p = &n.pair.b
    let q = &n.*
    let r = &n.next.val
    let s = &n.*.pair
    let t = &nn.pair
    return p
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set p (I32.Add n 16)) (set q n) \
             (set tmp4 (I32.Load offset=24 n)) (set r tmp4) \
             (set s (I32.Add n 8)) \
             (set tmp7 (I32.Load offset=0 nn)) (set t (I32.Add tmp7 8)) (return p)"
        );
        let src = "\
struct P:
    x: i32
var g = P(x: 1)
fn f(a: i32, p: P, pp: &&P):
    let b = &a
    let c = &p.x
    let d = &g.x
    let e = &(a + 1)
    let h: &i32 = &pp.*
    a.* = 1
";
        use TypeErrorKind::*;
        assert_eq!(
            errors(src),
            vec![
                NotAddressable,
                NotAddressable,
                NotAddressable,
                NotAddressable,
                mismatch("&i32", "&&P"),
                invalid_operand(".*", "i32"),
            ]
        );
    }

    fn check_start(src: &str, start: &str) -> Result<Module, Vec<TypeError>> {
        let settings = Settings {
            start: Some(start.to_string()),
            ..Settings::default()
        };
        check_with(src, &settings)
    }

    #[test]
    fn start_function() {
        let src = "\
extern:
    fn ready()
    fn get() -> i32
struct S:
    x: i32
let g = 1
fn init():
    ready()
fn take(x: i32):
    pass
fn give() -> tuple():
    return
fn back() -> i32:
    return 1
fn(T) generic():
    pass
";
        let start = |name| check_start(src, name).map(|m| m.start);
        assert_eq!(start("init"), Ok(Some(FuncId(2))));
        assert_eq!(start("ready"), Ok(Some(FuncId(0))));
        assert_eq!(start("give"), Ok(Some(FuncId(4))));
        assert_eq!(lower(src).start, None);

        for name in ["nope", "S", "g"] {
            assert_eq!(
                start(name),
                Err(vec![TypeError {
                    kind: TypeErrorKind::UnknownStart(name.into()),
                    span: None,
                    instances: Vec::new(),
                }])
            );
        }
        for name in ["take", "back", "get", "generic"] {
            let errors = start(name).unwrap_err();
            assert_eq!(errors.len(), 1, "{errors:?}");
            assert_eq!(errors[0].kind, TypeErrorKind::InvalidStart(name.into()));
            let span = errors[0].span.unwrap();
            assert_eq!(&src[span.start..span.end], name);
        }
    }

    #[test]
    fn memory_export_name_is_reserved() {
        let src = "\
pub fn memory():
    pass
pub let memory = 1
let hidden = 2
fn f():
    let memory = 3
";
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::ReservedExport("memory".into()),
                TypeErrorKind::DuplicateItem("memory".into()),
                TypeErrorKind::ReservedExport("memory".into()),
            ]
        );
    }

    #[test]
    fn narrow_shift_amounts_wrap_at_their_width() {
        let src = "\
let g: u8 = 1 << 9
fn f(a: i16, b: i16, c: u8, d: i32):
    let s = a << b
    let t = c >> 9
    let u = a >> b
    let v = d << d
";
        let module = lower(src);
        assert_eq!(module.globals[0].init, Const::I32(2));
        assert_eq!(
            body(&module, "f"),
            "(set s (I32.Extend16S (I32.Shl a (I32.And b 15)))) \
             (set t (I32.ShrU c 1)) \
             (set u (I32.ShrS a (I32.And b 15))) \
             (set v (I32.Shl d d))"
        );
    }

    #[test]
    fn externrefs_pass_through_locals_and_structs() {
        let src = "\
pub struct Handle:
    el: externref
    id: i32
extern:
    fn get(id: i32) -> externref
    fn put(el: externref)
    fn wrap(h: Handle) -> Handle
pub fn f(a: externref) -> Handle:
    var b = get(1)
    put(b)
    b = a
    let h = wrap(Handle(el: b, id: 2))
    return Handle(el: h.el, id: 3)
";
        let module = lower(src);
        assert_eq!(module.imports[0].results, vec![ValType::ExternRef]);
        assert_eq!(
            module.imports[2].params,
            vec![ValType::ExternRef, ValType::I32]
        );
        assert_eq!(module.funcs[0].params, vec![ValType::ExternRef]);
        assert_eq!(
            module.funcs[0].results,
            vec![ValType::ExternRef, ValType::I32]
        );
        assert_eq!(
            body(&module, "f"),
            "(set b (call get 1)) (call put [b] -> []) (set b a) \
             (call wrap [b 2] -> [tmp2 tmp3]) (set h.el tmp2) (set h.id tmp3) \
             (return h.el 3)"
        );
    }

    #[test]
    fn externrefs_are_opaque_and_never_in_memory() {
        let src = "\
struct S:
    e: externref
struct T:
    p: &&S
    q: &U
    r: &T
struct U:
    s: S
extern:
    fn get() -> externref
let g = get()
fn f(a: externref, p: &externref):
    let b = a == a
    let c = a + a
    let d = -a
    let e: externref = 0
    let h = a as i32
    let i = 0 as externref
    let j = 1 as &S
";
        let cast = |from: &str, to: &str| TypeErrorKind::InvalidCast {
            from: from.into(),
            to: to.into(),
        };
        let not_storable = |ty: &str| TypeErrorKind::NotStorable(ty.into());
        assert_eq!(
            errors(src),
            vec![
                not_storable("S"),
                not_storable("U"),
                not_storable("externref"),
                TypeErrorKind::NotConstant,
                invalid_operand("==", "externref"),
                invalid_operand("+", "externref"),
                invalid_operand("-", "externref"),
                mismatch("externref", "i32"),
                cast("externref", "i32"),
                cast("i32", "externref"),
                not_storable("S"),
            ]
        );
    }

    #[test]
    fn tuples_are_split_into_scalars() {
        let src = "\
fn swap(t: tuple(i32, f64)) -> tuple(f64, i32):
    return (t.1, t.0)

fn f() -> f64:
    let t: tuple(u8, f64) = (1, 2)
    let u = swap((3, 4.5))
    var v = ((1, 2), 3)
    v.0.1 = u.1
    v = ((v.1, 5), 6)
    return u.0 + t.1
";
        let module = lower(src);
        let swap = &module.funcs[0];
        assert_eq!(swap.params, vec![ValType::I32, ValType::F64]);
        assert_eq!(swap.results, vec![ValType::F64, ValType::I32]);
        assert_eq!(body(&module, "swap"), "(return t.1 t.0)");
        assert_eq!(
            body(&module, "f"),
            "(set t.0 1) (set t.1 2f64) \
             (call swap [3 4.5f64] -> [tmp2 tmp3]) (set u.0 tmp2) (set u.1 tmp3) \
             (set v.0.0 1) (set v.0.1 2) (set v.1 3) \
             (set v.0.1 u.1) \
             (set tmp9 v.1) (set v.0.0 tmp9) (set v.0.1 5) (set v.1 6) \
             (return (F64.Add u.0 t.1))"
        );
    }

    #[test]
    fn tuple_types_are_structural() {
        let src = "\
struct P:
    x: i32
    y: i32
fn make() -> tuple(i32, P):
    return (1, P(x: 2, y: 3))
fn take(t: tuple(i32, P)) -> i32:
    return t.1.y
fn f() -> i32:
    let t: tuple(i32, P) = make()
    return take(t) + take(make())
";
        lower(src);
    }

    #[test]
    fn destructuring_binds_each_name() {
        let src = "\
extern:
    fn pair() -> tuple(i32, i64)
    fn one() -> i32
fn f() -> i64:
    let (a, b) = pair()
    let ((c, _), d) = ((one(), one()), 1 as i64)
    var (e, g): tuple(u8, u8) = (1, 2)
    e += g
    let () = ()
    let _ = one()
    return b + d + (a + c + e as i32) as i64
";
        assert_eq!(
            body(&lower(src), "f"),
            "(call pair [] -> [tmp0 tmp1]) (set a tmp0) (set b tmp1) \
             (set c (call one )) (drop (call one )) (set d (I32.ExtendS 1)) \
             (set e 1) (set g 2) \
             (set e (I32.And (I32.Add e g) 255)) \
             (drop (call one )) \
             (return (I64.Add (I64.Add b d) \
             (I32.ExtendS (I32.Add (I32.Add a c) e))))"
        );
    }

    #[test]
    fn destructured_globals_are_separate() {
        let src = "\
pub let (w, h) = (640, 480)
pub let pos = (w, (h, 1.5))
let (_, hidden) = (1, pos.1.1)
";
        let globals: Vec<_> = lower(src)
            .globals
            .into_iter()
            .map(|g| (g.name, g.export.is_some(), g.init))
            .collect();
        let global = |name: &str, export, init| (name.to_string(), export, init);
        assert_eq!(
            globals,
            vec![
                global("w", true, Const::I32(640)),
                global("h", true, Const::I32(480)),
                global("pos.0", true, Const::I32(640)),
                global("pos.1.0", true, Const::I32(480)),
                global("pos.1.1", true, Const::F64(1.5)),
                global("hidden", false, Const::F64(1.5)),
                global("data_end", true, Const::I32(0)),
            ]
        );
    }

    #[test]
    fn tuples_behind_pointers_use_c_layout() {
        let src = "\
fn f(p: &tuple(u8, tuple(f64, i16)), q: &&tuple(i32, i32)) -> &i16:
    let a = p.0
    let b = p.1.1
    p.1.0 = 2.0
    q.1 = 3
    let (c, d) = q.*.*
    return &p.1.1
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set a (I32.Load8U offset=0 p)) \
             (set b (I32.Load16S offset=16 p)) \
             (F64.Store offset=8 p 2f64) \
             (set tmp4 (I32.Load offset=0 q)) (I32.Store offset=4 tmp4 3) \
             (set tmp5 (I32.Load offset=0 q)) \
             (set c (I32.Load offset=0 tmp5)) (set d (I32.Load offset=4 tmp5)) \
             (return (I32.Add p 16))"
        );
    }

    #[test]
    fn tuple_errors() {
        use TypeErrorKind::*;
        let src = "\
struct A:
    t: tuple(i32, A)
struct B:
    p: &tuple(externref, i32)
fn f(t: tuple(i32, f32)) -> tuple(i32, i32):
    let x = t.2
    let y = t.x
    let (a, b, c) = t
    let (d, e) = 1
    let (g, g) = t
    let w = t as tuple(i32, i32)
    t.0 = 1
    return (1, 2.0)
";
        let mismatch = |expected: &str, found: &str| Mismatch {
            expected: expected.into(),
            found: found.into(),
        };
        let no_field = |field: &str| NoField {
            ty: "tuple(i32, f32)".into(),
            field: field.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                RecursiveStruct("A".into()),
                NotStorable("tuple(externref, i32)".into()),
                no_field("2"),
                no_field("x"),
                mismatch("tuple(_, _, _)", "tuple(i32, f32)"),
                mismatch("tuple(_, _)", "i32"),
                DuplicateBinding("g".into()),
                InvalidCast {
                    from: "tuple(i32, f32)".into(),
                    to: "tuple(i32, i32)".into()
                },
                ImmutableAssign("t".into()),
                mismatch("tuple(i32, i32)", "tuple(i32, f64)"),
            ]
        );
    }

    #[test]
    fn generic_fns_are_instantiated_per_inferred_type_argument() {
        let src = "\
fn(T) id(val: T) -> T:
    return val
fn f(x: u8, y: &i32) -> u8:
    id(y)
    id(x)
    return id(x)
";
        let module = lower(src);
        let names: Vec<_> = module.funcs.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(names, vec!["f", "id(&i32)", "id(u8)"]);
        assert_eq!(
            body(&module, "f"),
            "(drop (call id(&i32) y)) (drop (call id(u8) x)) (return (call id(u8) x))"
        );
        assert_eq!(body(&module, "id(u8)"), "(return val)");
    }

    #[test]
    fn literals_take_the_type_arguments_other_arguments_settle() {
        let src = "\
fn(T) max(a: T, b: T) -> T:
    return a
fn f(x: u8) -> u8:
    max(1.5, 2)
    max(1, 2)
    return max(1, x)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(drop (call max(f64) 1.5f64 2f64)) (drop (call max(i32) 1 2)) \
             (return (call max(u8) 1 x))"
        );
    }

    #[test]
    fn type_arguments_are_inferred_from_within_argument_types() {
        let src = "\
struct(T) Box:
    value: T
fn(T) first(xs: array(T)) -> T:
    return xs[0]
fn(A, B) swap(p: &tuple(A, B), b: Box(B)) -> tuple(B, A):
    return (b.value, p.*.0)
fn f(xs: array(u16), p: &tuple(u8, bool)) -> tuple(bool, u8):
    first(xs)
    return swap(p, Box(bool)(value: true))
";
        let module = lower(src);
        let names: Vec<_> = module.funcs.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(names, vec!["f", "first(u16)", "swap(u8, bool)"]);
    }

    #[test]
    fn type_arguments_can_be_given_explicitly() {
        let src = "\
fn(T) id(val: T) -> T:
    return val
fn(T) zero() -> T:
    return 0 as T
fn f() -> u8:
    id(i64)(1)
    return zero(u8)()
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(drop (call id(i64) 1i64)) (return (call zero(u8) ))"
        );
        assert_eq!(
            errors(
                "\
fn(A, B) pair(a: A, b: B):
    pass
fn g(x: i32):
    pass
fn f():
    pair(i32)(1, 2)
    g(i32)(1)
    pair(i32, 1)(1, 2)
    pair(i32, b: u8)(1, 2)
"
            ),
            vec![
                TypeErrorKind::TypeArgCount {
                    name: "pair".to_string(),
                    expected: 2,
                    found: 1
                },
                TypeErrorKind::NotGeneric("g".to_string()),
                TypeErrorKind::NotAType,
                TypeErrorKind::LabelledTypeArg,
            ]
        );
    }

    #[test]
    fn type_arguments_no_argument_settles_are_reported() {
        let src = "\
fn(T, U) make(x: T) -> U:
    return x as U
fn(T) max(a: T, b: T) -> T:
    return a
fn f(x: u8, y: i32):
    make(x)
    max(x, y)
    max(x, 1.5)
";
        let errors = check_src(src).unwrap_err();
        let kinds: Vec<_> = errors.iter().map(|e| e.kind.clone()).collect();
        assert_eq!(
            kinds,
            vec![
                TypeErrorKind::CannotInfer {
                    func: "make".to_string(),
                    param: "U".to_string()
                },
                TypeErrorKind::Mismatch {
                    expected: "u8".to_string(),
                    found: "i32".to_string()
                },
                TypeErrorKind::Mismatch {
                    expected: "u8".to_string(),
                    found: "f64".to_string()
                },
            ]
        );
        let span = errors[0].span.unwrap();
        assert_eq!(&src[span.start..span.end], "make(x)");
        let span = errors[1].span.unwrap();
        assert_eq!(&src[span.start..span.end], "y");
    }

    #[test]
    fn pub_generic_fns_are_not_exported() {
        let module = lower(
            "pub fn(T) id(val: T) -> T:\n    return val\npub fn f() -> i32:\n    return id(1)\n",
        );
        let exports: Vec<_> = module
            .funcs
            .iter()
            .filter_map(|f| f.export.as_deref())
            .collect();
        assert_eq!(exports, ["f"]);
    }

    #[test]
    fn type_parameters_name_their_type_arguments_in_instances() {
        let src = "\
struct Point:
    x: u8
    y: u8
struct(T) Box:
    value: T
enum(i8) Code:
    ok
    bad
fn(T) sized(x: T) -> u32:
    let y: T = x
    let b = Box(T)(value: y)
    return T.size + (&T).size
fn(T) make(v: u8) -> T:
    return T(x: v, y: v)
fn(T) last() -> T:
    return T.bad
fn f():
    sized(1 as u16)
    make(Point)(1)
    last(Code)()
";
        let module = lower(src);
        assert_eq!(
            body(&module, "sized(u16)"),
            "(set y x) (set b.value y) (return (I32.Add 2 4))"
        );
        assert_eq!(body(&module, "make(Point)"), "(return v v)");
        assert_eq!(body(&module, "last(Code)"), "(return 1)");
    }

    #[test]
    fn errors_in_instances_name_the_instances_they_are_in() {
        let src = "\
fn(T) add(a: T, b: T) -> T:
    return a + b
fn(T) twice(x: T) -> T:
    return add(x, x)
fn(T) unused(x: T):
    nope()
fn f():
    twice(true)
    twice(false)
";
        let errors = check_src(src).unwrap_err();
        assert_eq!(errors.len(), 1, "{errors:#?}");
        let span = errors[0].span.unwrap();
        assert_eq!(&src[span.start..span.end], "a + b");
        let instances: Vec<_> = errors[0]
            .instances
            .iter()
            .map(|site| (site.name.as_str(), &src[site.call.start..site.call.end]))
            .collect();
        assert_eq!(
            instances,
            vec![("add(bool)", "add(x, x)"), ("twice(bool)", "twice(true)")]
        );
    }

    #[test]
    fn generic_fns_must_have_finitely_many_instances() {
        let src = "\
fn(T) deep(x: T):
    deep((x, 1))
fn(T) wide(x: T):
    wide((x, x))
fn(T) fine(x: T, n: i32):
    if n > 0:
        fine(x, n - 1)
        fine(1 as u8, n - 1)
fn f():
    deep(1)
    wide(1)
    fine(1, 5)
";
        let errors = check_src(src).unwrap_err();
        let mut kinds: Vec<_> = errors.iter().map(|e| e.kind.clone()).collect();
        kinds.sort_by_key(|kind| format!("{kind:?}"));
        assert_eq!(
            kinds,
            vec![
                TypeErrorKind::InstanceTooDeep("deep".to_string()),
                TypeErrorKind::InstanceTooLarge("wide".to_string()),
            ]
        );
        for error in &errors {
            let span = error.span.unwrap();
            assert!(["deep((x, 1))", "wide((x, x))"].contains(&&src[span.start..span.end]));
        }
        let deep = errors
            .iter()
            .find(|e| e.kind == TypeErrorKind::InstanceTooDeep("deep".to_string()))
            .unwrap();
        assert_eq!(deep.instances.len(), generic_fn::MAX_INSTANCE_DEPTH);
    }

    #[test]
    fn generic_fn_signatures_are_checked_without_calls() {
        use TypeErrorKind::*;
        let src = "\
struct S:
    x: i32
fn g():
    pass
fn(T, T) a(x: T):
    pass
fn(S) b():
    pass
fn(g) c():
    pass
fn(i32) d():
    pass
fn(T) e(x: Nope) -> T:
    return nope
";
        assert_eq!(
            errors(src),
            vec![
                DuplicateParam("T".to_string()),
                DuplicateItem("S".to_string()),
                DuplicateItem("g".to_string()),
                DuplicateItem("i32".to_string()),
                UnknownType("Nope".to_string()),
            ]
        );
    }

    #[test]
    fn instances_cannot_point_to_what_memory_cannot_hold() {
        let src = "\
fn(T) f(p: &T):
    pass
fn(T) g() -> array(T):
    return g(T)()
fn h():
    f(externref)(0)
    g(externref)()
";
        let errors = check_src(src).unwrap_err();
        let found: Vec<_> = errors
            .iter()
            .map(|e| {
                (
                    e.kind.clone(),
                    &src[e.span.unwrap().start..e.span.unwrap().end],
                )
            })
            .collect();
        let not_storable = TypeErrorKind::NotStorable("externref".to_string());
        assert_eq!(
            found,
            vec![
                (not_storable.clone(), "f(externref)(0)"),
                (not_storable, "g(externref)()"),
            ]
        );
    }

    #[test]
    fn type_arguments_are_not_reported_after_the_errors_that_hide_them() {
        use TypeErrorKind::*;
        let src = "\
struct(T) Box:
    value: T
fn(T) id(val: T) -> T:
    return val
fn(T) g(b: Box(Nope)) -> T:
    return b.value
fn f():
    id(nope)
    id()
    g(1)
";
        assert_eq!(
            errors(src),
            vec![
                UnknownType("Nope".to_string()),
                UnknownName("nope".to_string()),
                MissingArg("val".to_string()),
            ]
        );
    }

    #[test]
    fn generic_structs_are_instantiated_per_type_argument() {
        let src = "\
struct(T) Box:
    value: T
struct(A, B) Pair:
    a: A
    b: Box(B)
fn f(x: Box(i32)) -> Pair(f64, u8):
    let b: Box(i32) = Box(i32)(value: 1)
    let c: Box(i32) = x
    return Pair(f64, u8)(a: 2.0, b: Box(u8)(value: 3))
fn g(p: &Pair(u8, i64)) -> i64:
    return p.b.value
";
        let module = lower(src);
        assert_eq!(body(&module, "g"), "(return (I64.Load offset=8 p))");
        let f = &module.funcs[0];
        assert_eq!(f.params, [ValType::I32]);
        assert_eq!(f.results, [ValType::F64, ValType::I32]);
        assert_eq!(f.locals[0].name, "x.value");
        assert_eq!(
            body(&module, "f"),
            "(set b.value 1) (set c.value x.value) (return 2f64 3)"
        );
        assert_eq!(
            errors("struct(T) Box:\n    value: T\nfn f(x: Box(i32)) -> Box(u8):\n    return x\n"),
            vec![mismatch("Box(u8)", "Box(i32)")]
        );
    }

    #[test]
    fn type_arguments_must_match_type_parameters() {
        use TypeErrorKind::*;
        let src = "\
struct(T) Box:
    value: T
struct P:
    x: i32
struct(T, T, P, i32) Bad:
    pass
struct array:
    pass
struct(T) Wrap:
    w: T()
fn f(a: Box, b: P(i32), c: Box(i32, u8), d: array, e: i32(u8)):
    let g = Box(i32)
    let h = Box(value: 1)
    let i = Box(T: i32)(value: 1)
    let j = Box(1)(value: 1)
    let k = array
    let l = Box(T: i32)
    let m = P(x: 1)(x: 2)
fn g(a: i32(), b: P(), c: Box(), d: array(), e: Foo(), f: Foo):
    pass
";
        let count = |name: &str, expected, found| TypeArgCount {
            name: name.into(),
            expected,
            found,
        };
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("array".into()),
                DuplicateParam("T".into()),
                DuplicateItem("P".into()),
                DuplicateItem("i32".into()),
                NotGeneric("T".into()),
                MissingTypeArgs("Box".into()),
                NotGeneric("P".into()),
                count("Box", 1, 2),
                MissingTypeArgs("array".into()),
                NotGeneric("i32".into()),
                NotGeneric("i32".into()),
                NotGeneric("P".into()),
                count("Box", 1, 0),
                count("array", 1, 0),
                UnknownType("Foo".into()),
                UnknownType("Foo".into()),
                MissingTypeArgs("Box".into()),
                LabelledTypeArg,
                NotAType,
                MissingTypeArgs("array".into()),
                MissingTypeArgs("Box".into()),
                NotCallable("expression".into()),
            ]
        );
        assert_eq!(
            count("Box", 1, 0).to_string(),
            "`Box` takes 1 type argument, found 0"
        );
        assert_eq!(
            NotGeneric("i32".into()).to_string(),
            "`i32` has no type parameters"
        );
        assert_eq!(
            MissingTypeArgs("Box".into()).to_string(),
            "`Box` needs a list of type arguments"
        );
    }

    #[test]
    fn generic_declarations_report_errors_once_and_uses_report_their_own() {
        let src = "\
struct(T) Box:
    value: T
    other: Missing
struct(T) Ptr:
    p: &T
struct Holder:
    h: Ptr(externref)
fn f(a: Ptr(tuple(externref, i32)), b: &Box(externref), c: Box(i32), d: Box(u8)):
    pass
";
        let errors: Vec<_> = check_src(src)
            .unwrap_err()
            .into_iter()
            .map(|e| {
                let span = e.span.unwrap();
                (e.kind, &src[span.start..span.end])
            })
            .collect();
        assert_eq!(
            errors,
            vec![
                (TypeErrorKind::UnknownType("Missing".into()), "Missing"),
                (
                    TypeErrorKind::NotStorable("externref".into()),
                    "Ptr(externref)"
                ),
                (
                    TypeErrorKind::NotStorable("tuple(externref, i32)".into()),
                    "Ptr(tuple(externref, i32))"
                ),
                (
                    TypeErrorKind::NotStorable("Box(externref)".into()),
                    "&Box(externref)"
                ),
            ]
        );
    }

    #[test]
    fn generic_structs_must_have_finitely_many_finite_instances() {
        use TypeErrorKind::*;
        let src = "\
struct(T) L:
    next: L(T)
struct(T) A:
    b: B(T)
struct(T) B:
    a: A(T)
struct(T) W:
    x: T
struct S:
    w: W(S)
struct(T) List:
    next: &List(T)
struct(X, Y) Pair:
    swap: &Pair(Y, X)
struct(T) C:
    other: &C(i32)
struct(T) Bad:
    next: &Bad(&T)
struct(T) M:
    n: &N(Box(T))
struct(T) N:
    m: &M(T)
struct(T) Box:
    value: T
fn f(a: List(i32), p: Pair(i32, u8), c: C(u8), b: Bad(i32), m: M(f32)):
    pass
";
        let errors: Vec<_> = check_src(src)
            .unwrap_err()
            .into_iter()
            .map(|e| {
                let span = e.span.unwrap();
                (e.kind, &src[span.start..span.end])
            })
            .collect();
        assert_eq!(
            errors,
            vec![
                (ExpansiveRecursion("Bad".into()), "next: &Bad(&T)"),
                (ExpansiveRecursion("M".into()), "n: &N(Box(T))"),
                (RecursiveStruct("L".into()), "next: L(T)"),
                (RecursiveStruct("B".into()), "a: A(T)"),
                (RecursiveStruct("W(S)".into()), "W(S)"),
            ]
        );
    }

    #[test]
    fn tuple_types_take_none_or_at_least_two_type_arguments() {
        use TypeErrorKind::*;
        let src = "\
struct tuple:
    pass
struct(T) Box:
    value: T
struct(tuple) Bad:
    pass
fn f(a: tuple(i32), b: tuple(), c: tuple) -> tuple():
    let d = Box(tuple(i32, u8))(value: (1, 2))
    let e = Box((i32, u8))(value: (1, 2))
    let g = tuple(i32, u8)(1, 2)
    let h = tuple(i32, u8)
    let i = tuple
    let j: Box(tuple(u8, bool)) = d
    let k: Box(tuple()) = Box(tuple())(value: b)
    let l = Box(())(value: ())
    return c
";
        let count = |found| TooFewTypeArgs {
            name: "tuple".into(),
            at_least: 2,
            found,
        };
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("tuple".into()),
                DuplicateItem("tuple".into()),
                count(1),
                MissingTypeArgs("tuple".into()),
                NotAType,
                NotCallable("tuple(i32, u8)".into()),
                MissingTypeArgs("tuple".into()),
                mismatch("Box(tuple(u8, bool))", "Box(tuple(i32, u8))"),
                NotAType,
            ]
        );
        assert_eq!(
            count(1).to_string(),
            "`tuple` takes 0 or at least 2 type arguments, found 1"
        );
    }

    #[test]
    fn types_used_as_values_are_their_size_and_alignment() {
        let src = "\
struct Point:
    x: f32
    y: f64
struct(T) Box:
    value: T
pub let INT = i32
var heap: u32 = 1024
fn malloc(t: type) -> &u8:
    heap = (heap + t.align - 1) / t.align * t.align
    let p = heap as &u8
    heap += t.size
    return p
fn f() -> u32:
    let p = malloc(Point)
    let t: type = type(size: 3, align: 1)
    let u = tuple().size + (&tuple()).size
    return Box(u8).size + array(u8).align + tuple(u8, i64).size + (&Point).size + type.size
fn g(i32: u32) -> u32:
    return i32
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        assert_eq!(
            globals[..2],
            [("INT.size", Const::I32(4)), ("INT.align", Const::I32(4))]
        );
        assert_eq!(
            body(&module, "f"),
            "(set p (call malloc 16 8)) (set t.size 3) (set t.align 1) \
             (set u (I32.Add 0 4)) \
             (return (I32.Add (I32.Add (I32.Add (I32.Add 1 4) 16) 4) 8))"
        );
        assert_eq!(body(&module, "g"), "(return i32)");
    }

    #[test]
    fn only_storable_types_are_values() {
        use TypeErrorKind::*;
        let src = "\
struct type:
    pass
struct(T) Box:
    value: T
fn f(t: type):
    let a = externref
    let b = Box(tuple(externref, i32))
    let c = Box
    let d = i32(1)
    i32 = 1
    let e = type(size: 1)
    let g = t.len
";
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("type".into()),
                NotStorable("externref".into()),
                NotStorable("Box(tuple(externref, i32))".into()),
                MissingTypeArgs("Box".into()),
                NotCallable("i32".into()),
                NotAssignable,
                MissingArg("align".into()),
                NoField {
                    ty: "type".into(),
                    field: "len".into()
                },
            ]
        );
    }

    #[test]
    fn arrays_are_a_length_then_a_pointer() {
        let src = "\
extern:
    fn put(s: array(u8)) -> array(i32)
fn f(a: array(u8)) -> array(u8):
    return a
";
        let module = lower(src);
        assert_eq!(module.imports[0].params, [ValType::I32, ValType::I32]);
        assert_eq!(module.imports[0].results, [ValType::I32, ValType::I32]);
        let f = &module.funcs[0];
        let locals: Vec<_> = f.locals.iter().map(|l| l.name.as_str()).collect();
        assert_eq!(locals, ["a.len", "a.ptr"]);
        assert_eq!(body(&module, "f"), "(return a.len a.ptr)");
    }

    #[test]
    fn array_fields_are_places_laid_out_like_a_struct() {
        let src = "\
struct S:
    tag: u8
    name: array(u16)
fn f(a: array(u8), s: &S) -> u32:
    var b = a
    b.len = 2
    s.name.ptr = b.ptr as &u16
    return s.name.len
fn g(t: &tuple(u8, array(i32))) -> &i32:
    return t.1.ptr
";
        let module = lower(src);
        assert_eq!(body(&module, "g"), "(return (I32.Load offset=8 t))");
        assert_eq!(
            body(&module, "f"),
            "(set b.len a.len) (set b.ptr a.ptr) (set b.len 2) \
             (I32.Store offset=8 s b.ptr) (return (I32.Load offset=4 s))"
        );
    }

    #[test]
    fn arrays_are_constructed_from_a_length_and_pointer() {
        let src = "\
fn f(n: u32, p: &u8) -> array(u8):
    let b = array(u8)(len: n, ptr: p)
    let c = array(u8)(ptr: p, len: 3)
    return array(u8)(len: 0, ptr: 0)
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set b.len n) (set b.ptr p) (set c.len 3) (set c.ptr p) (return 0 0)"
        );
        let src = "\
fn f(n: u32, p: &u8, q: &i8, a: array(u8)):
    let b = array(u8)(len: n, ptr: q)
    let c = array(u8)(len: -1, ptr: 4294967296)
    let d = (n, p) as array(u8)
    let e = a as tuple(u32, &u8)
";
        let cast = |from: &str, to: &str| TypeErrorKind::InvalidCast {
            from: from.into(),
            to: to.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                mismatch("&u8", "&i8"),
                TypeErrorKind::InvalidOperand {
                    op: "-",
                    ty: "u32".into()
                },
                TypeErrorKind::IntOutOfRange("&u8".into()),
                cast("tuple(u32, &u8)", "array(u8)"),
                cast("array(u8)", "tuple(u32, &u8)"),
            ]
        );
    }

    #[test]
    fn integer_literals_are_addresses_where_pointers_are_expected() {
        let src = "\
fn f(p: &u8) -> bool:
    let q: &u8 = 16
    return p == 0
";
        assert_eq!(body(&lower(src), "f"), "(set q 16) (return (I32.Eq p 0))");
        assert_eq!(
            errors("fn f():\n    let p: &u8 = -4\n"),
            vec![TypeErrorKind::InvalidOperand {
                op: "-",
                ty: "&u8".into()
            }]
        );
    }

    #[test]
    fn indexing_checks_bounds_then_loads() {
        let src = "\
extern:
    fn tick() -> u32
fn f(a: array(u16), i: u32) -> u16:
    return a[i]
fn g(a: array(u8)) -> u8:
    return a[3]
fn h(a: array(u8)) -> u8:
    return a[tick()]
struct Q:
    a: i32
    b: i32
    c: i32
fn k(a: array(Q)) -> i32:
    return a[357913941].c
";
        let module = lower(src);
        let check =
            |i: &str, len: &str| format!("(if (I32.GeU {i} {len}) (then unreachable) (else ))");
        assert_eq!(
            body(&module, "f"),
            format!(
                "{} (set tmp3 (I32.Add a.ptr (I32.Mul i 2))) (return (I32.Load16U offset=0 tmp3))",
                check("i", "a.len")
            )
        );
        assert_eq!(
            body(&module, "g"),
            format!(
                "{} (set tmp2 (I32.Add a.ptr 3)) (return (I32.Load8U offset=0 tmp2))",
                check("3", "a.len")
            )
        );
        assert_eq!(
            body(&module, "h"),
            format!(
                "(set tmp2 (call tick )) {} (set tmp3 (I32.Add a.ptr tmp2)) \
                 (return (I32.Load8U offset=0 tmp3))",
                check("tmp2", "a.len")
            )
        );
        let src = "\
fn f(a: array(u8), i: i32, n: i32):
    let b = a[i]
    let c = n[0]
";
        assert_eq!(
            errors(src),
            vec![mismatch("u32", "i32"), invalid_operand("[]", "i32"),]
        );
    }

    #[test]
    fn elements_are_assignable_and_addressable() {
        let src = "\
struct P:
    x: i32
    y: f64
fn f(a: array(P), i: u32) -> &P:
    a[i].x += 1
    a[0] = P(x: 1, y: 2.0)
    return &a[i]
";
        let check = |i: &str| format!("(if (I32.GeU {i} a.len) (then unreachable) (else ))");
        assert_eq!(
            body(&lower(src), "f"),
            format!(
                "{} (set tmp3 (I32.Add a.ptr (I32.Mul i 16))) \
                 (I32.Store offset=0 tmp3 (I32.Add (I32.Load offset=0 tmp3) 1)) \
                 {} (set tmp4 (I32.Add a.ptr (I32.Mul 0 16))) \
                 (I32.Store offset=0 tmp4 1) (F64.Store offset=8 tmp4 2f64) \
                 {} (set tmp5 (I32.Add a.ptr (I32.Mul i 16))) (return tmp5)",
                check("i"),
                check("0"),
                check("i"),
            )
        );
    }

    #[test]
    fn for_loops_copy_each_element() {
        let src = "\
extern:
    fn log(n: u16)
fn f(a: array(u16)):
    for x in a:
        if x == 0:
            break
        log(x)
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set tmp2 a.len) (set tmp3 a.ptr) (set tmp4 0) (block (loop \
             (br_if 1 (I32.GeU tmp4 tmp2)) \
             (set x (I32.Load16U offset=0 (I32.Add tmp3 (I32.Mul tmp4 2)))) \
             (set tmp4 (I32.Add tmp4 1)) \
             (if (I32.Eq x 0) (then (br 2)) (else )) (call log [x] -> []) (br 0)))"
        );
        let src = "\
fn f(a: array(u8)):
    for x in a:
        x = 1
    for y in 5:
        pass
";
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::ImmutableAssign("x".into()),
                invalid_operand("for", "i32"),
            ]
        );
    }

    #[test]
    fn string_literals_are_data() {
        let src = "\
pub let greeting = \"hi\"
var duck = \"🦆\"
";
        let module = lower(src);
        assert_eq!(
            data(&module),
            [(0, &b"hi"[..]), (2, &[0xf0, 0x9f, 0xa6, 0x86][..])]
        );
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.export.as_deref(), g.init))
            .collect();
        assert_eq!(
            globals[..4],
            [
                ("greeting.len", Some("greeting.len"), Const::I32(2)),
                ("greeting.ptr", Some("greeting.ptr"), Const::I32(0)),
                ("duck.len", None, Const::I32(4)),
                ("duck.ptr", None, Const::I32(2)),
            ]
        );
    }

    #[test]
    fn array_literals_are_aligned_data_placed_inner_first() {
        let src = "\
struct P:
    a: u8
    b: i32
let names = [\"foo\", \"bar\"]
let table: array(u16) = [1, 2, 65535]
let points = [P(a: 1, b: -2)]
let empty: array(f64) = []
let flags = [true, false]
let nested: array(array(i8)) = [[], [-1]]
";
        let module = lower(src);
        assert_eq!(
            data(&module),
            [
                (0, &b"foo"[..]),
                (3, b"bar"),
                (8, &[3, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0]),
                (24, &[1, 0, 2, 0, 0xff, 0xff]),
                (32, &[1, 0, 0, 0, 0xfe, 0xff, 0xff, 0xff]),
                (40, &[1, 0]),
                (42, &[0xff]),
                (44, &[0, 0, 0, 0, 42, 0, 0, 0, 1, 0, 0, 0, 42, 0, 0, 0]),
            ]
        );
        let inits: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        for global in [
            ("names.len", Const::I32(2)),
            ("names.ptr", Const::I32(8)),
            ("empty.len", Const::I32(0)),
            ("empty.ptr", Const::I32(40)),
            ("nested.len", Const::I32(2)),
            ("nested.ptr", Const::I32(44)),
        ] {
            assert!(inits.contains(&global), "{global:?} in {inits:?}");
        }
    }

    #[test]
    fn literal_errors() {
        use TypeErrorKind::*;
        let src = "\
fn get() -> u8:
    return 1
let a = []
let b = [1, 2.0]
let c = [get()]
let d: array(u8) = [256]
let e = [1 / 0]
let g: array(externref) = []
fn f():
    let s = \"hi\"
    let l = [1]
";
        assert_eq!(
            errors(src),
            vec![
                UntypedEmptyArray,
                mismatch("i32", "f64"),
                NotConstant,
                IntOutOfRange("u8".into()),
                ConstTrap,
                NotStorable("externref".into()),
                LiteralOutsideGlobal,
                LiteralOutsideGlobal,
            ]
        );
    }

    #[test]
    fn data_end_is_the_first_free_address() {
        let data_end = |src: &str| {
            let global = lower(src).globals.pop().unwrap();
            (global.name, global.export, global.mutable, global.init)
        };
        let exported = |end| {
            let name = "data_end".to_string();
            (name.clone(), Some(name), false, Const::I32(end))
        };
        assert_eq!(data_end("pub let a = 1\n"), exported(0));
        assert_eq!(
            data_end("let s = \"abc\"\nlet t: array(i32) = []\n"),
            exported(3)
        );
        assert_eq!(data_end("let data_end = 1\n"), exported(0));
        assert_eq!(
            errors("pub let data_end = 1\n"),
            [TypeErrorKind::ReservedExport("data_end".into())]
        );
    }

    #[test]
    fn data_must_fit_in_the_initial_memory() {
        let pages = |min_pages| Settings {
            memory: MemoryLimits {
                min_pages,
                max_pages: None,
            },
            ..Settings::default()
        };
        assert!(check_with("let s = \"\"\n", &pages(0)).is_ok());
        assert_eq!(
            check_with("let s = \"a\"\n", &pages(0)),
            Err(vec![TypeError {
                kind: TypeErrorKind::DataTooLarge {
                    bytes: 1,
                    min_pages: 0
                },
                span: None,
                instances: Vec::new(),
            }])
        );
    }

    #[test]
    fn enum_members_are_their_values() {
        let src = "\
enum(i8) ReturnCode:
    ok
    error = 5
    fatal
fn f() -> i8:
    let r = ReturnCode.fatal
    return r as i8
";
        assert_eq!(body(&lower(src), "f"), "(set r 6) (return r)");
    }

    #[test]
    fn enum_members_are_distinct_constants() {
        use TypeErrorKind::*;
        let src = "\
struct P:
    x: i32
enum(i8) Count:
    a = 126
    b
    c
enum(u8) Clash:
    a = 1
    b
    c = 2
    a = 3
enum(f32) Zeros:
    pos = 0.0
    neg = -0.0
    same = 0.0
enum(P) Points:
    origin = P(x: 0)
    far
var v = 1
fn f() -> i32:
    return 1
enum(i32) Bad:
    call = f()
    mutable = v
    own = Bad.call as i32
    later = Later.x as i32
    wrong = true
    after
enum(i32) Later:
    x = 1
";
        assert_eq!(
            errors(src),
            vec![
                MemberOutOfRange {
                    member: "c".into(),
                    ty: "i8".into()
                },
                DuplicateValue {
                    member: "c".into(),
                    same_as: "b".into()
                },
                DuplicateMember("a".into()),
                DuplicateValue {
                    member: "same".into(),
                    same_as: "pos".into()
                },
                MissingValue("far".into()),
                NotConstant,
                NotConstant,
                NotConstant,
                NotConstant,
                mismatch("i32", "bool"),
            ]
        );
    }

    #[test]
    fn enums_compare_their_bits() {
        let src = "\
enum(i8) R:
    ok
    err
enum(tuple(f32, u8)) T:
    a = (0.0, 1)
    b = (-0.0, 1)
enum(tuple()) U:
    only = ()
let same = T.a == T.b
fn f(r: R, t: T, u: T) -> bool:
    let x = r == R.ok
    let y = t != u
    let z = U.only == U.only
    return x and y
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        assert_eq!(globals[0], ("same", Const::I32(0)));
        assert_eq!(
            body(&module, "f"),
            "(set x (I32.Eq r 0)) \
             (set y (I32.Or (I32.Ne (F32.Reinterpret t.0) (F32.Reinterpret u.0)) (I32.Ne t.1 u.1))) \
             (set z 1) \
             (return (if x y 0))"
        );
        let src = "\
enum(i8) R:
    ok
fn f(r: R):
    let a = r < R.ok
    let b = r == 0
    let c = r + r
";
        assert_eq!(
            errors(src),
            vec![
                invalid_operand("<", "R"),
                mismatch("R", "i32"),
                invalid_operand("+", "R"),
            ]
        );
    }

    #[test]
    fn aggregates_compare_their_fields() {
        let src = "\
struct P:
    x: i32
    y: f32
fn f(p: P, q: P, t: tuple(i8, P), u: tuple(i8, P)) -> bool:
    let a = p == q
    let b = t != u
    return a and b
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(set a (I32.And (I32.Eq p.x q.x) (F32.Eq p.y q.y))) \
             (set b (I32.Or (I32.Or (I32.Ne t.0 u.0) (I32.Ne t.1.x u.1.x)) (F32.Ne t.1.y u.1.y))) \
             (return (if a b 0))"
        );
    }

    #[test]
    fn units_and_types_compare() {
        let src = "\
struct P:
    x: i32
    y: f32
let same = i32 == u32
let differ = u8 == u16
let point = P(x: 1, y: 2.0) == P(x: 1, y: 2.0)
fn u():
    return
fn f(t: type) -> bool:
    let a = u() == u()
    let b = t != i8
    return b
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        assert_eq!(
            globals[..3],
            [
                ("same", Const::I32(1)),
                ("differ", Const::I32(0)),
                ("point", Const::I32(1)),
            ]
        );
        assert_eq!(
            body(&module, "f"),
            "(call u [] -> []) (call u [] -> []) (set a 1) \
             (set b (I32.Or (I32.Ne t.size 1) (I32.Ne t.align 1))) (return b)"
        );
    }

    #[test]
    fn arrays_compare_their_elements() {
        let src = "\
struct S:
    n: i32
    name: array(u8)
fn f(a: array(u8), b: array(u8), s: S, t: S) -> bool:
    let x = a == b
    let y = s != t
    return x and y
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(set x (call ==(array(u8)) a.len a.ptr b.len b.ptr)) \
             (set y (if (I32.Ne s.n t.n) 1 \
             (I32.Eqz (call ==(array(u8)) s.name.len s.name.ptr t.name.len t.name.ptr)))) \
             (return (if x y 0))"
        );
        let helpers: Vec<_> = module.funcs.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(helpers, ["f", "==(array(u8))"]);
        assert_eq!(
            body(&module, "==(array(u8))"),
            "(if (I32.Ne a.len b.len) (then (return 0)) (else )) (set tmp4 0) \
             (block (loop (br_if 1 (I32.GeU tmp4 a.len)) \
             (if (I32.Ne (I32.Load8U offset=0 (I32.Add a.ptr tmp4)) \
             (I32.Load8U offset=0 (I32.Add b.ptr tmp4))) (then (return 0)) (else )) \
             (set tmp4 (I32.Add tmp4 1)) (br 0))) \
             (return 1)"
        );
    }

    #[test]
    fn recursive_arrays_compare_through_one_function() {
        let src = "\
struct N:
    v: f32
    kids: array(N)
fn f(a: N, b: N) -> bool:
    return a == b
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(return (if (F32.Eq a.v b.v) \
             (call ==(array(N)) a.kids.len a.kids.ptr b.kids.len b.kids.ptr) 0))"
        );
        assert_eq!(
            body(&module, "==(array(N))"),
            "(if (I32.Ne a.len b.len) (then (return 0)) (else )) (set tmp4 0) \
             (block (loop (br_if 1 (I32.GeU tmp4 a.len)) \
             (set tmp5 (I32.Add a.ptr (I32.Mul tmp4 12))) \
             (set tmp7 (F32.Load offset=0 tmp5)) (set tmp8 (I32.Load offset=4 tmp5)) \
             (set tmp9 (I32.Load offset=8 tmp5)) \
             (set tmp6 (I32.Add b.ptr (I32.Mul tmp4 12))) \
             (set tmp10 (F32.Load offset=0 tmp6)) (set tmp11 (I32.Load offset=4 tmp6)) \
             (set tmp12 (I32.Load offset=8 tmp6)) \
             (if (if (F32.Ne tmp7 tmp10) 1 (I32.Eqz (call ==(array(N)) tmp8 tmp9 tmp11 tmp12))) \
             (then (return 0)) (else )) \
             (set tmp4 (I32.Add tmp4 1)) (br 0))) \
             (return 1)"
        );
    }

    #[test]
    fn equality_needs_values_to_compare() {
        let src = "\
struct H:
    r: externref
struct P:
    x: i32
let s = \"ab\" == \"ab\"
let t = (1, \"a\") == (2, \"b\")
enum(bool) E:
    a = (1, \"a\") != (2, \"a\")
fn f(h: H, p: P) -> bool:
    let a = h == h
    let b = (1, h) != (1, h)
    let c = p < p
    return p == 1
";
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::NotConstant,
                TypeErrorKind::NotConstant,
                TypeErrorKind::NotConstant,
                invalid_operand("==", "H"),
                invalid_operand("!=", "tuple(i32, H)"),
                invalid_operand("<", "P"),
                mismatch("P", "i32"),
            ]
        );
    }

    #[test]
    fn enums_cast_as_the_type_of_their_values() {
        let src = "\
enum(i8) R:
    ok = -1
    size
pub enum(R) S:
    good = R.ok
enum(f32) F:
    half = 0.5
pub let DEFAULT = S.good
fn f(s: S) -> i32:
    let a = s as R
    let b = s as i32
    let c = F.half as i64
    let d = R.size as i8
    let e = (R as type).size + S.align
    let t: type = R
    return b
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.export.as_deref(), g.init))
            .collect();
        assert_eq!(globals[0], ("DEFAULT", Some("DEFAULT"), Const::I32(-1)));
        assert_eq!(
            body(&module, "f"),
            "(set a s) (set b s) (set c (F32.TruncSatS(I64) 0.5f32)) (set d 0) \
             (set e (I32.Add 1 1)) (set t.size 1) (set t.align 1) (return b)"
        );
        let src = "\
enum(i8) R:
    ok
fn f(x: i8, r: R):
    let a = x as R
    let b = r as bool
    let c = R.missing
    R.ok = r
    let d = r.ok
";
        use TypeErrorKind::*;
        assert_eq!(
            errors(src),
            vec![
                InvalidCast {
                    from: "i8".into(),
                    to: "R".into()
                },
                InvalidCast {
                    from: "R".into(),
                    to: "bool".into()
                },
                NoMember {
                    ty: "R".into(),
                    member: "missing".into()
                },
                NotAssignable,
                NoField {
                    ty: "R".into(),
                    field: "ok".into()
                },
            ]
        );
    }

    #[test]
    fn for_loops_visit_each_enum_member() {
        let src = "\
extern:
    fn log(n: i8)
enum(i8) R:
    ok
    err = 5
    fatal
enum(tuple(u8, u8)) P:
    a = (1, 2)
    b = (3, 4)
fn f():
    for r in R:
        if r == R.err:
            continue
        log(r as i8)
    for p in P:
        pass
";
        assert_eq!(
            body(&lower(src), "f"),
            "(block \
             (block (set r 0) (if (I32.Eq r 5) (then (br 1)) (else )) (call log [r] -> [])) \
             (block (set r 5) (if (I32.Eq r 5) (then (br 1)) (else )) (call log [r] -> [])) \
             (block (set r 6) (if (I32.Eq r 5) (then (br 1)) (else )) (call log [r] -> []))) \
             (block (block (set p.0 1) (set p.1 2)) (block (set p.0 3) (set p.1 4)))"
        );
        let src = "\
enum(i8) R:
    ok
struct S:
    pass
fn f(E: i32):
    for a in (R as type):
        pass
    for b in S:
        pass
    for c in E:
        pass
";
        assert_eq!(
            errors(src),
            vec![
                invalid_operand("for", "type"),
                invalid_operand("for", "type"),
                invalid_operand("for", "i32"),
            ]
        );
    }

    #[test]
    fn enums_are_laid_out_like_their_values() {
        let src = "\
extern:
    fn get() -> R
enum(i8) R:
    ok
    err
struct S:
    r: R
    x: i32
let codes: array(R) = [R.err, R.ok]
fn f(p: &S) -> R:
    p.r = get()
    return p.r
";
        let module = lower(src);
        assert_eq!(data(&module), [(0, &[1, 0][..])]);
        assert_eq!(module.imports[0].results, [ValType::I32]);
        assert_eq!(
            body(&module, "f"),
            "(I32.Store8 offset=0 p (I32.Extend8S (call get ))) \
             (return (I32.Load8S offset=0 p))"
        );
    }

    #[test]
    fn enums_can_not_contain_themselves() {
        use TypeErrorKind::*;
        let src = "\
enum(i8) R:
    ok
struct R:
    pass
enum(A) A:
    a = 1
enum(tuple(C, i8)) C:
    c = 1
struct S:
    e: E
enum(S) E:
    a = S(e: 1)
enum(Nope) Z:
    z = 1
enum(&externref) X:
    x = 1
struct(R) Box:
    value: R
enum(tuple(u8, u8)) P:
    a = (1, 2)
fn f():
    let r = R(1)
    let (a, b) = P.a
";
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("R".into()),
                UnknownType("Nope".into()),
                RecursiveEnum("A".into()),
                RecursiveEnum("C".into()),
                DuplicateItem("R".into()),
                RecursiveStruct("S".into()),
                NotStorable("externref".into()),
                NotCallable("R".into()),
                mismatch("tuple(_, _)", "P"),
            ]
        );
    }
}

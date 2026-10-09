//! Name resolution, type checking, and lowering to [`crate::ir`].
//!
//! All three happen in one walk over each function body. Signatures are
//! collected first so items can be used before they are declared. Functions
//! imported from `extern` blocks come first in the function index space.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::mem;
use std::ops::Range;

use crate::eval::Evaluator;
use crate::file::{FileId, MemoryLimits, Settings, StaticSection};
use crate::ir::{
    self, BinOp as IrBinOp, Const, Expr, FuncId, GlobalId, LoadOp, LocalId, Stmt, StoreOp,
    UnOp as IrUnOp, ValType,
};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{
    self, Arg, BinOp, ExprKind, ExternBlock, ExternFn, FnSig, Ident, ItemKind, Mutability, Pattern,
    PatternKind, StmtKind, StructDecl, TypeKind, UnaryOp, UnionDecl,
};

use defaults::DefaultValue;
use enums::EnumDef;
use evaluate::Dep;
use generic::{Arity, Instance, ParamDef, param_names};
use generic_fn::{FnInstance, GenericFn, InstanceCall};
use unions::{Holds, narrow, tags_are, where_held, widen};

mod defaults;
mod enums;
mod equality;
mod evaluate;
mod fn_ptr;
mod generic;
mod generic_fn;
mod inspect;
mod patterns;
mod unions;

pub use evaluate::DEFAULT_FUEL;
pub use inspect::{
    Action, Analysis, Completion, CompletionKind, Hint, HintKind, Hover, Parameter, Signature,
    Symbol, SymbolKind, Unused, UnusedKind, analyze, module_members,
};

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

/// The export name of the module's table, which no item may take either.
const TABLE_EXPORT: &str = "table";

/// Bytes in a wasm page.
const PAGE_SIZE: u64 = 64 * 1024;

/// The functions of `module`, which are lowered inline at each call rather
/// than to wasm functions.
const MODULE_FUNCS: [&str; 8] = [
    "memory",
    "size",
    "grow",
    "fill",
    "copy",
    "unreachable",
    COUNT_LEADING_ZEROS,
    COUNT_TRAILING_ZEROS,
];

/// The function of `module` that counts the zero bits above an integer's
/// highest set bit.
const COUNT_LEADING_ZEROS: &str = "count_leading_zeros";

/// The function of `module` that counts the zero bits below an integer's
/// lowest set bit.
const COUNT_TRAILING_ZEROS: &str = "count_trailing_zeros";

/// The constants of `module`.
const MODULE_CONSTS: [&str; 4] = ["static", "page_size", "min", "max"];

/// The name of the built-in array type.
const ARRAY: &str = "array";

/// The name of the built-in type of arrays whose elements can be written.
const VARRAY: &str = "varray";

/// The name of the built-in tuple type.
const TUPLE: &str = "tuple";

/// The name of the built-in union that holds a value or `none`.
const OPTION: &str = "option";

/// The name of the built-in union that holds a value or an error.
const RESULT: &str = "result";

/// The name of the host reference type.
const EXTERNREF: &str = "externref";

/// The name of the built-in type of types used as values.
const TYPE: &str = "type";

/// The fields of every array, in order.
const ARRAY_FIELDS: [&str; 2] = ["ptr", "len"];

/// The fields of a `type`, in order.
const TYPE_FIELDS: [&str; 2] = ["size", "align"];

/// The module that `extern` blocks without one import from.
const DEFAULT_IMPORT_MODULE: &str = "env";

/// The most structs and unions that can be nested by value, each a field of
/// the one before or a variant, or in a tuple or enum of one. Generics can
/// nest far more than are ever written, as one that holds another of itself
/// twice over does.
const MAX_VALUE_DEPTH: usize = 64;

/// The name of a local the compiler makes, which holds no variable.
const TEMP: &str = "tmp";

/// The most constants that can be nested, each folded where the last is
/// first to use it.
const MAX_CONSTANT_DEPTH: usize = 64;

/// A primitive stored as exactly one wasm value. `tuple()` is [`Ty::Unit`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Prim {
    I8,
    I16,
    I32,
    I64,
    /// `int`, a signed integer as wide as an address.
    Int,
    U8,
    U16,
    U32,
    U64,
    /// `uint`, an unsigned integer as wide as an address, which counts
    /// bytes and elements.
    Uint,
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

/// Index of an interned pointer type, which records the pointee and whether
/// it can be written through.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PtrId(u32);

/// Index of an interned tuple type, which records the element types.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TupleId(u32);

/// Index of an interned array type, which records the type of its `ptr`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArrayId(u32);

/// Index of an interned function type, which records the types of its
/// parameters and result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FnId(u32);

/// Index of a generic struct's or function's type parameter.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ParamId(u32);

/// Index of a generic function declaration, in declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct GenericFnId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ty {
    Prim(Prim),
    /// A struct, or a union, which is declared as a struct is: with a field
    /// per variant.
    Struct(StructId),
    /// An enum, stored as the value of its member, so laid out like the type
    /// of its values.
    Enum(EnumId),
    /// `&T`, an address in linear memory, stored as a `uint` is. `&var T` is
    /// one that can be written through.
    Ptr(PtrId),
    /// `tuple(A, B)`, which is laid out like a struct with a field per element.
    Tuple(TupleId),
    /// `array(T)`, a view of elements in linear memory that it doesn't own.
    /// Laid out like a struct with the fields `ptr: &T` and `len: uint`.
    /// `varray(T)` is one whose elements can be written, so its `ptr` is a
    /// `&var T`.
    Array(ArrayId),
    /// `fn(A) -> R`, a pointer to a function, stored as its index in the
    /// module's table, which is as wide as an address.
    Fn(FnId),
    /// `type`, the type of a type written where a value belongs, as in
    /// `malloc(Point)`, and of the parameter it is given to, which is a type
    /// parameter. Its values have no scalars: a type is known as the
    /// program is compiled.
    Type,
    /// A type parameter, which the fields of its generic struct's declaration
    /// have, and the body of its generic function's while that is checked as
    /// declared. Uses of either replace it with a type argument.
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
    /// For an error in an instance of a generic function, which is reported
    /// at the call that led to it, the instances the call led to, outermost
    /// first: each but the last calls the next, and the last has the error.
    pub instances: Vec<InstanceSite>,
}

/// An instance of a generic function, and where in its body it calls the
/// next instance, or has the error.
#[derive(Debug, Clone, PartialEq)]
pub struct InstanceSite {
    /// The instance as written, such as `id(i32)`.
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeErrorKind {
    UnknownName(String),
    UnknownType(String),
    /// A module, or a function of `module`, used as a value.
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
    /// A union that contains itself by value.
    RecursiveUnion(String),
    DuplicateVariant(String),
    /// A union with more variants than its tag tells apart.
    TooManyVariants(String),
    NoVariant {
        ty: String,
        variant: String,
    },
    /// A variant that holds no value, given one.
    VariantTakesNothing(String),
    /// A variant that holds a `ty`, given none, or more than one.
    VariantNeedsValue {
        variant: String,
        ty: String,
    },
    /// `.name` where nothing says what type it's a variant or member of.
    UntypedDot(String),
    /// A `match` whose arms leave out values that this pattern matches.
    NonExhaustive(String),
    /// An arm of a `match` after others that match every value it does.
    UnreachableArm,
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
    /// A generic struct or union that uses itself with ever larger type
    /// arguments, so it has no end of instances.
    ExpansiveRecursion(String),
    /// A struct or union that holds others by value, each holding the next,
    /// too many deep. It is the generic one of an instance.
    NestedTooDeep(String),
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
    /// A type parameter bounded by a type that isn't a struct, a union or an
    /// enum.
    NotABound(String),
    /// A type argument that isn't a union of the first variants of its type
    /// parameter's bound, or an enum of its first members, which `what`
    /// says.
    NotWithin {
        ty: String,
        bound: String,
        what: &'static str,
    },
    /// A bound that names its own type parameter, or one declared after it
    /// in the list.
    BoundNamesLater {
        bound: String,
        param: String,
    },
    /// A type argument that doesn't start as its type parameter's bound
    /// does.
    BoundNotMet {
        ty: String,
        bound: String,
    },
    /// A default with a type of its own, which isn't the type that its
    /// parameter or field has where a call or constructor leaves it out.
    DefaultMismatch {
        param: String,
        expected: String,
        found: String,
    },
    /// `type` written as any type but a function's parameter's.
    TypeOutsideParam,
    /// A parameter of type `type` given a default.
    TypeParamDefault(String),
    /// A type parameter that a call infers, which is in no parameter's type.
    NeverInferred {
        func: String,
        param: String,
    },
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
    /// A cast between a pointer or function pointer and an integer other
    /// than `int` and `uint`, which alone are as wide as an address.
    AddressCast {
        from: String,
        to: String,
    },
    /// A cast with `as` that only `as!` makes, as nothing says that a
    /// `from` is a `to`.
    UncheckedCast {
        from: String,
        to: String,
    },
    /// A cast with `as!` that is neither between addresses nor between an
    /// integer and a float of one width: only `as` makes a value one of
    /// another type.
    UncheckedValue {
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
    /// A write to memory behind `ty`, a `&T` or `array(T)`, which only read
    /// it. `needs` is the type that writes, and `element` is whether `ty` is
    /// the array.
    ReadOnlyWrite {
        ty: String,
        needs: String,
        element: bool,
    },
    /// `&var` of memory behind `ty`, as [`Self::ReadOnlyWrite`] has it.
    ReadOnlyAddr {
        ty: String,
        needs: String,
        element: bool,
    },
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
    /// A call through a function pointer given too few arguments. Its
    /// parameters have no names to report as missing.
    TooFewArgs {
        expected: usize,
        found: usize,
    },
    /// An argument given a label in a call through a function pointer,
    /// whose parameters have no names.
    LabelledPointerArg,
    MissingReturn(String),
    BreakOutsideLoop,
    ContinueOutsideLoop,
    /// A global initializer that traps, such as dividing by zero.
    ConstTrap,
    /// Code that traps while it's run to evaluate a constant.
    ConstTraps {
        trap: String,
        stack: Vec<String>,
    },
    /// Code run to evaluate a constant that used up its fuel.
    ConstOutOfFuel {
        fuel: u64,
        stack: Vec<String>,
    },
    /// A call of an `extern` function by code run to evaluate a constant.
    ConstCallsExtern {
        name: String,
        stack: Vec<String>,
    },
    /// A call, by code run to evaluate a constant, of a function that
    /// nothing the constant names leads to: only a pointer that other code
    /// left in memory does.
    ConstCallsUnnamed {
        name: String,
        stack: Vec<String>,
    },
    /// Code that couldn't be run to evaluate a constant, and why.
    ConstNotRun(String),
    /// A global, enum or struct that the global's initializer, the enum's
    /// members' values or the struct's fields' defaults use.
    RecursiveConstant(String),
    /// A global, enum or struct first used by a constant that is itself
    /// nested within too many others, each first used by the one before.
    ConstantTooDeep(String),
    /// A `pub` item whose export name is taken by the module itself.
    ReservedExport(String),
    /// An item of another module that isn't `pub`.
    Private(String),
    /// A name that no item of the module `module` has.
    NoItem {
        module: String,
        item: String,
    },
    /// An item that a `use` path goes on past, as only a module's can.
    NotAModule(String),
    /// A `use` path through a name that another `use` gives what this one
    /// names, or a `use` in a struct, a union or an enum of a type that
    /// uses it.
    RecursiveUse(String),
    /// A `use` in `within`, which is a struct, a union or an enum, of a
    /// `ty`, which is no such type.
    UseOfOther {
        within: &'static str,
        ty: String,
    },
    /// A `use` in an enum of `expected` values of the enum `name`, whose
    /// values are `found`.
    UseOfValues {
        name: String,
        expected: String,
        found: String,
    },
    /// A `use` of a field or variant `name` whose type holds a `ty` that
    /// another module declares and isn't `pub`.
    UseOfPrivate {
        name: String,
        ty: String,
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
    /// Literal data that doesn't fit in the static data section.
    DataTooLarge {
        bytes: u128,
        capacity: u64,
    },
    /// A static data section that ends past the memory's initial pages.
    StaticOutsideMemory {
        end: u64,
        min_pages: u64,
    },
    /// A static data section that ends past the pages the memory may grow
    /// to, where it starts with as many as hold the section.
    StaticOutsideMax {
        end: u64,
        max_pages: u64,
    },
    /// A static data section fitted to literals that it is too small for
    /// once they are given its size.
    SelfSizedStatic,
    /// `module.name` naming nothing.
    UnknownModuleProperty(String),
    /// A string or array literal outside a global initializer or default.
    LiteralOutsideGlobal,
    /// A `varray` literal with elements in a default, which every value of
    /// the struct or call of the function would share.
    SharedLiteral,
    /// A `&var` that places its value in memory in a default, which every
    /// value of the struct or call of the function would share.
    SharedPointee,
    /// A default that names this type parameter of its struct or function,
    /// or whose value one lays out.
    DefaultUsesParam(String),
    /// A parameter's default that names this parameter of its function.
    DefaultReadsParam(String),
    /// `[]` with no type to give its elements.
    UntypedEmptyArray,
    /// An expression where a type argument should be.
    NotAType,
    /// A type argument given a label, as only fields and parameters are.
    LabelledTypeArg,
    /// An error in the body of an instance of a generic function, whose
    /// declaration was found to be right for every type argument. A bug in
    /// the compiler.
    Unchecked {
        instance: String,
        error: Box<TypeErrorKind>,
    },
}

#[derive(Default)]
struct Checker {
    /// The names declared in each module: its items and what it uses.
    scopes: HashMap<FileId, HashMap<String, Entry>>,
    /// The names each module uses that weren't found, which are reported
    /// where they are used and not again where they are named.
    unresolved: HashSet<(FileId, String)>,
    /// How far each `use` of the program is declared.
    uses: Vec<Visit>,
    /// The module whose names are in scope.
    module: FileId,
    /// The module whose `pub` items are exported.
    entry: FileId,
    /// Struct declarations in declaration order, then the built-in unions,
    /// then instances of generic ones as they are used.
    structs: Vec<StructDef>,
    /// The built-in unions, `option` and then `result`, once declared.
    builtin_unions: Vec<StructId>,
    /// Each instance of a generic struct by its declaration and type
    /// arguments.
    instances: HashMap<(StructId, Vec<Ty>), StructId>,
    /// Every generic struct's type parameters, indexed by [`ParamId`].
    params: Vec<ParamDef>,
    /// The type parameters in scope, and the types they stand for: themselves
    /// in a generic declaration, and type arguments in an instance.
    type_params: Vec<(String, Ty)>,
    /// Enum declarations in declaration order.
    enums: Vec<EnumDef>,
    /// Instances whose fields wait on every generic struct's being defined.
    pending: Vec<StructId>,
    /// Where a struct that holds others nested too deep is reported, which
    /// it is once.
    deep_sites: Vec<Span>,
    /// Whether every generic struct's fields are known, so instances can
    /// be given theirs.
    generics_defined: bool,
    /// The pointee of each pointer type, and whether it's a `&var`.
    pointees: Vec<(Ty, bool)>,
    ptr_ids: HashMap<(Ty, bool), PtrId>,
    /// The element types of each tuple type.
    tuples: Vec<Vec<Ty>>,
    tuple_ids: HashMap<Vec<Ty>, TupleId>,
    /// The type of each array type's `ptr` field, which points to its
    /// elements. A `varray`'s is a `&var`.
    arrays: Vec<Ty>,
    array_ids: HashMap<Ty, ArrayId>,
    /// The parameter types and result type of each function type.
    fn_tys: Vec<(Vec<Ty>, Ty)>,
    fn_ty_ids: HashMap<(Vec<Ty>, Ty), FnId>,
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
    /// The functions that pointers call, in the order their pointers are
    /// first taken. Each is at the table index one past its place here.
    table: Vec<FuncId>,
    table_indices: HashMap<FuncId, u32>,
    /// The function that pointers to each imported function call it
    /// through, for those whose results the host may give out of range.
    wrappers: HashMap<FuncId, FuncId>,
    /// Generic function declarations, indexed by [`GenericFnId`].
    generic_fns: Vec<GenericFn>,
    /// Each instance of a generic function by its declaration and type
    /// arguments.
    fn_instances: HashMap<(GenericFnId, Vec<Ty>), FuncId>,
    /// Where the body of a generic function uses a value of a bounded type
    /// parameter as its bound, by the file and start of what does: the name
    /// of a field it reads, or the value a `match` takes apart. Each
    /// instance uses it as that bound too.
    bound_uses: HashMap<(FileId, usize), Ty>,
    /// The type arguments still to be compared with the bounds they were
    /// given, and where: those that are enums whose members' values weren't
    /// folded.
    pending_bounds: Vec<(Ty, Ty, Span)>,
    /// While checking or lowering an instance of a generic function, it and
    /// the instances whose calls led to it, innermost first. Given to errors.
    instance_chain: Vec<InstanceCall>,
    /// Whether the body of a generic function is being checked as declared,
    /// with its type parameters standing for themselves. What is lowered is
    /// of no instance, so it creates no function and takes no pointer.
    open: bool,
    /// `None` until the global's initializer has been checked.
    globals: Vec<Option<GlobalDef>>,
    /// The item of the program that binds each global.
    global_items: Vec<usize>,
    /// The constants of each item of the program.
    constants: Vec<Constants>,
    /// How many constants are being folded, each within the one before.
    constant_depth: usize,
    ir_globals: Vec<ir::Global>,
    /// The memory's size limits, which `module.min` and `module.max` are.
    memory: MemoryLimits,
    /// Whether an address is 64 bits wide rather than 32.
    memory64: bool,
    /// Where literals are placed, which `module.static` is. While
    /// `unfitted`, it is empty.
    static_section: StaticSection,
    /// Whether the static data section is yet to be fitted to the literals,
    /// which it is once every global is defined.
    unfitted: bool,
    /// Whether anything was given the size of the static data section, or
    /// the pages that hold it, while it was `unfitted`.
    read_unfitted: bool,
    /// The address literals must end by.
    data_limit: u64,
    /// The contents of literals, placed in memory in the order they are
    /// lowered.
    data: Vec<ir::Data>,
    /// The first address after `data`, or the start of the static data
    /// section if there is none. Data that doesn't fit may end past every
    /// address.
    data_end: u128,
    /// The address of each string that a pattern is, which is placed once.
    pattern_strings: HashMap<String, u64>,
    /// The item of the program that declares each function that isn't
    /// generic, indexed by [`FuncId`], and each that is, by [`GenericFnId`].
    func_items: Vec<usize>,
    generic_fn_items: Vec<usize>,
    /// The items whose constants are being folded, innermost last.
    folding: Vec<usize>,
    /// What each item being folded and each function being lowered for one
    /// names, innermost last.
    deps: Vec<Vec<Dep>>,
    /// What the constants of each item that is folded name.
    item_deps: HashMap<usize, Vec<Dep>>,
    /// The functions lowered for a constant to call, which are lowered once,
    /// and what each names.
    lowered: HashMap<FuncId, ir::Func>,
    func_deps: HashMap<FuncId, Vec<Dep>>,
    /// The functions being lowered for a constant to call.
    lowering: HashSet<FuncId>,
    /// The state that the code constants run leaves, which the module
    /// starts with. `None` until one runs any.
    eval: Option<Evaluator>,
    /// How many of `data` are in the memory of `eval`.
    synced: usize,
    /// The addresses of literals that are all zeros, which aren't in `data`,
    /// and how many bytes each is: those placed since `eval` was last given
    /// them.
    zeroed: Vec<(u64, u64)>,
    /// Whether code run for a constant failed. None is run after that, as
    /// it left the state half made.
    failed: bool,
    /// The fuel the constants of one item run on, and what is left of it
    /// for the item being folded.
    fuel_limit: u64,
    fuel: u64,
    errors: Vec<TypeError>,
    /// The type of each expression and of each name a pattern binds, by
    /// where it is written, if they are kept for an [`Analysis`].
    types: Option<HashMap<Span, Ty>>,
}

/// The functions that were running where code run for a constant stopped,
/// innermost first, as an error says them.
struct Stack<'a>(&'a [String]);

#[derive(Debug, Clone, Copy, PartialEq)]
enum Item {
    Func(FuncId),
    GenericFn(GenericFnId),
    Struct(StructId),
    Enum(EnumId),
    Global(usize),
    /// A module, by the name it's used as.
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

/// A struct, or a union, whose fields are its variants.
struct StructDef {
    /// The declared name, or for an instance, its type as written.
    name: String,
    /// The module that declares it, or for an instance, its declaration.
    module: FileId,
    /// The item of the program that declares it, or for an instance, its
    /// declaration. Unused for a built-in union, which no item declares.
    item: usize,
    is_pub: bool,
    /// Whether it's a union: a value holds one of its fields, and a tag
    /// that says which.
    union: bool,
    /// The [`Ty::Param`] of each type parameter of a generic declaration.
    params: Vec<Ty>,
    /// Set for instances of generic declarations.
    instance: Option<Instance>,
    /// An instance's are its declaration's, with its type arguments in place
    /// of the type parameters.
    fields: Vec<FieldDef>,
    /// How many structs and unions nest by value in it, itself included, as
    /// [`Checker::value_depth`] found. `None` until it is asked for.
    depth: Option<usize>,
}

#[derive(Clone)]
struct FieldDef {
    name: String,
    ty: Ty,
    /// Whether modules other than the struct's can use it.
    is_pub: bool,
    /// Whether it's a variant of a union that holds no value. Its `ty` is
    /// `tuple()`, as is that of one that holds a `tuple()`.
    bare: bool,
    /// What it is where a constructor gives it no value, if anything. An
    /// instance's is its declaration's, as it was when the instance was made.
    default: Option<DefaultValue>,
    /// The type of its default, if that has one of its own rather than the
    /// field's as declared. Only a declaration's is set.
    default_ty: Option<Ty>,
    /// The field of another struct or union that a `use` makes it one of,
    /// if any, whose default is its own.
    used: Option<(StructId, usize)>,
    /// Where it is written: the `use`, for one that a `use` makes a field.
    span: Span,
}

#[derive(Clone)]
struct FuncSig {
    name: String,
    params: Vec<(String, Ty)>,
    /// What each parameter is where a call gives it no argument, if
    /// anything. Empty for a function the checker creates, which no call
    /// names: an instance of a generic function has its declaration's.
    defaults: Vec<Option<DefaultValue>>,
    ret: Ty,
}

/// A function the checker creates, rather than one defined in the source.
enum Synth {
    /// Compares two arrays of this type.
    Eq(Ty),
    Instance(FnInstance),
    /// Calls this imported function and brings its results into range.
    Wrapper(FuncId),
}

struct GlobalDef {
    ty: Ty,
    mutable: bool,
    /// [`Slots::Global`] for a `var`, and [`Slots::Const`] for a `let`.
    slots: Slots,
}

/// What an item of the program has that is folded when first used: the
/// initializer of a binding's globals, the values of an enum's members or
/// the defaults of a struct's fields.
#[derive(Clone, Copy)]
struct Constants {
    /// The first of a binding's globals, or the enum or struct by its id.
    id: usize,
    /// Whether they are folded, or being folded. An item without any is
    /// done.
    state: Visit,
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
    /// The program, if this is a global initializer: the only place
    /// literals that need memory can be, and where a constant that isn't
    /// folded yet is folded to be read.
    global: Option<&'c Program>,
    /// The program, if this is the body of a function: one lowered for a
    /// constant to call folds the constants it is first to read.
    program: Option<&'c Program>,
    /// Whether this is a field's or parameter's default, a kind of global
    /// initializer whose value is shared wherever the default is used.
    default: bool,
    /// The value piped into each enclosing pipe body, innermost last.
    piped: Vec<(Ty, Vec<(ValType, Expr)>)>,
    /// The variables that an assignment within the statement being lowered
    /// changes before the statement ends. What is read of one is held in
    /// temporaries, so that it is what the variable had when it was read.
    assigned: Vec<String>,
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
    /// An `if`, a `match`, or an arm of one.
    Other,
}

/// A variable, a field of one, or memory behind a pointer, that can be
/// assigned.
struct Place {
    name: String,
    ty: Ty,
    mutable: bool,
    /// The pointer or array whose memory this is, if it's in memory.
    behind: Option<Ty>,
    /// Computes the address of a `Slots::Memory` place. Runs before anything
    /// else in the assignment.
    pre: Vec<Stmt>,
    slots: Slots,
}

#[derive(Clone)]
enum Slots {
    Local(Vec<LocalId>),
    /// One wasm global per scalar leaf.
    Global(Vec<GlobalId>),
    /// The value of each scalar leaf of a `let` global, which every use of
    /// it is replaced with.
    Const(Vec<Const>),
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

/// A scalar leaf of a value: which of them it is, and its type.
#[derive(Clone, Copy, PartialEq)]
struct Leaf {
    index: usize,
    ty: ValType,
}

/// A narrow integer or `bool` in a value, which is an `i32` that the host
/// may give out of its range.
struct Ranged {
    /// The leaf that holds it.
    leaf: Leaf,
    prim: Prim,
    /// For one in a union's variant, each union it's in and the variant of
    /// it, outermost first: the leaf holds it only where they all hold.
    when: Vec<Holds>,
}

/// Where one scalar of a type lives in memory.
struct Cell {
    /// Bytes from the start of the value.
    offset: u32,
    /// The leaf of the value that holds the scalar, which may be wider than
    /// it where the variants of a union share the leaf.
    leaf: Leaf,
    ty: ValType,
    load: LoadOp,
    store: StoreOp,
    /// Whether the cell holds a `bool`, which may be any byte in memory.
    bool: bool,
    /// For a cell of a union's variant, each union it's in and the variant
    /// of it, outermost first: the cell holds nothing unless they all hold.
    when: Vec<Holds>,
}

/// Why a global initializer could not be folded.
enum Fold {
    /// It is only known by running it.
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
            "int" => Self::Int,
            "u8" => Self::U8,
            "u16" => Self::U16,
            "u32" => Self::U32,
            "u64" => Self::U64,
            "uint" => Self::Uint,
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
            Self::Int => "int",
            Self::U8 => "u8",
            Self::U16 => "u16",
            Self::U32 => "u32",
            Self::U64 => "u64",
            Self::Uint => "uint",
            Self::F32 => "f32",
            Self::F64 => "f64",
            Self::Bool => "bool",
        }
    }

    /// The wasm value that holds one. An `int` or `uint` is
    /// [fixed](Checker::fixed) first, as are those of every method that
    /// depends on a size: theirs is that of an address.
    fn val_type(self) -> ValType {
        match self {
            Self::Int | Self::Uint => unreachable!("`int` and `uint` are fixed first"),
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
        matches!(
            self,
            Self::I8 | Self::I16 | Self::I32 | Self::I64 | Self::Int
        )
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
            Self::Int | Self::Uint => unreachable!("`int` and `uint` are fixed first"),
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
            Self::Int | Self::Uint => unreachable!("`int` and `uint` are fixed first"),
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
            Self::RecursiveUnion(name) => write!(f, "union `{name}` contains itself"),
            Self::DuplicateVariant(name) => write!(f, "duplicate variant `{name}`"),
            Self::TooManyVariants(name) => write!(
                f,
                "union `{name}` has more than {} variants",
                unions::MAX_VARIANTS
            ),
            Self::NoVariant { ty, variant } => write!(f, "`{ty}` has no variant `{variant}`"),
            Self::VariantTakesNothing(name) => {
                write!(
                    f,
                    "variant `{name}` holds no value, so it takes no argument"
                )
            }
            Self::VariantNeedsValue { variant, ty } => {
                write!(
                    f,
                    "variant `{variant}` holds a `{ty}`, and takes it as its one argument"
                )
            }
            Self::UntypedDot(name) => write!(
                f,
                "nothing says what type `.{name}` is of; name it, as in `Type.{name}`"
            ),
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
            Self::NonExhaustive(pattern) => write!(
                f,
                "`match` has no arm for `{pattern}`; give it one, or an `else`"
            ),
            Self::UnreachableArm => write!(
                f,
                "this arm is never reached: those before it match every value it does"
            ),
            Self::NoMember { ty, member } => write!(f, "`{ty}` has no member `{member}`"),
            Self::ExpansiveRecursion(name) => {
                write!(f, "`{name}` uses itself with ever larger type arguments")
            }
            Self::NestedTooDeep(name) => write!(
                f,
                "`{name}` holds structs and unions nested more than {MAX_VALUE_DEPTH} deep"
            ),
            Self::NotGeneric(name) => write!(f, "`{name}` has no type parameters"),
            Self::NotABound(ty) => write!(
                f,
                "`{ty}` can't bound a type parameter; only a struct, a union or an enum can"
            ),
            Self::NotWithin { ty, bound, what } => write!(
                f,
                "`{ty}` doesn't have only the first {what} of `{bound}`, in order"
            ),
            Self::BoundNamesLater { bound, param } => write!(
                f,
                "the bound `{bound}` names `{param}`, which isn't declared before the type \
                 parameter it bounds"
            ),
            Self::BoundNotMet { ty, bound } => {
                write!(f, "`{ty}` doesn't start as `{bound}` does")
            }
            Self::DefaultMismatch {
                param,
                expected,
                found,
            } => write!(
                f,
                "the default of `{param}` is a `{found}`, where a `{expected}` is needed here: \
                 give `{param}` a value"
            ),
            Self::TypeOutsideParam => write!(
                f,
                "`type` is only the type of a function's parameter, which it makes a type parameter"
            ),
            Self::TypeParamDefault(name) => {
                write!(f, "type parameter `{name}` can't have a default")
            }
            Self::NeverInferred { func, param } => write!(
                f,
                "no parameter of `{func}` has `{param}` in its type, so no call infers it; \
                 make it a parameter: `{param}: type`"
            ),
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
                "cannot infer `{param}` for `{func}`: no argument has a type that settles it"
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
            Self::AddressCast { from, to } => write!(
                f,
                "can't cast `{from}` as `{to}`; pointers cast to and from `uint` and `int`"
            ),
            Self::UncheckedCast { from, to } => {
                write!(f, "casting `{from}` as `{to}` is unchecked: write `as!`")
            }
            Self::UncheckedValue { from, to } => write!(
                f,
                "`as!` casts an address as another, or an integer and a float of one width \
                 as each other, and `{from}` as `{to}` is neither"
            ),
            Self::IntOutOfRange(ty) => write!(f, "literal out of range for `{ty}`"),
            Self::NoField { ty, field } => write!(f, "`{ty}` has no field `{field}`"),
            Self::NotAssignable => write!(f, "invalid assignment target"),
            Self::NotAddressable => write!(f, "only memory behind a pointer has an address"),
            Self::NotStorable(ty) => write!(f, "`{ty}` can't be stored in memory"),
            Self::ImmutableAssign(name) => write!(f, "can't assign to immutable `{name}`"),
            Self::ReadOnlyWrite { ty, needs, element } => {
                let through = if *element {
                    "to an element of"
                } else {
                    "through"
                };
                write!(f, "can't write {through} `{ty}`; it needs a `{needs}`")
            }
            Self::ReadOnlyAddr { ty, needs, element } => {
                let through = if *element {
                    "of an element of"
                } else {
                    "through"
                };
                write!(
                    f,
                    "can't take `&var` {through} `{ty}`; it needs a `{needs}`"
                )
            }
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
            Self::TooFewArgs { expected, found } => {
                write!(f, "expected {expected} arguments, found {found}")
            }
            Self::LabelledPointerArg => {
                write!(
                    f,
                    "arguments of a call through a function pointer can't be labelled"
                )
            }
            Self::MissingReturn(name) => write!(f, "`{name}` can finish without returning"),
            Self::BreakOutsideLoop => write!(f, "`break` outside of a loop"),
            Self::ContinueOutsideLoop => write!(f, "`continue` outside of a loop"),
            Self::ConstTrap => write!(f, "constant evaluation traps"),
            Self::ConstTraps { trap, stack } => {
                write!(f, "constant evaluation traps: {trap}{}", Stack(stack))
            }
            Self::ConstOutOfFuel { fuel, stack } => write!(
                f,
                "constant evaluation used up its fuel of {fuel}{}; \
                 `fuel` under `[const]` in Duck.toml gives it more",
                Stack(stack)
            ),
            Self::ConstCallsExtern { name, stack } => write!(
                f,
                "constant evaluation calls the extern function `{name}`{}",
                Stack(stack)
            ),
            Self::ConstCallsUnnamed { name, stack } => write!(
                f,
                "constant evaluation calls `{name}` through a pointer that nothing the \
                 constant names leads to{}",
                Stack(stack)
            ),
            Self::ConstNotRun(why) => write!(f, "constant evaluation couldn't run: {why}"),
            Self::RecursiveConstant(name) => {
                write!(f, "`{name}` is used in its own definition")
            }
            Self::ConstantTooDeep(name) => write!(
                f,
                "`{name}` is first used more than {MAX_CONSTANT_DEPTH} constants deep; \
                 declare it before the constants that use it"
            ),
            Self::ReservedExport(name) => write!(f, "the export name `{name}` is reserved"),
            Self::UnknownStart(name) => write!(f, "no function named `{name}` to start"),
            Self::Private(name) => write!(f, "`{name}` is private"),
            Self::NoItem { module, item } => write!(f, "`{module}` has no item `{item}`"),
            Self::NotAModule(name) => write!(f, "`{name}` is not a module"),
            Self::RecursiveUse(path) => write!(f, "`use` of `{path}` leads back to itself"),
            Self::UseOfOther { within, ty } => {
                write!(f, "`use` in {within} takes {within}, which `{ty}` isn't")
            }
            Self::UseOfValues {
                name,
                expected,
                found,
            } => write!(
                f,
                "`use` in an enum of `{expected}` takes one, and `{name}` is an enum of `{found}`"
            ),
            Self::UseOfPrivate { name, ty } => {
                write!(f, "`use` of `{name}`, whose type holds the private `{ty}`")
            }
            Self::PrivateField { ty, field } => write!(f, "field `{field}` of `{ty}` is private"),
            Self::PrivateInPublic { ty, item } => {
                write!(f, "private type `{ty}` in the type of `pub` item `{item}`")
            }
            Self::InvalidStart(name) => write!(
                f,
                "start function `{name}` must take no arguments and return nothing"
            ),
            Self::DataTooLarge { bytes, capacity } => write!(
                f,
                "literals take {bytes} bytes, more than the {capacity} bytes of the static data section"
            ),
            Self::StaticOutsideMemory { end, min_pages } => write!(
                f,
                "the static data section ends at address {end}, past the {min_pages} pages memory starts with"
            ),
            Self::StaticOutsideMax { end, max_pages } => write!(
                f,
                "the static data section ends at address {end}, past the {max_pages} pages memory may grow to"
            ),
            Self::SelfSizedStatic => write!(
                f,
                "the static data section is fitted to literals whose size depends on its own"
            ),
            Self::UnknownModuleProperty(name) => write!(f, "`module` has no property `{name}`"),
            Self::LiteralOutsideGlobal => write!(
                f,
                "string and array literals are only allowed in global initializers and defaults"
            ),
            Self::SharedLiteral => write!(
                f,
                "a writable literal in a default is shared wherever the default is used, so it must be empty"
            ),
            Self::SharedPointee => write!(
                f,
                "a `&var` in a default places one value, shared wherever the default is used"
            ),
            Self::DefaultUsesParam(param) => {
                write!(f, "a default can't depend on the type parameter `{param}`")
            }
            Self::DefaultReadsParam(param) => write!(
                f,
                "a default is evaluated once, so it can't use the parameter `{param}`"
            ),
            Self::UntypedEmptyArray => write!(f, "can't infer the element type of `[]`"),
            Self::NotAType => write!(f, "expected a type"),
            Self::LabelledTypeArg => write!(f, "type arguments can't be labelled"),
            Self::Unchecked { instance, error } => write!(
                f,
                "internal error: checking the declaration of `{instance}` missed an error in its body: \
                 {error}; please report this"
            ),
        }
    }
}

impl fmt::Display for Stack<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, name) in self.0.iter().enumerate() {
            match i {
                0 => write!(f, ", in `{name}`")?,
                _ => write!(f, ", called from `{name}`")?,
            }
        }
        Ok(())
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.span {
            Some(span) => write!(f, "{} at {}..{}", self.kind, span.start, span.end)?,
            None => self.kind.fmt(f)?,
        }
        for site in &self.instances {
            let span = site.span;
            write!(
                f,
                ", required by `{}` at {}..{}",
                site.name, span.start, span.end
            )?;
        }
        Ok(())
    }
}

impl std::error::Error for TypeError {}

/// Resolves names in, type checks, and lowers a loaded program to one wasm
/// module, giving it the memory and start function `settings` describe.
///
/// The module starts as the code its constants ran left it: with that
/// memory, of that size, and with each `var` as it was last assigned.
///
/// Checking continues past errors, so every error in the program is reported
/// at once.
pub fn check(program: &Program, settings: &Settings) -> Result<ir::Module, Vec<TypeError>> {
    let (mut ck, imports, funcs, start) = lower_program(program, settings, false);
    if !ck.errors.is_empty() {
        return Err(ck.errors);
    }
    let mut min_pages = ck.min_pages();
    if let Some(eval) = &mut ck.eval {
        min_pages = min_pages.max(eval.pages());
        ck.data = eval.data();
        let globals = ck.ir_globals.iter_mut().enumerate();
        for (index, global) in globals.filter(|(_, global)| global.mutable) {
            global.init = eval.global(index);
        }
    }
    Ok(ir::Module {
        memory: ir::Memory {
            min_pages,
            max_pages: settings.memory.max_pages,
            memory64: settings.memory64,
            export: MEMORY_EXPORT.to_string(),
        },
        data: ck.data,
        table: (!ck.table.is_empty()).then(|| ir::Table {
            table64: settings.memory64,
            export: TABLE_EXPORT.to_string(),
            funcs: ck.table,
        }),
        globals: ck.ir_globals,
        imports,
        funcs,
        start,
    })
}

/// The errors that [`check`] finds in `program`, without the module it
/// makes of one that has none.
pub fn errors(program: &Program, settings: &Settings) -> Vec<TypeError> {
    lower_program(program, settings, false).0.errors
}

/// Checks and lowers `program`. Returns the checker, which has its errors,
/// and its imports, its functions and its start function. If it `records`,
/// the checker keeps the type of what is written, too.
fn lower_program(
    program: &Program,
    settings: &Settings,
    records: bool,
) -> (Checker, Vec<ir::Import>, Vec<ir::Func>, Option<FuncId>) {
    let mut ck = Checker::define(program, settings, None, records);
    if ck.unfitted {
        // Literals are only in globals, so every one has been placed.
        let fitted = StaticSection {
            start: 0,
            end: ck.data_end.min(ck.data_limit.into()) as u64,
        };
        if ck.read_unfitted {
            // A global was given a size the section doesn't have.
            ck = Checker::define(program, settings, Some(fitted), records);
            if ck.data_fits() && ck.data_end != u128::from(fitted.end) {
                ck.errors.push(TypeError {
                    kind: TypeErrorKind::SelfSizedStatic,
                    span: None,
                    instances: Vec::new(),
                });
            }
        } else {
            ck.static_section = fitted;
            ck.unfitted = false;
        }
    }
    ck.check_static_section();
    let start = settings
        .start
        .as_ref()
        .and_then(|name| ck.resolve_start(program, name));
    ck.check_generic_fns(program);
    let imports = ck.lower_imports(program);
    let mut funcs = ck.lower_funcs(program);
    funcs.extend(ck.lower_synths(program));
    // An instance may only have an error that checking its declaration
    // missed because of one that is reported.
    let unchecked = |e: &TypeError| matches!(e.kind, TypeErrorKind::Unchecked { .. });
    if !ck.errors.iter().all(unchecked) {
        ck.errors.retain(|e| !unchecked(e));
    }
    ck.place_late_literals();
    (ck, imports, funcs, start)
}

impl Checker {
    /// Reports an error at `span`. In an instance of a generic function it
    /// is reported at the call that led to the instance, with `span` as
    /// where in the instance it is.
    fn error(&mut self, kind: TypeErrorKind, span: Span) {
        if let TypeErrorKind::UnknownName(name) | TypeErrorKind::UnknownType(name) = &kind
            && self.unresolved.contains(&(self.module, name.clone()))
        {
            return;
        }
        let mut span = span;
        let mut instances = Vec::new();
        for instance in &self.instance_chain {
            let name = instance.name.clone();
            instances.push(InstanceSite { name, span });
            span = instance.call;
        }
        instances.reverse();
        self.errors.push(TypeError {
            kind,
            span: Some(span),
            instances,
        });
    }

    /// Keeps `ty` as the type of what is written at `span`, if types are
    /// kept. One written in a generic function has the type it is declared
    /// with, and none of an instance.
    fn record(&mut self, span: Span, ty: Ty) {
        if let Some(types) = &mut self.types
            && self.instance_chain.is_empty()
            && ty != Ty::Error
        {
            types.insert(span, ty);
        }
    }

    /// Keeps the type of each parameter of `sig`, which `decl` declares, as
    /// [`Self::record`] keeps that of a name a pattern binds.
    fn record_params(&mut self, decl: &FnSig, sig: &FuncSig) {
        for (param, (_, ty)) in decl.params.iter().zip(&sig.params) {
            self.record(param.name.span, *ty);
        }
    }

    /// Registers every item's name, so bodies can refer to later items.
    fn declare(&mut self, program: &Program) {
        self.import_count = extern_fns(program).count() as u32;
        self.funcs = fn_sigs(program)
            .map(|(_, sig)| FuncSig {
                name: sig.name.name.clone(),
                params: Vec::new(),
                defaults: Vec::new(),
                ret: Ty::Unit,
            })
            .collect();
        self.func_items = vec![0; self.funcs.len()];
        let (mut next_import, mut next_def) = (0, self.import_count);
        for (index, item) in program.items.iter().enumerate() {
            self.module = item.span.file;
            let has_default = |sig: &FnSig| sig.params.iter().any(|p| p.default.is_some());
            let (id, state) = match &item.kind {
                ItemKind::Struct(_) => (self.structs.len(), Visit::New),
                ItemKind::Enum(_) => (self.enums.len(), Visit::New),
                ItemKind::Binding(_) => (self.globals.len(), Visit::New),
                // The defaults of its parameters.
                ItemKind::Fn(f) if !has_default(&f.sig) => (0, Visit::Done),
                ItemKind::Fn(f) if f.sig.is_generic() => (self.generic_fns.len(), Visit::New),
                ItemKind::Fn(_) => (next_def as usize, Visit::New),
                ItemKind::Extern(block) if block.fns.iter().any(|f| has_default(&f.sig)) => {
                    (next_import as usize, Visit::New)
                }
                _ => (0, Visit::Done),
            };
            self.constants.push(Constants { id, state });
            let (name, entry) = match &item.kind {
                ItemKind::Struct(StructDecl { name, params, .. })
                | ItemKind::Union(UnionDecl { name, params, .. }) => {
                    let id = StructId(self.structs.len() as u32);
                    let params = self.new_params(&param_names(params));
                    self.structs.push(StructDef {
                        name: name.name.clone(),
                        module: self.module,
                        item: index,
                        is_pub: item.is_pub,
                        union: matches!(item.kind, ItemKind::Union(_)),
                        params,
                        instance: None,
                        fields: Vec::new(),
                        depth: None,
                    });
                    (name, Item::Struct(id))
                }
                ItemKind::Fn(f) if f.sig.is_generic() => {
                    self.generic_fn_items.push(index);
                    (&f.sig.name, Item::GenericFn(self.declare_generic_fn(f)))
                }
                ItemKind::Fn(f) => {
                    self.func_items[next_def as usize] = index;
                    next_def += 1;
                    (&f.sig.name, Item::Func(FuncId(next_def - 1)))
                }
                ItemKind::Extern(block) => {
                    for f in &block.fns {
                        self.func_items[next_import as usize] = index;
                        self.declare_name(&f.sig.name, Item::Func(FuncId(next_import)), f.is_pub);
                        next_import += 1;
                    }
                    continue;
                }
                ItemKind::Binding(b) => {
                    for name in pattern_names(&b.pattern) {
                        self.globals.push(None);
                        self.global_items.push(index);
                        self.declare_item(item, &name, Item::Global(self.globals.len() - 1));
                    }
                    continue;
                }
                ItemKind::Enum(e) => {
                    let id = self.declare_enum(e, index, item.is_pub);
                    (&e.name, Item::Enum(id))
                }
                // Replaced by the items of the modules used when loading.
                ItemKind::Use(_) => continue,
            };
            self.declare_item(item, name, entry);
        }
        self.declare_builtin_unions();
        self.uses = vec![Visit::New; program.uses.len()];
        for index in 0..program.uses.len() {
            self.declare_use(program, index);
        }
    }

    /// Declares the name that use `index` of `program` gives the module its
    /// path leads into, or what the rest of the path reaches from there,
    /// unless it's declared or being declared.
    fn declare_use(&mut self, program: &Program, index: usize) {
        if self.uses[index] != Visit::New {
            return;
        }
        self.uses[index] = Visit::Active;
        let used = &program.uses[index];
        self.module = used.module;
        let mut item = Some(Item::Module(used.target));
        let mut path = used.target_path.clone();
        for member in &used.members {
            item = match item {
                Some(Item::Module(module)) => {
                    let declared = self.declare_uses_of(program, module, &member.name);
                    self.module = used.module;
                    if !declared {
                        let path = format!("{path}.{}", member.name);
                        self.error(TypeErrorKind::RecursiveUse(path), member.span);
                        None
                    } else if self.unresolved.contains(&(module, member.name.clone())) {
                        // Reported where `module` uses it.
                        None
                    } else {
                        self.reach(module, &path, member)
                    }
                }
                Some(_) => {
                    self.error(TypeErrorKind::NotAModule(path.clone()), member.span);
                    None
                }
                None => break,
            };
            path = format!("{path}.{}", member.name);
        }
        match item {
            Some(item) => self.declare_name(&used.name, item, used.is_pub),
            None => {
                let name = used.name.name.clone();
                self.unresolved.insert((used.module, name));
            }
        }
        self.uses[index] = Visit::Done;
    }

    /// Declares what `module` uses as `name`, if it has no such name yet:
    /// modules that use each other reach names through uses that come
    /// later. Returns whether none of them is being declared, as one that a
    /// path leads back to is.
    fn declare_uses_of(&mut self, program: &Program, module: FileId, name: &str) -> bool {
        let scope = self.scopes.get(&module);
        if scope.is_some_and(|scope| scope.contains_key(name)) {
            return true;
        }
        let mut declared = true;
        for (index, used) in program.uses.iter().enumerate() {
            if used.module == module && used.name.name == name {
                declared &= self.uses[index] != Visit::Active;
                self.declare_use(program, index);
            }
        }
        declared
    }

    /// Declares a name defined by `item`, which may export it.
    fn declare_item(&mut self, item: &parse::Item, name: &Ident, entry: Item) {
        self.declare_name(name, entry, item.is_pub);
        if self.exports(item) && [MEMORY_EXPORT, TABLE_EXPORT].contains(&name.name.as_str()) {
            self.error(TypeErrorKind::ReservedExport(name.name.clone()), name.span);
        }
    }

    /// Declares `name` in the current module.
    fn declare_name(&mut self, name: &Ident, item: Item, is_pub: bool) {
        let scope = self.scopes.entry(self.module).or_default();
        if scope.contains_key(&name.name)
            || [ARRAY, VARRAY, TUPLE, TYPE, OPTION, RESULT].contains(&name.name.as_str())
        {
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

    /// Resolves the type of every enum's values, every struct's fields and
    /// every union's variants, reporting generic structs that recurse
    /// without end and types that contain themselves, then gives every
    /// instance used so far its fields.
    fn define_structs(&mut self, program: &Program) {
        self.resolve_enums(program);
        let is_decl =
            |item: &&parse::Item| matches!(item.kind, ItemKind::Struct(_) | ItemKind::Union(_));
        let decl_count = program.items.iter().filter(is_decl).count();
        let mut visits = vec![Visit::New; decl_count];
        for id in 0..decl_count {
            self.define_fields(program, id, &mut visits);
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
        // What was measured as instances were filled may have been cut.
        for id in 0..self.structs.len() {
            self.structs[id].depth = None;
        }
        for id in 0..self.structs.len() {
            self.value_depth(StructId(id as u32));
        }
        self.check_field_pointers(0..self.structs.len());
        self.check_enum_pointers();
        self.structs_defined = true;
        for id in 0..self.structs.len() {
            self.check_instance_bounds(StructId(id as u32));
        }
    }

    /// How many structs and unions nest by value in struct `id`, itself
    /// included, which is found once. A field that holds as many as may nest
    /// is reported and given the error type, so that no value nests deeper.
    /// A struct being measured counts for nothing: it contains itself, and
    /// is reported for that.
    fn value_depth(&mut self, id: StructId) -> usize {
        let index = id.0 as usize;
        if let Some(depth) = self.structs[index].depth {
            return depth;
        }
        // An instance that waits on its fields is given them.
        if self.generics_defined {
            self.fill_instance(id);
        }
        self.structs[index].depth = Some(0);
        let mut deepest = 0;
        for i in 0..self.structs[index].fields.len() {
            let mut held = Vec::new();
            self.push_inline_structs(self.structs[index].fields[i].ty, &mut held);
            let depths = held.into_iter().map(|held| self.value_depth(held));
            let depth = depths.max().unwrap_or(0);
            if depth < MAX_VALUE_DEPTH {
                deepest = deepest.max(depth);
                continue;
            }
            let site = self.field_site(index, i);
            let def = &mut self.structs[index];
            def.fields[i].ty = Ty::Error;
            let named = match &mut def.instance {
                Some(instance) => {
                    instance.too_deep = true;
                    instance.generic.0 as usize
                }
                None => index,
            };
            let name = self.structs[named].name.clone();
            if !self.deep_sites.contains(&site) {
                self.deep_sites.push(site);
                self.error(TypeErrorKind::NestedTooDeep(name), site);
            }
        }
        self.structs[index].depth = Some(deepest + 1);
        deepest + 1
    }

    /// Resolves the fields of struct or union declaration `id`, unless it
    /// has them, or is being given them, as one that a `use` leads back to
    /// is. `visits` is how far each declaration is. Those it uses are given
    /// theirs first.
    fn define_fields(&mut self, program: &Program, id: usize, visits: &mut [Visit]) {
        if visits[id] != Visit::New {
            return;
        }
        visits[id] = Visit::Active;
        let item = &program.items[self.structs[id].item];
        let (ItemKind::Struct(StructDecl { params, .. })
        | ItemKind::Union(UnionDecl { params, .. })) = &item.kind
        else {
            unreachable!("a struct or a union declares it")
        };
        // It may be a declaration that another, being resolved, uses.
        let module = mem::replace(&mut self.module, item.span.file);
        let outer = mem::take(&mut self.type_params);
        let tys = self.structs[id].params.clone();
        self.declare_type_params(&param_names(params), &tys);
        self.resolve_bounds(params, &tys);
        let fields = match &item.kind {
            ItemKind::Union(decl) => self.union_variants(program, id, decl, visits),
            ItemKind::Struct(decl) => self.struct_fields(program, id, decl, visits),
            _ => Vec::new(),
        };
        self.type_params = outer;
        self.module = module;
        self.structs[id].fields = fields;
        visits[id] = Visit::Done;
    }

    /// Resolves the fields of struct `id`, which `decl` declares, with its
    /// type parameters in scope.
    fn struct_fields(
        &mut self,
        program: &Program,
        id: usize,
        decl: &StructDecl,
        visits: &mut [Visit],
    ) -> Vec<FieldDef> {
        let mut fields: Vec<FieldDef> = Vec::new();
        for entry in &decl.entries {
            let field = match entry {
                parse::Entry::Own(field) => field,
                parse::Entry::Use(used) => {
                    for field in self.used_fields(program, id, used, visits) {
                        if self.structs[id].is_pub && field.is_pub {
                            self.check_public(field.ty, used.span, &field.name);
                        }
                        if fields.iter().any(|f| f.name == field.name) {
                            self.error(TypeErrorKind::DuplicateField(field.name), used.span);
                            continue;
                        }
                        fields.push(field);
                    }
                    continue;
                }
            };
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
                bare: false,
                default: field.default.as_ref().map(|_| DefaultValue::Pending),
                default_ty: None,
                used: None,
                span: field.span,
            });
        }
        fields
    }

    /// The fields that `use written` gives struct or union declaration
    /// `id`: those of the struct or union that `written` names, as its type
    /// arguments make them, each written where the `use` is. None after
    /// reporting an error.
    pub(super) fn used_fields(
        &mut self,
        program: &Program,
        id: usize,
        written: &parse::Type,
        visits: &mut [Visit],
    ) -> Vec<FieldDef> {
        let ty = self.resolve_ty(written);
        let union = self.structs[id].union;
        let used = match ty {
            Ty::Struct(used) if self.structs[used.0 as usize].union == union => used,
            Ty::Error => return Vec::new(),
            _ => {
                let within = match union {
                    true => "a union",
                    false => "a struct",
                };
                let ty = self.ty_name(ty);
                self.error(TypeErrorKind::UseOfOther { within, ty }, written.span);
                return Vec::new();
            }
        };
        let (decl, args) = match &self.structs[used.0 as usize].instance {
            Some(instance) => (instance.generic, instance.args.clone()),
            None => (used, Vec::new()),
        };
        // A built-in union is no declaration, and uses nothing.
        if let Some(visit) = visits.get(decl.0 as usize) {
            if *visit == Visit::Active {
                let kind = TypeErrorKind::RecursiveUse(self.ty_name(ty));
                self.error(kind, written.span);
                return Vec::new();
            }
            self.define_fields(program, decl.0 as usize, visits);
        }
        let mut fields = self.structs[decl.0 as usize].fields.clone();
        for (index, field) in fields.iter_mut().enumerate() {
            if !args.is_empty() {
                field.ty = self.substitute(field.ty, &args, written.span);
            }
            if let Some(private) = self.private_part(field.ty, Some(self.module)) {
                let (name, ty) = (field.name.clone(), self.ty_name(private));
                self.error(TypeErrorKind::UseOfPrivate { name, ty }, written.span);
                field.ty = Ty::Error;
            }
            // Folded with the defaults of the declaration that uses it.
            field.default = field.default.as_ref().map(|_| DefaultValue::Pending);
            field.default_ty = None;
            field.used = Some((used, index));
            field.span = written.span;
        }
        fields
    }

    /// Reports pointer fields whose pointee can't be stored in memory, which
    /// `resolve_ty` couldn't know before every struct was defined, and gives
    /// them the error type. Only checks the structs `ids`.
    fn check_field_pointers(&mut self, ids: Range<usize>) {
        for id in ids {
            // Known once its type parameters are given their arguments.
            if self.structs[id].instance.is_some() && self.is_open(StructId(id as u32)) {
                continue;
            }
            for i in 0..self.structs[id].fields.len() {
                let field = &self.structs[id].fields[i];
                if let Some(ty) = self.unstorable_pointee(field.ty) {
                    if !self.reports_pointee(field) {
                        let kind = TypeErrorKind::NotStorable(self.ty_name(ty));
                        self.error(kind, self.field_site(id, i));
                    }
                    self.structs[id].fields[i].ty = Ty::Error;
                }
            }
        }
    }

    /// Whether a pointer in `field` that can't be stored is reported in the
    /// field that a `use` makes it one of: the struct that the `use` names
    /// has its own fields checked, unless it waits on type arguments.
    fn reports_pointee(&self, field: &FieldDef) -> bool {
        let Some((used, at)) = field.used else {
            return false;
        };
        let def = &self.structs[used.0 as usize];
        let ty = def.fields[at].ty;
        let waits = def.instance.is_some() && self.is_open(used);
        !waits && (ty == Ty::Error || self.unstorable_pointee(ty).is_some())
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
                        let name = self.structs[id].name.clone();
                        let kind = match self.structs[id].union {
                            true => TypeErrorKind::RecursiveUnion(name),
                            false => TypeErrorKind::RecursiveStruct(name),
                        };
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
            self.funcs[id].defaults = pending_defaults(decl);
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
        if let Some(private) = self.private_part(ty, None) {
            let kind = TypeErrorKind::PrivateInPublic {
                ty: self.ty_name(private),
                item: item.to_string(),
            };
            self.error(kind, span);
        }
    }

    /// The first struct or enum in `ty` that isn't `pub`. With `within`,
    /// only one that the module `within` doesn't declare, so can't name.
    fn private_part(&self, ty: Ty, within: Option<FileId>) -> Option<Ty> {
        match ty {
            Ty::Struct(id) => {
                let def = &self.structs[id.0 as usize];
                if !def.is_pub && within != Some(def.module) {
                    return Some(ty);
                }
                let args = def.instance.iter().flat_map(|instance| &instance.args);
                args.into_iter()
                    .find_map(|arg| self.private_part(*arg, within))
            }
            Ty::Enum(id) => {
                let def = &self.enums[id.0 as usize];
                (!def.is_pub && within != Some(def.module)).then_some(ty)
            }
            _ => self
                .components(ty)
                .into_iter()
                .find_map(|component| self.private_part(component, within)),
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
            // A type parameter, which only a generic function has.
            let ty = match param.ty.is_type() {
                true => Ty::Type,
                false => self.resolve_ty(&param.ty),
            };
            params.push((param.name.name.clone(), ty));
        }
        let ret = sig.ret.as_ref().map_or(Ty::Unit, |ty| self.resolve_ty(ty));
        (params, ret)
    }

    /// Checks and folds global initializers, the values of enum members and
    /// the defaults of struct fields and of parameters: in declaration
    /// order, but for those that an earlier one uses, which are folded then.
    fn define_globals(&mut self, program: &Program) {
        for index in 0..program.items.len() {
            self.fold_item(program, index);
        }
    }

    /// Checks and folds the constants of item `index` of `program`, unless
    /// they are folded or being folded, or nested too deep to be.
    fn fold_item(&mut self, program: &Program, index: usize) {
        let Constants { id, state } = self.constants[index];
        if state != Visit::New || self.constant_depth == MAX_CONSTANT_DEPTH {
            return;
        }
        self.constants[index].state = Visit::Active;
        self.constant_depth += 1;
        self.folding.push(index);
        self.deps.push(Vec::new());
        let item = &program.items[index];
        // What first reads them may be an instance of a generic function.
        let module = mem::replace(&mut self.module, item.span.file);
        let type_params = mem::take(&mut self.type_params);
        let chain = mem::take(&mut self.instance_chain);
        let fuel = mem::replace(&mut self.fuel, self.fuel_limit);
        match &item.kind {
            ItemKind::Binding(decl) => self.define_binding(program, item, decl, id),
            ItemKind::Enum(decl) => self.define_members(program, EnumId(id as u32), decl),
            ItemKind::Struct(decl) => self.define_defaults(program, StructId(id as u32), decl),
            ItemKind::Fn(decl) if decl.sig.is_generic() => {
                self.define_generic_fn_defaults(program, GenericFnId(id as u32), &decl.sig);
            }
            ItemKind::Fn(decl) => self.define_param_defaults(program, id, &decl.sig),
            ItemKind::Extern(block) => {
                for (i, decl) in block.fns.iter().enumerate() {
                    self.define_param_defaults(program, id + i, &decl.sig);
                }
            }
            _ => {}
        }
        self.fuel = fuel;
        self.module = module;
        self.type_params = type_params;
        self.instance_chain = chain;
        let deps = self.deps.pop().unwrap_or_default();
        self.item_deps.insert(index, deps);
        self.folding.pop();
        self.constant_depth -= 1;
        self.constants[index].state = Visit::Done;
    }

    /// Whether the constants of item `index` of `program` are folded, which
    /// they are here if they weren't, where there is a `program` to fold.
    /// Otherwise reports why `name`, used at `span`, has none.
    fn folded(&mut self, program: Option<&Program>, index: usize, name: &str, span: Span) -> bool {
        if let Some(program) = program {
            self.fold_item(program, index);
        }
        let kind = match self.constants[index].state {
            Visit::Done => {
                self.note(Dep::Item(index));
                return true;
            }
            Visit::Active => TypeErrorKind::RecursiveConstant(name.to_string()),
            Visit::New => TypeErrorKind::ConstantTooDeep(name.to_string()),
        };
        self.error(kind, span);
        false
    }

    /// Records that what is being folded or lowered names `dep`, which code
    /// that a constant runs may then call.
    fn note(&mut self, dep: Dep) {
        if let Some(deps) = self.deps.last_mut() {
            deps.push(dep);
        }
    }

    /// The name of item `index` of `program`, as an error says whose
    /// constants are being folded.
    fn item_name(&self, program: &Program, index: usize) -> String {
        match &program.items[index].kind {
            ItemKind::Binding(decl) => {
                let names = pattern_names(&decl.pattern);
                names.first().map_or("_", |name| &name.name).to_string()
            }
            ItemKind::Struct(StructDecl { name, .. }) | ItemKind::Union(UnionDecl { name, .. }) => {
                name.name.clone()
            }
            ItemKind::Enum(decl) => decl.name.name.clone(),
            ItemKind::Fn(decl) => decl.sig.name.name.clone(),
            ItemKind::Extern(_) | ItemKind::Use(_) => "extern".to_string(),
        }
    }

    /// Checks and folds the initializer of `decl`, the binding that `item`
    /// is, and defines the globals it binds, the first of which is `index`.
    fn define_binding(
        &mut self,
        program: &Program,
        item: &parse::Item,
        decl: &parse::Binding,
        mut index: usize,
    ) {
        let mut body = Body::new(self, Ty::Unit);
        body.global = Some(program);
        let (ty, value) = body.binding_value(decl);
        let mutable = decl.mutability == Mutability::Var;
        let inits = body.evaluate(value, decl.value.span).unwrap_or_default();
        let exported = self.exports(item);
        // Each name gets its own globals, in the order `declare` gave them.
        for bound in self.destructure(&decl.pattern, ty) {
            let (mut wasm, mut consts) = (Vec::new(), Vec::new());
            let leaves = self.leaves(bound.ty, bound.name);
            for ((name, vt), i) in leaves.into_iter().zip(bound.leaves) {
                let init = inits.get(i).copied().unwrap_or(zero(vt));
                consts.push(init);
                // Only a wasm global can be assigned or exported.
                if mutable || exported {
                    wasm.push(GlobalId(self.ir_globals.len() as u32));
                    self.ir_globals.push(ir::Global {
                        export: exported.then(|| name.clone()),
                        name,
                        ty: vt,
                        mutable,
                        init,
                    });
                }
            }
            // A `let` is its value wherever it is used, so an exported
            // one's wasm globals are only read by the host.
            let slots = match mutable {
                true => Slots::Global(wasm),
                false => Slots::Const(consts),
            };
            let ty = bound.ty;
            if item.is_pub {
                self.check_public(ty, bound.span, bound.name);
            }
            self.globals[index] = Some(GlobalDef { ty, mutable, slots });
            index += 1;
        }
    }

    /// Declares and defines every item of `program`, which places its
    /// literals. `fitted` is the static data section, if the settings leave
    /// it to be fitted to the literals and it has been. If it `records`, the
    /// type of what is written is kept.
    fn define(
        program: &Program,
        settings: &Settings,
        fitted: Option<StaticSection>,
        records: bool,
    ) -> Self {
        let static_section = settings.static_section.or(fitted).unwrap_or_default();
        let mut ck = Self {
            types: records.then(HashMap::new),
            entry: program.entry,
            memory: settings.memory,
            memory64: settings.memory64,
            static_section,
            unfitted: settings.static_section.is_none() && fitted.is_none(),
            data_end: static_section.start.into(),
            fuel_limit: settings.fuel.unwrap_or(DEFAULT_FUEL),
            ..Self::default()
        };
        ck.data_limit = match settings.static_section {
            Some(section) => section.end,
            None => ck.max_addr(),
        };
        ck.declare(program);
        ck.define_structs(program);
        ck.define_funcs(program);
        ck.define_globals(program);
        ck.check_pending_bounds();
        ck.place_pattern_strings(program);
        ck
    }

    /// The pages memory starts with, which `module.min` is: those of the
    /// settings, or else the fewest that hold the static data section.
    fn min_pages(&self) -> u64 {
        let fewest = self.static_section.end.div_ceil(PAGE_SIZE);
        self.memory.min_pages.unwrap_or(fewest)
    }

    /// Checks that the static data section is in the memory's initial
    /// pages, and that literal data fits in it.
    fn check_static_section(&mut self) {
        let StaticSection { start, end } = self.static_section;
        let mut errors = Vec::new();
        match (self.memory.min_pages, self.memory.max_pages) {
            (Some(min_pages), _) if end.div_ceil(PAGE_SIZE) > min_pages => {
                errors.push(TypeErrorKind::StaticOutsideMemory { end, min_pages });
            }
            (None, Some(max_pages)) if self.min_pages() > max_pages => {
                errors.push(TypeErrorKind::StaticOutsideMax { end, max_pages });
            }
            _ => {}
        }
        if !self.data_fits() {
            errors.push(TypeErrorKind::DataTooLarge {
                bytes: self.data_end - u128::from(start),
                capacity: self.data_limit - start,
            });
        }
        self.errors.extend(errors.into_iter().map(|kind| TypeError {
            kind,
            span: None,
            instances: Vec::new(),
        }));
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

    /// Lowers every function the source defines that isn't generic, but for
    /// those lowered for a constant to call, which are lowered already.
    fn lower_funcs(&mut self, program: &Program) -> Vec<ir::Func> {
        let mut funcs = Vec::new();
        for (i, (item, decl)) in fn_decls(program).enumerate() {
            let id = FuncId(self.import_count + i as u32);
            let func = match self.lowered.remove(&id) {
                Some(func) => func,
                None => self.lower_decl(program, id, item, decl),
            };
            funcs.push(func);
        }
        funcs
    }

    /// Lowers function `id`, which `decl` of `item` defines.
    fn lower_decl(
        &mut self,
        program: &Program,
        id: FuncId,
        item: &parse::Item,
        decl: &parse::FnDecl,
    ) -> ir::Func {
        self.module = item.span.file;
        let sig = self.funcs[id.0 as usize].clone();
        self.record_params(&decl.sig, &sig);
        let export = self.exports(item).then(|| sig.name.clone());
        self.lower_body(program, sig, &decl.body, item.span, export)
    }

    /// Lowers a function of `program` with signature `sig` and body `block`,
    /// declared by the item spanning `span`, and exported as `export` if
    /// given.
    fn lower_body(
        &mut self,
        program: &Program,
        sig: FuncSig,
        block: &parse::Block,
        span: Span,
        export: Option<String>,
    ) -> ir::Func {
        let returns = diverges(block);
        let mut body = Body::new(self, sig.ret);
        body.program = Some(program);
        // A type parameter is a type by its name, and no variable.
        for (name, ty) in sig.params.iter().filter(|(_, ty)| *ty != Ty::Type) {
            let slots = body.alloc(name, *ty);
            body.bind(name, *ty, false, slots);
        }
        let params = body.locals.iter().map(|local| local.ty).collect();
        let mut stmts = body.block(block);
        let locals = body.locals;
        let results = self.val_types(sig.ret);
        if !matches!(sig.ret, Ty::Unit | Ty::Error) && !returns {
            self.error(TypeErrorKind::MissingReturn(sig.name.clone()), span);
        }
        // Wasm validates the end of a function with results as reachable
        // unless it follows a `return` or `unreachable`.
        let ends_unreachable = matches!(stmts.last(), Some(Stmt::Return(_) | Stmt::Unreachable));
        if !results.is_empty() && !ends_unreachable {
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
    /// others creates, but for those lowered for a constant to call, which
    /// are lowered already.
    fn lower_synths(&mut self, program: &Program) -> Vec<ir::Func> {
        let first = self.funcs.len() - self.synths.len();
        let mut funcs = Vec::new();
        while funcs.len() < self.synths.len() {
            let id = FuncId((first + funcs.len()) as u32);
            let func = match self.lowered.remove(&id) {
                Some(func) => func,
                None => self.lower_synth(program, id),
            };
            funcs.push(func);
        }
        funcs
    }

    /// Lowers function `id`, which is one of `synths`.
    fn lower_synth(&mut self, program: &Program, id: FuncId) -> ir::Func {
        let first = self.funcs.len() - self.synths.len();
        match &self.synths[id.0 as usize - first] {
            Synth::Eq(ty) => self.lower_eq_func(id, *ty),
            Synth::Instance(instance) => {
                let instance = instance.clone();
                self.lower_instance(program, id, instance)
            }
            Synth::Wrapper(import) => self.lower_wrapper(id, *import),
        }
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
            TypeKind::Pointer(mutability, pointee) => match self.resolve_ty(pointee) {
                Ty::Error => Ty::Error,
                // Struct fields are checked once every struct is defined.
                pointee if self.structs_defined && !self.storable(pointee) => {
                    let kind = TypeErrorKind::NotStorable(self.ty_name(pointee));
                    self.error(kind, ty.span);
                    Ty::Error
                }
                pointee => self.ptr_to(pointee, *mutability == Mutability::Var),
            },
            TypeKind::Fn(params, ret) => {
                let params: Vec<_> = params.iter().map(|param| self.resolve_ty(param)).collect();
                let ret = ret.as_ref().map_or(Ty::Unit, |ret| self.resolve_ty(ret));
                match params.contains(&Ty::Error) || ret == Ty::Error {
                    true => Ty::Error,
                    false => self.fn_of(params, ret),
                }
            }
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
            TypeKind::Pointer(..) | TypeKind::Fn(..) => unreachable!("only names are qualified"),
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
            self.error(TypeErrorKind::TypeOutsideParam, span);
            Ty::Error
        } else if let Some(union) = self.builtin_union(name) {
            self.instantiate(union, args, span)
        } else if name == TUPLE && args.is_empty() {
            Ty::Unit
        } else if name == TUPLE {
            self.tuple_of(args)
        } else if name == ARRAY || name == VARRAY {
            match args[0] {
                // Struct fields are checked once every struct is defined.
                elem if self.structs_defined && !self.storable(elem) => {
                    let kind = TypeErrorKind::NotStorable(self.ty_name(elem));
                    self.error(kind, span);
                    Ty::Error
                }
                elem => self.array_of(elem, name == VARRAY),
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
            // A type argument is storable.
            Ty::Param(_) => true,
            // Only the index of a function is stored, whatever it takes.
            Ty::Fn(_) => true,
            // A type is in no value.
            Ty::Type => false,
            Ty::Prim(_) | Ty::Ptr(_) | Ty::Array(_) | Ty::Unit | Ty::Error => true,
        }
    }

    /// The types of a struct's fields, a union's variants, a tuple's
    /// elements, or an array's `ptr` and `len`, in order. Empty for any
    /// other type.
    fn members(&self, ty: Ty) -> Vec<Ty> {
        match ty {
            Ty::Struct(id) => self.structs[id.0 as usize]
                .fields
                .iter()
                .map(|field| field.ty)
                .collect(),
            Ty::Tuple(id) => self.tuples[id.0 as usize].clone(),
            Ty::Array(id) => vec![self.arrays[id.0 as usize], Ty::Prim(Prim::Uint)],
            _ => Vec::new(),
        }
    }

    /// The type of a fixed size that `prim` is held as. An `int` and a
    /// `uint` are as wide as an address: an `i32` and a `u32`, or an `i64`
    /// and a `u64` where addresses are 64 bits wide. Any other is itself.
    fn fixed(&self, prim: Prim) -> Prim {
        match (prim, self.memory64) {
            (Prim::Int, false) => Prim::I32,
            (Prim::Int, true) => Prim::I64,
            (Prim::Uint, false) => Prim::U32,
            (Prim::Uint, true) => Prim::U64,
            _ => prim,
        }
    }

    /// The wasm type of an address, which a pointer, a function pointer, an
    /// `int` and a `uint` each are.
    fn addr_type(&self) -> ValType {
        self.fixed(Prim::Uint).val_type()
    }

    /// The largest address, which is the largest `uint`.
    fn max_addr(&self) -> u64 {
        self.fixed(Prim::Uint).range().1 as u64
    }

    /// The address `n`, or a count of `n` bytes, elements or pages, as a
    /// constant.
    fn addr_const(&self, n: u64) -> Const {
        match self.memory64 {
            true => Const::I64(n as i64),
            false => Const::I32(n as i32),
        }
    }

    /// The constant array of `len` elements at `ptr`.
    fn array_value(&self, ptr: u64, len: u64) -> Value {
        let vt = self.addr_type();
        let consts = [ptr, len].map(|x| (vt, Expr::Const(self.addr_const(x))));
        Value {
            pre: Vec::new(),
            scalars: consts.to_vec(),
        }
    }

    /// The address of element `index` of an array whose elements start at
    /// `ptr` and are `stride` bytes apart.
    fn element_addr(&self, ptr: Expr, index: Expr, stride: u32) -> Expr {
        let vt = self.addr_type();
        let offset = match stride {
            1 => index,
            _ => {
                let stride = Expr::Const(self.addr_const(stride.into()));
                binary(vt, IrBinOp::Mul, index, stride)
            }
        };
        binary(vt, IrBinOp::Add, ptr, offset)
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

    /// The interned type `&pointee`, or `&var pointee` if it's `mutable`.
    fn ptr_to(&mut self, pointee: Ty, mutable: bool) -> Ty {
        let next = PtrId(self.pointees.len() as u32);
        let id = *self.ptr_ids.entry((pointee, mutable)).or_insert(next);
        if id == next {
            self.pointees.push((pointee, mutable));
        }
        Ty::Ptr(id)
    }

    fn pointee(&self, id: PtrId) -> Ty {
        self.pointees[id.0 as usize].0
    }

    /// The interned type `array(elem)`, or `varray(elem)` if it's `mutable`.
    fn array_of(&mut self, elem: Ty, mutable: bool) -> Ty {
        let ptr = self.ptr_to(elem, mutable);
        let next = ArrayId(self.arrays.len() as u32);
        let id = *self.array_ids.entry(ptr).or_insert(next);
        if id == next {
            self.arrays.push(ptr);
        }
        Ty::Array(id)
    }

    /// Whether `ty` is a `&var T` or a `varray(T)`, whose memory can be
    /// written.
    fn writes(&self, ty: Ty) -> bool {
        match ty {
            Ty::Ptr(id) => self.pointees[id.0 as usize].1,
            Ty::Array(id) => self.writes(self.arrays[id.0 as usize]),
            _ => false,
        }
    }

    /// The pointer or array `ty` as one whose memory can be written if
    /// `mutable`, and only read otherwise. Any other type is itself.
    fn with_writes(&mut self, ty: Ty, mutable: bool) -> Ty {
        match ty {
            Ty::Ptr(id) => self.ptr_to(self.pointee(id), mutable),
            Ty::Array(id) => self.array_of(self.element(id), mutable),
            _ => ty,
        }
    }

    /// Whether a `found` can stand where a `want` is expected: it is the
    /// same type, or the `&var T` or `varray(T)` of a `want` that only reads.
    /// Nothing within a type converts.
    fn fits(&self, found: Ty, want: Ty) -> bool {
        found == want
            || match (found, want) {
                (Ty::Ptr(f), Ty::Ptr(w)) => {
                    self.pointee(f) == self.pointee(w) && !self.writes(want)
                }
                (Ty::Array(f), Ty::Array(w)) => {
                    self.fits(self.arrays[f.0 as usize], self.arrays[w.0 as usize])
                }
                _ => false,
            }
    }

    /// The types a pointer, tuple, array, or function type is made of: its
    /// pointee, elements, element type, or parameters and then result. Empty
    /// for any other type.
    fn components(&self, ty: Ty) -> Vec<Ty> {
        match ty {
            Ty::Ptr(id) => vec![self.pointee(id)],
            Ty::Tuple(id) => self.tuples[id.0 as usize].clone(),
            Ty::Array(id) => vec![self.element(id)],
            Ty::Fn(id) => {
                let (params, ret) = &self.fn_tys[id.0 as usize];
                params.iter().copied().chain([*ret]).collect()
            }
            _ => Vec::new(),
        }
    }

    /// The type shaped like `ty` but made of `components`, as
    /// [`Self::components`] takes it apart. Any other type is itself.
    fn rebuild(&mut self, ty: Ty, mut components: Vec<Ty>) -> Ty {
        match ty {
            Ty::Ptr(_) => self.ptr_to(components[0], self.writes(ty)),
            Ty::Tuple(_) => self.tuple_of(components),
            Ty::Array(_) => self.array_of(components[0], self.writes(ty)),
            Ty::Fn(_) => {
                let ret = components.pop().unwrap();
                self.fn_of(components, ret)
            }
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
            Ty::Ptr(id) if self.writes(ty) => format!("&var {}", self.ty_name(self.pointee(id))),
            Ty::Ptr(id) => format!("&{}", self.ty_name(self.pointee(id))),
            Ty::Array(id) => {
                let name = if self.writes(ty) { VARRAY } else { ARRAY };
                format!("{name}({})", self.ty_name(self.element(id)))
            }
            Ty::Tuple(id) => {
                let elems: Vec<_> = self.tuples[id.0 as usize]
                    .iter()
                    .map(|elem| self.ty_name(*elem))
                    .collect();
                format!("{TUPLE}({})", elems.join(", "))
            }
            Ty::Fn(id) => {
                let (params, ret) = &self.fn_tys[id.0 as usize];
                let params: Vec<_> = params.iter().map(|param| self.ty_name(*param)).collect();
                let ret = match ret {
                    Ty::Unit => String::new(),
                    ret => format!(" -> {}", self.ty_name(*ret)),
                };
                format!("fn({}){ret}", params.join(", "))
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
        let ty = self.known(ty);
        match ty {
            Ty::Prim(prim) => out.push((name, self.fixed(prim).val_type())),
            Ty::Ptr(_) | Ty::Fn(_) => out.push((name, self.addr_type())),
            Ty::ExternRef => out.push((name, ValType::ExternRef)),
            Ty::Enum(id) => self.push_leaves(self.enum_ty(id), name, out),
            Ty::Struct(id) => {
                // A union's tag has the name of the union itself, and the
                // leaves its variants share are named by index.
                if self.union_id(ty).is_some() {
                    out.push((name.clone(), ValType::I32));
                    let shared = self.union_leaves(id).0.into_iter().enumerate();
                    out.extend(shared.map(|(i, vt)| (format!("{name}.{i}"), vt)));
                    return;
                }
                for field in &self.structs[id.0 as usize].fields {
                    self.push_leaves(field.ty, format!("{name}.{}", field.name), out);
                }
            }
            Ty::Tuple(id) => {
                for (i, elem) in self.tuples[id.0 as usize].iter().enumerate() {
                    self.push_leaves(*elem, format!("{name}.{i}"), out);
                }
            }
            Ty::Array(_) => {
                for (field, member) in ARRAY_FIELDS.iter().zip(self.members(ty)) {
                    self.push_leaves(member, format!("{name}.{field}"), out);
                }
            }
            Ty::Param(_) | Ty::Type | Ty::Unit | Ty::Error => {}
        }
    }

    fn val_types(&self, ty: Ty) -> Vec<ValType> {
        self.leaves(ty, "").into_iter().map(|(_, vt)| vt).collect()
    }

    /// The leaves of a value of type `ty`, in order.
    fn leaf_list(&self, ty: Ty) -> Vec<Leaf> {
        let leaves = self.val_types(ty).into_iter().enumerate();
        leaves.map(|(index, ty)| Leaf { index, ty }).collect()
    }

    /// Each of the [members](Self::members) of `ty`, and which of `leaves`,
    /// those of a `ty`, hold it: the leaves that follow those of the member
    /// before, or for a union's variant, those after the tag that it shares
    /// with the others.
    fn member_leaves(&self, ty: Ty, leaves: &[Leaf]) -> Vec<(Ty, Vec<Leaf>)> {
        let members = self.members(ty);
        if let Some(id) = self.union_id(ty) {
            let held = self.union_leaves(id).1.into_iter();
            let held = held.map(|held| held.into_iter().map(|leaf| leaves[leaf]).collect());
            return members.into_iter().zip(held).collect();
        }
        let mut rest = leaves;
        let mut out = Vec::new();
        for member in members {
            let (held, after) = rest.split_at(self.val_types(member).len());
            out.push((member, held.to_vec()));
            rest = after;
        }
        out
    }

    /// The narrow integers and `bool`s in a value of type `ty`.
    fn ranged(&self, ty: Ty) -> Vec<Ranged> {
        let mut out = Vec::new();
        self.push_ranged(ty, &self.leaf_list(ty), &[], &mut out);
        out
    }

    /// Pushes those of a `ty` held in `leaves`, which holds nothing unless
    /// every union of `when` holds its variant.
    fn push_ranged(&self, ty: Ty, leaves: &[Leaf], when: &[Holds], out: &mut Vec<Ranged>) {
        match ty {
            Ty::Prim(prim) if self.fixed(prim).size() < 4 => out.push(Ranged {
                leaf: leaves[0],
                prim,
                when: when.to_vec(),
            }),
            Ty::Enum(id) => self.push_ranged(self.enum_ty(id), leaves, when, out),
            Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_) => {
                let union = self.union_id(ty).is_some();
                let members = self.member_leaves(ty, leaves).into_iter();
                for (index, (member, held)) in members.enumerate() {
                    let mut when = when.to_vec();
                    if union {
                        when.push(Holds::new(leaves[0], index));
                    }
                    self.push_ranged(member, &held, &when, out);
                }
            }
            _ => {}
        }
    }

    /// The type of `field` in `ty`, the range of `ty`'s leaves it covers, and
    /// its offset in memory. A tuple's fields are its indices. `None` after
    /// reporting an error.
    fn field(&mut self, ty: Ty, field: &parse::Ident) -> Option<(Ty, Range<usize>, u32)> {
        // A bounded type parameter has the fields of its bound.
        let (written, ty) = (ty, self.read_as(ty, field));
        let index = match ty {
            // A union's variants are only read by `match`.
            Ty::Struct(id) if self.union_id(ty).is_none() => self.structs[id.0 as usize]
                .fields
                .iter()
                .position(|def| def.name == field.name),
            Ty::Tuple(id) => field
                .name
                .parse()
                .ok()
                .filter(|i| *i < self.tuples[id.0 as usize].len()),
            Ty::Array(_) => ARRAY_FIELDS.iter().position(|name| *name == field.name),
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
                ty: self.ty_name(written),
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
            (Ty::Prim(from), Ty::Prim(as_)) if convertible(from, as_) => {
                let (from, as_) = (self.fixed(from), self.fixed(as_));
                let value = map1(value, as_.val_type(), |e| convert(from, as_, e));
                Some((to, value))
            }
            // A pointer is one that reads what it writes, and one to what
            // its pointee starts as.
            (Ty::Ptr(have), Ty::Ptr(want))
                if self.fits(from, to) || self.points_to_start(have, want) =>
            {
                Some((to, value))
            }
            // A `varray` is an array of the same elements.
            (Ty::Array(_), Ty::Array(_)) if self.fits(from, to) => Some((to, value)),
            // A pointer converts to its address, and a function pointer to
            // its index in the table.
            (Ty::Ptr(_) | Ty::Fn(_), Ty::Prim(Prim::Uint | Prim::Int)) => Some((to, value)),
            // An enum is one that starts as it does, as its values are.
            (Ty::Enum(_), Ty::Enum(_)) if self.meets(from, to) => Some((to, value)),
            // A union is one that starts as it does, and holds the same
            // variant of it.
            (Ty::Struct(have), Ty::Struct(want))
                if self.union_id(from).is_some() && self.meets(from, to) =>
            {
                Some((to, self.widen_union(have, want, value)))
            }
            // An enum casts to whatever the type of its values does.
            (Ty::Enum(id), to) => self.cast_value(self.enum_ty(id), to, value),
            _ => None,
        }
    }

    /// Whether a pointer `from` is one to what `to` points to, with no more
    /// than that known of either: its pointee is a struct that starts as
    /// that of `to` does, which `to` writes only if `from` does. A union
    /// that starts as another is laid out otherwise.
    fn points_to_start(&self, from: PtrId, to: PtrId) -> bool {
        let (have, writes) = self.pointees[from.0 as usize];
        let (want, written) = self.pointees[to.0 as usize];
        let is_struct = matches!(want, Ty::Struct(_)) && !self.is_sum(want);
        (writes || !written) && is_struct && self.meets(have, want)
    }

    /// How many of the scalars of a `from` are a `to`, if `from as to` is a
    /// struct as one that it starts as, which its first fields are.
    fn starting_scalars(&self, from: Ty, to: Ty) -> Option<usize> {
        let is_struct = |ty| matches!(ty, Ty::Struct(_)) && !self.is_sum(ty);
        let starts = from != to && is_struct(from) && is_struct(to) && self.meets(from, to);
        starts.then(|| self.val_types(to).len())
    }

    /// Whether `from as! to` is a cast, which leaves the value as it is: to
    /// a pointer or a function pointer from another or from an address, or
    /// between an array and a `varray` of the same elements. Nothing says
    /// that the value is a `to`.
    fn reinterprets(&self, from: Ty, to: Ty) -> bool {
        match (from, to) {
            (Ty::Ptr(_) | Ty::Prim(Prim::Uint | Prim::Int), Ty::Ptr(_))
            | (Ty::Fn(_) | Ty::Prim(Prim::Uint | Prim::Int), Ty::Fn(_)) => true,
            (Ty::Array(from), Ty::Array(to)) => self.element(from) == self.element(to),
            // An enum casts as the type of its values does.
            (Ty::Enum(id), to) => self.reinterprets(self.enum_ty(id), to),
            _ => false,
        }
    }

    /// Whether `from as! to` is a number as the one with its bits: an
    /// integer and a float of one width, which an `int` or a `uint` has
    /// none of, being as wide as an address.
    fn shares_bits(&self, from: Ty, to: Ty) -> bool {
        let (Ty::Prim(from), Ty::Prim(to)) = (from, to) else {
            return false;
        };
        let sized = |prim: Prim| !matches!(prim, Prim::Int | Prim::Uint);
        let pair = |int: Prim, float: Prim| {
            int.is_int() && float.is_float() && sized(int) && int.size() == float.size()
        };
        pair(from, to) || pair(to, from)
    }

    /// Whether `from as to` casts between a pointer or function pointer and
    /// an integer.
    fn casts_address(&self, from: Ty, to: Ty) -> bool {
        let address = |ty| matches!(ty, Ty::Ptr(_) | Ty::Fn(_));
        let integer = |ty| matches!(ty, Ty::Prim(prim) if prim.is_int());
        (address(from) && integer(to)) || (integer(from) && address(to))
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
            PatternKind::Name(name) => {
                self.record(pattern.span, ty);
                out.push(Bound {
                    name,
                    span: pattern.span,
                    ty,
                    leaves: start..start + self.val_types(ty).len(),
                });
            }
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
            PatternKind::Variant(..) | PatternKind::Literal(_) | PatternKind::Array(_) => {
                unreachable!("only an arm of a `match` has one")
            }
        }
    }

    /// Size and alignment of `ty` in memory.
    fn layout(&self, ty: Ty) -> (u32, u32) {
        let ty = self.known(ty);
        match ty {
            Ty::Prim(prim) => {
                let size = self.fixed(prim).size();
                (size, size)
            }
            Ty::Ptr(_) | Ty::Fn(_) => self.layout(Ty::Prim(Prim::Uint)),
            Ty::Enum(id) => self.layout(self.enum_ty(id)),
            Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_) => {
                if let Some(id) = self.union_id(ty) {
                    let (_, size, align) = self.union_layout(id);
                    return (size, align);
                }
                let (_, size, align) = self.aggregate_layout(ty);
                (size, align)
            }
            // Never in memory, but a struct holding one still has a layout
            // that `field` asks for.
            Ty::ExternRef | Ty::Param(_) | Ty::Type | Ty::Unit | Ty::Error => (0, 1),
        }
    }

    /// Member offsets, size, and alignment of a struct, tuple or array, laid
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

    /// Where each scalar of `ty` lives in memory, in the order they are
    /// laid out, a union's tag before each of its variants in turn.
    fn cells(&self, ty: Ty) -> Vec<Cell> {
        let mut out = Vec::new();
        self.push_cells(ty, 0, &self.leaf_list(ty), &[], &mut out);
        out
    }

    /// Pushes the cells of a `ty` at `offset` whose value `leaves` hold,
    /// which hold nothing unless every union of `when` holds its variant.
    fn push_cells(
        &self,
        ty: Ty,
        offset: u32,
        leaves: &[Leaf],
        when: &[Holds],
        out: &mut Vec<Cell>,
    ) {
        let when = when.to_vec();
        let ty = self.known(ty);
        match ty {
            Ty::Prim(prim) => {
                let fixed = self.fixed(prim);
                out.push(Cell {
                    offset,
                    leaf: leaves[0],
                    ty: fixed.val_type(),
                    load: fixed.load(),
                    store: fixed.store(),
                    bool: prim == Prim::Bool,
                    when,
                });
            }
            Ty::Ptr(_) | Ty::Fn(_) => out.push(Cell {
                offset,
                leaf: leaves[0],
                ty: self.addr_type(),
                load: LoadOp::Load,
                store: StoreOp::Store,
                bool: false,
                when,
            }),
            Ty::Enum(id) => self.push_cells(self.enum_ty(id), offset, leaves, &when, out),
            Ty::Struct(id) if self.union_id(ty).is_some() => {
                self.push_cells(Ty::Prim(unions::TAG), offset, leaves, &when, out);
                let start = offset + self.union_layout(id).0;
                let variants = self.member_leaves(ty, leaves).into_iter();
                for (index, (variant, held)) in variants.enumerate() {
                    let mut when = when.clone();
                    when.push(Holds::new(leaves[0], index));
                    self.push_cells(variant, start, &held, &when, out);
                }
            }
            Ty::Struct(_) | Ty::Tuple(_) | Ty::Array(_) => {
                let offsets = self.aggregate_layout(ty).0;
                let members = self.member_leaves(ty, leaves).into_iter();
                for ((member, held), member_offset) in members.zip(offsets) {
                    self.push_cells(member, offset + member_offset, &held, &when, out);
                }
            }
            Ty::ExternRef => unreachable!("`externref` has no pointer type"),
            Ty::Param(_) | Ty::Type | Ty::Unit | Ty::Error => {}
        }
    }

    /// Writes a value whose scalars are `consts` to the start of `out`, as
    /// storing it to `cells` would.
    fn write_consts(&self, out: &mut [u8], cells: &[Cell], consts: &[Const]) {
        for cell in cells {
            // A value that failed to fold, or is stored when it is run,
            // lacks some.
            let Some(c) = consts.get(cell.leaf.index) else {
                continue;
            };
            let held = cell.when.iter().all(|holds| holds.in_consts(consts));
            if let Expr::Const(c) = narrow(cell.leaf.ty, cell.ty, Expr::Const(*c))
                && held
            {
                write_const(&mut out[cell.offset as usize..], cell.store, c);
            }
        }
    }

    /// Places `bytes`, which hold `len` elements, in memory at the next
    /// multiple of `align`, or right at the end if there are none. Returns the
    /// array of them.
    fn push_data(&mut self, bytes: Vec<u8>, align: u32, len: u64) -> Value {
        let ptr = self.place_data(bytes, align);
        self.array_value(ptr, len)
    }

    /// Places `bytes` in memory at the next multiple of `align`, or right
    /// at the end if there are none. Returns their address.
    fn place_data(&mut self, bytes: Vec<u8>, align: u32) -> u64 {
        let offset = self.reserve_data(bytes.len() as u128, align);
        if !bytes.is_empty() {
            self.data.push(ir::Data { offset, bytes });
        }
        offset
    }

    /// Makes room in memory for `size` bytes at the next multiple of `align`,
    /// or right at the end if there are none. Returns their address, which
    /// is only meaningful while the data fits.
    fn reserve_data(&mut self, size: u128, align: u32) -> u64 {
        let mut offset = self.data_end;
        if size > 0 {
            offset = offset.next_multiple_of(align.into());
            self.data_end = offset + size;
        }
        offset as u64
    }

    /// Places `count` copies of a `ty` whose scalars are `consts` in memory.
    /// Returns the address of the first.
    fn repeat_data(&mut self, ty: Ty, consts: Vec<Const>, count: u64) -> u64 {
        let (size, align) = self.layout(ty);
        let mut bytes = vec![0; size as usize];
        self.write_consts(&mut bytes, &self.cells(ty), &consts);
        let offset = self.reserve_data(u128::from(size) * u128::from(count), align);
        // Memory starts out zeroed, and data that doesn't fit is an error, so
        // neither is written out.
        let zeroed = count == 0 || bytes.iter().all(|&byte| byte == 0);
        if !zeroed && self.data_fits() {
            let bytes = bytes.repeat(count as usize);
            self.data.push(ir::Data { offset, bytes });
        } else if self.eval.is_some() && self.data_fits() {
            // Code that has run may have written there.
            self.zeroed.push((offset, u64::from(size) * count));
        }
        offset
    }

    /// Whether every literal placed so far is within the static data
    /// section, or within memory if the section is fitted to them.
    fn data_fits(&self) -> bool {
        self.data_end <= self.data_limit.into()
    }

    /// Evaluates each scalar of a lowered constant without running it.
    /// Stops at the first that can't be.
    fn fold_value(&self, value: &Value) -> Result<Vec<Const>, Fold> {
        if !value.pre.is_empty() {
            return Err(Fold::NotConstant);
        }
        let scalars = value.scalars.iter();
        scalars.map(|(_, scalar)| self.fold(scalar)).collect()
    }

    /// Evaluates a lowered global initializer without running it.
    fn fold(&self, expr: &Expr) -> Result<Const, Fold> {
        match expr {
            Expr::Const(c) => Ok(*c),
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
            // Only a `var` is read from a global, and may have been
            // assigned.
            Expr::Local(_)
            | Expr::Global(_)
            | Expr::Call(..)
            | Expr::CallIndirect { .. }
            | Expr::Load { .. }
            | Expr::MemorySize
            | Expr::MemoryGrow(_)
            | Expr::Seq(..) => Err(Fold::NotConstant),
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
            global: None,
            program: None,
            default: false,
            piped: Vec::new(),
            assigned: Vec::new(),
        }
    }

    fn error(&mut self, kind: TypeErrorKind, span: Span) {
        self.ck.error(kind, span);
    }

    /// Whether the constants of item `index` of the program are folded,
    /// which a global initializer that is first to use them has done here.
    /// Otherwise reports why `name`, used at `span`, has none.
    fn folded(&mut self, index: usize, name: &str, span: Span) -> bool {
        self.ck
            .folded(self.global.or(self.program), index, name, span)
    }

    /// Reports a mismatch unless `found` fits where `want` is expected or
    /// either is an error.
    fn expect(&mut self, found: Ty, want: Ty, span: Span) {
        if self.ck.fits(found, want) || found == Ty::Error || want == Ty::Error {
            return;
        }
        let kind = TypeErrorKind::Mismatch {
            expected: self.ck.ty_name(want),
            found: self.ck.ty_name(found),
        };
        self.error(kind, span);
    }

    /// A value of type `ty` that is never run: the result of a call in a
    /// generic function checked as declared, which calls no instance.
    fn blank(&self, ty: Ty) -> Value {
        let zeros = self.ck.val_types(ty).into_iter().map(zero);
        self.scalars(ty, zeros.map(Expr::Const).collect())
    }

    /// The type parameter `expr` names, if it's the name of one that no
    /// variable or item shadows, and the type it stands for.
    fn param_named(&self, expr: &parse::Expr) -> Option<Ty> {
        match &expr.kind {
            ExprKind::Name(name) if self.lookup(name).is_none() && self.ck.item(name).is_none() => {
                self.ck.type_param(name)
            }
            _ => None,
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
        self.push_local(TEMP.to_string(), ty)
    }

    /// Names the temporary `local` for what it turned out to hold, unless
    /// it has a name.
    fn name_temp(&mut self, local: LocalId, name: String) {
        let local = &mut self.locals[local.0 as usize];
        if local.name == TEMP {
            local.name = name;
        }
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
        let outer = mem::replace(&mut self.assigned, assigned_within(stmt));
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
            StmtKind::Expr(expr) => {
                let value = match &expr.kind {
                    // Nothing reads what a statement assigns.
                    ExprKind::Assign { target, op, value } => {
                        self.assignment(target, *op, value, expr.span, false).1
                    }
                    _ => self.expr(expr, None).1,
                };
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
            StmtKind::Match { value, arms } => self.match_stmt(value, arms, out),
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
        self.assigned = outer;
    }

    /// `target = value`, or `target op= value` if `op` is given. The target
    /// is found, then the value is evaluated, and then it is stored. If it's
    /// `used`, the value of the assignment is the one stored. Otherwise it
    /// has none.
    fn assignment(
        &mut self,
        target: &parse::Expr,
        op: Option<BinOp>,
        value: &parse::Expr,
        span: Span,
        used: bool,
    ) -> (Ty, Value) {
        let Some(mut place) = self.place(target) else {
            self.expr(value, None);
            return (Ty::Error, Value::default());
        };
        let mut pre = mem::take(&mut place.pre);
        if !place.mutable {
            let kind = match place.behind {
                Some(ty) => {
                    let (ty, needs, element) = self.read_only(ty);
                    TypeErrorKind::ReadOnlyWrite { ty, needs, element }
                }
                None => TypeErrorKind::ImmutableAssign(place.name.clone()),
            };
            self.error(kind, target.span);
        }
        let mut value = match op {
            None => self.check(value, place.ty),
            Some(op) => {
                let current = self.read_place(&place);
                let rhs = self.check(value, place.ty);
                self.binary_values(op, place.ty, current, rhs, span).1
            }
        };
        if !used {
            self.assign(&place, value, &mut pre);
            let scalars = Vec::new();
            return (place.ty, Value { pre, scalars });
        }
        // Read again as the value of the assignment, so held where storing
        // it changes nothing: a variable that is assigned here is read into
        // temporaries, and so none of these locals is the target's.
        self.spill(&mut value, is_simple);
        pre.extend(value.pre);
        let scalars = value.scalars;
        let cells = self.cells(&place);
        self.store(&place, &cells, exprs(scalars.clone()), &mut pre);
        // Only a mistyped value has other scalars than its type's.
        let ty = match scalars.len() == self.ck.val_types(place.ty).len() {
            true => place.ty,
            false => Ty::Error,
        };
        (ty, Value { pre, scalars })
    }

    /// `for var in iter`, which copies each element of the array `iter`, or
    /// each member of the enum `iter` names, to `var` in turn. The array's
    /// `ptr` and `len` are read once, before the first iteration.
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
        self.ck.record(var.span, elem);
        let vt = self.ck.addr_type();
        let (ptr, len, index) = (self.temp(vt), self.temp(vt), self.temp(vt));
        let [zero, one] = [0, 1].map(|n| Expr::Const(self.ck.addr_const(n)));
        out.extend(value.pre);
        let mut scalars = exprs(value.scalars).into_iter();
        for dest in [ptr, len] {
            let scalar = scalars.next().unwrap_or(zero.clone());
            out.push(Stmt::SetLocal(dest, scalar));
        }
        out.push(Stmt::SetLocal(index, zero));
        let i = Expr::Local(index);
        let done = binary(vt, IrBinOp::GeU, i.clone(), Expr::Local(len));
        let mut inner = vec![Stmt::BrIf(1, done)];
        let stride = self.ck.layout(elem).0;
        let addr = self.ck.element_addr(Expr::Local(ptr), i.clone(), stride);
        let element = self.load(scalar(vt, addr), 0, elem);
        let slots = self.alloc(&var.name, elem);
        inner.extend(element.pre);
        for (slot, (_, scalar)) in slots.iter().zip(element.scalars) {
            inner.push(Stmt::SetLocal(*slot, scalar));
        }
        // Advanced before the body, so `continue` moves on too.
        let next = binary(vt, IrBinOp::Add, i, one);
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

    /// What an error says of `ty`, a pointer or array that only reads its
    /// memory: its name, that of the type that writes it, and whether it's
    /// the array.
    fn read_only(&mut self, ty: Ty) -> (String, String, bool) {
        let needs = self.ck.with_writes(ty, true);
        let element = matches!(ty, Ty::Array(_));
        (self.ck.ty_name(ty), self.ck.ty_name(needs), element)
    }

    /// Resolves an assignment target. `None` after reporting an error.
    fn place(&mut self, target: &parse::Expr) -> Option<Place> {
        let place = self.find_place(target)?;
        self.ck.record(target.span, place.ty);
        Some(place)
    }

    /// [`Self::place`], but for keeping the type.
    fn find_place(&mut self, target: &parse::Expr) -> Option<Place> {
        match &target.kind {
            ExprKind::Name(name) => {
                if let Some(var) = self.lookup(name) {
                    let place = Place {
                        name: name.clone(),
                        ty: var.ty,
                        mutable: var.mutable,
                        behind: None,
                        pre: Vec::new(),
                        slots: Slots::Local(var.slots.clone()),
                    };
                    return Some(place);
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
                        (ty @ Ty::Ptr(_), ptr) => self.deref_place(ptr, ty),
                        (Ty::Error, _) => return None,
                        _ => {
                            self.error(TypeErrorKind::NotAssignable, target.span);
                            return None;
                        }
                    },
                };
                // Fields are reached through any number of pointers.
                while let Ty::Ptr(_) = place.ty {
                    let ptr = self.read_place(&place);
                    let mut deref = self.deref_place(ptr, place.ty);
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
                    Slots::Const(consts) => Slots::Const(consts[range].to_vec()),
                    Slots::Memory { addr, offset } => Slots::Memory {
                        addr,
                        offset: offset + field_offset,
                    },
                };
                Some(Place { ty, slots, ..place })
            }
            ExprKind::Deref(inner) => match self.expr(inner, None) {
                (ty @ Ty::Ptr(_), ptr) => Some(self.deref_place(ptr, ty)),
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
        if !self.folded(self.ck.global_items[index], name, span) {
            return None;
        }
        let global = self.ck.globals[index].as_ref()?;
        Some(Place {
            name: name.to_string(),
            ty: global.ty,
            mutable: global.mutable,
            behind: None,
            pre: Vec::new(),
            slots: global.slots.clone(),
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
        let index = self.check(index, Ty::Prim(Prim::Uint));
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
        let [ptr, len, index] = <[_; 3]>::try_from(exprs(value.scalars)).ok()?;
        let mut pre = value.pre;
        let vt = self.ck.addr_type();
        pre.push(Stmt::If {
            cond: binary(vt, IrBinOp::GeU, index.clone(), len),
            then_body: vec![Stmt::Unreachable],
            else_body: Vec::new(),
        });
        let tmp = self.temp(vt);
        let addr = self.ck.element_addr(ptr, index, self.ck.layout(elem).0);
        pre.push(Stmt::SetLocal(tmp, addr));
        Some(Place {
            name: String::new(),
            ty: elem,
            mutable: self.ck.writes(ty),
            behind: Some(ty),
            pre,
            slots: Slots::Memory {
                addr: Expr::Local(tmp),
                offset: 0,
            },
        })
    }

    /// The memory that `ptr`, a pointer of type `ty`, points to, as a place.
    fn deref_place(&mut self, ptr: Value, ty: Ty) -> Place {
        let (pre, addr) = self.reusable_addr(ptr);
        let Ty::Ptr(id) = ty else {
            unreachable!("only pointers are dereferenced")
        };
        Place {
            name: String::new(),
            ty: self.ck.pointee(id),
            mutable: self.ck.writes(ty),
            behind: Some(ty),
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
        let tmp = self.temp(self.ck.addr_type());
        pre.push(Stmt::SetLocal(tmp, addr));
        (pre, Expr::Local(tmp))
    }

    /// Reads a place, not including its `pre`.
    fn read_place(&mut self, place: &Place) -> Value {
        let reads = match &place.slots {
            Slots::Local(slots) => {
                let reads = slots.iter().map(|l| Expr::Local(*l)).collect();
                let value = self.scalars(place.ty, reads);
                return self.read_variable(&place.name, value);
            }
            Slots::Global(slots) => slots.iter().map(|g| Expr::Global(*g)).collect(),
            Slots::Const(consts) => consts.iter().map(|c| Expr::Const(*c)).collect(),
            Slots::Memory { addr, offset } => {
                let ptr = scalar(self.ck.addr_type(), addr.clone());
                return self.load(ptr, *offset, place.ty);
            }
        };
        self.scalars(place.ty, reads)
    }

    /// `value`, read from the locals of the variable `name`. If an
    /// assignment within the statement changes the variable, it is held in
    /// temporaries, which nothing else sets: only then is a local as it was
    /// read however much later it is evaluated.
    fn read_variable(&mut self, name: &str, mut value: Value) -> Value {
        if self.assigned.iter().any(|assigned| assigned == name) {
            self.spill(&mut value, |_| false);
        }
        value
    }

    /// Where each scalar of `place` lives in memory, if it's there.
    fn cells(&self, place: &Place) -> Vec<Cell> {
        match place.slots {
            Slots::Memory { .. } => self.ck.cells(place.ty),
            _ => Vec::new(),
        }
    }

    fn assign(&mut self, place: &Place, mut value: Value, out: &mut Vec<Stmt>) {
        // Every scalar is read before any slot is written, so `p = Point(x:
        // p.y, y: p.x)` swaps. Stores can't change locals.
        let cells = self.cells(place);
        if cells.iter().any(|cell| !cell.when.is_empty()) {
            // A union's tag is read again to store the variant it holds.
            self.spill(&mut value, is_simple);
        } else if value.scalars.len() > 1 {
            match place.slots {
                Slots::Memory { .. } => self.spill(&mut value, is_stable),
                _ => self.spill(&mut value, |e| matches!(e, Expr::Const(_))),
            }
        }
        out.extend(value.pre);
        self.store(place, &cells, exprs(value.scalars), out);
    }

    /// Writes `scalars` to `place`, whose `cells` are those of
    /// [`Self::cells`], in order. Each is read as late as it is written.
    fn store(&self, place: &Place, cells: &[Cell], scalars: Vec<Expr>, out: &mut Vec<Stmt>) {
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
            // Only after an error: an inlined global is immutable.
            Slots::Const(_) => {}
            // Only a mistyped value has other scalars than the place's, and
            // so may lack the tags that say which variants to store.
            Slots::Memory { .. } if scalars.len() != self.ck.val_types(place.ty).len() => {}
            Slots::Memory { addr, offset } => {
                let store = |cell: &Cell| Stmt::Store {
                    ty: cell.ty,
                    op: cell.store,
                    offset: offset + cell.offset,
                    addr: addr.clone(),
                    value: narrow(cell.leaf.ty, cell.ty, scalars[cell.leaf.index].clone()),
                };
                // The cells of a union's variant are stored where the value
                // holds it.
                for variant in cells.chunk_by(|a, b| a.when == b.when) {
                    let stores = variant.iter().map(store).collect();
                    out.extend(where_held(&variant[0].when, &scalars, stores));
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
        // A `.name` that names nothing of the type expected of it is still
        // known to be expected to be of that type.
        let dot = match &expr.kind {
            ExprKind::Dot(_) => true,
            ExprKind::Call(callee, _) => matches!(callee.kind, ExprKind::Dot(_)),
            _ => false,
        };
        if let (true, Some(expected)) = (dot, expected) {
            self.ck.record(expr.span, expected);
        }
        let (ty, value) = self.infer(expr, expected);
        self.ck.record(expr.span, ty);
        (ty, value)
    }

    /// [`Self::expr`], but for keeping the type.
    fn infer(&mut self, expr: &parse::Expr, expected: Option<Ty>) -> (Ty, Value) {
        match &expr.kind {
            ExprKind::Int(n) => self.int_literal(*n as i128, expected, expr.span),
            ExprKind::Float(x) => float_literal(*x, expected),
            ExprKind::Bool(b) => (
                Ty::Prim(Prim::Bool),
                scalar(ValType::I32, Expr::Const(Const::I32(*b as i32))),
            ),
            ExprKind::Unit => (Ty::Unit, Value::default()),
            ExprKind::Str(_) | ExprKind::List(_) | ExprKind::Repeat(..)
                if self.global.is_none() =>
            {
                self.error(TypeErrorKind::LiteralOutsideGlobal, expr.span);
                (Ty::Error, Value::default())
            }
            ExprKind::Str(s) => self.string(s, expected, expr.span),
            ExprKind::List(items) => self.list(items, expected, expr.span),
            ExprKind::Repeat(value, len) => self.repeat(value, len, expected, expr.span),
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
            ExprKind::Name(_)
            | ExprKind::Field(..)
            | ExprKind::AddrOf(..)
            | ExprKind::FnType(_)
                if self.is_type_expr(expr) =>
            {
                let ty = self.expr_type(expr);
                self.type_value(ty, expr.span)
            }
            ExprKind::Name(name) => self.name(name, expected, expr.span),
            ExprKind::Module(name) => self.module_property(name),
            ExprKind::Tuple(elems) => self.tuple(elems, expected),
            ExprKind::Unary(op, operand) => self.unary(*op, operand, expected, expr.span),
            ExprKind::Binary(op, lhs, rhs) => self.binary(*op, lhs, rhs, expected, expr.span),
            ExprKind::Dot(name) => self.dot(name, None, expected),
            ExprKind::Call(callee, args) => match &callee.kind {
                ExprKind::Dot(name) => self.dot(name, Some(args), expected),
                _ => self.call(callee, args, expr.span),
            },
            ExprKind::Field(inner, field) if self.names_module(inner).is_some() => {
                match self.member(inner, field) {
                    Some(item) => self.item_value(item, &field.name, expected, field.span),
                    None => (Ty::Error, Value::default()),
                }
            }
            ExprKind::Field(inner, field) => {
                let type_field = TYPE_FIELDS.contains(&field.name.as_str());
                match self.param_named(inner) {
                    // The `size` and `align` of a type parameter are those of
                    // the type, even if it's an enum with such a member.
                    Some(_) if type_field => {}
                    _ => {
                        let id = self.enum_name(inner);
                        if let Some(member) = id.and_then(|id| self.enum_member(id, field)) {
                            return member;
                        }
                        if let Some(variant) = self.union_variant(inner, field, None) {
                            return variant;
                        }
                    }
                }
                if type_field && self.is_type_expr(inner) {
                    let ty = self.expr_type(inner);
                    return self.type_field(ty, field, inner.span);
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
            ExprKind::Cast(inner, ty, unchecked) => self.cast(inner, ty, *unchecked, expr.span),
            ExprKind::AddrOf(mutability, inner) => {
                self.addr_of(*mutability, inner, expected, expr.span)
            }
            ExprKind::FnType(_) => unreachable!("function types are type expressions"),
            ExprKind::Pipe(value, body) => self.pipe(value, body, expected),
            ExprKind::Placeholder => match self.piped.last() {
                Some((ty, scalars)) => {
                    let scalars = scalars.clone();
                    (
                        *ty,
                        Value {
                            pre: Vec::new(),
                            scalars,
                        },
                    )
                }
                None => unreachable!("the parser rejects `_` outside a pipe"),
            },
            ExprKind::Assign { target, op, value } => {
                self.assignment(target, *op, value, expr.span, true)
            }
        }
    }

    /// `value |> body`. The value is evaluated first and held in temporaries,
    /// which each `_` in the body reads. In a global initializer, what folds
    /// of it is read as its constant.
    fn pipe(
        &mut self,
        value: &parse::Expr,
        body: &parse::Expr,
        expected: Option<Ty>,
    ) -> (Ty, Value) {
        let (value_ty, mut value) = self.expr(value, None);
        self.spill_simple(&mut value);
        self.piped.push((value_ty, value.scalars));
        let (ty, mut result) = self.expr(body, expected);
        self.piped.pop();
        value.pre.append(&mut result.pre);
        result.pre = value.pre;
        (ty, result)
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
            // An element is of the type expected if it fits there.
            let want = expected.get(i).filter(|want| self.ck.fits(ty, **want));
            tys.push(want.copied().unwrap_or(ty));
            values.push(value);
        }
        if tys.contains(&Ty::Error) {
            return (Ty::Error, Value::default());
        }
        (self.ck.tuple_of(tys), self.seq(values))
    }

    /// Whether a literal that is expected to be an `expected` is a `varray`,
    /// as it only is where one is expected.
    fn literal_writes(&self, expected: Option<Ty>) -> bool {
        matches!(expected, Some(ty @ Ty::Array(_)) if self.ck.writes(ty))
    }

    /// Reports a literal of `len` elements at `span` that is `mutable` in a
    /// default, unless it's empty: its elements would be shared wherever the
    /// default is used.
    fn check_shared(&mut self, mutable: bool, len: usize, span: Span) {
        if self.default && mutable && len > 0 {
            self.error(TypeErrorKind::SharedLiteral, span);
        }
    }

    /// A string literal: an array of its UTF-8 bytes.
    fn string(&mut self, s: &str, expected: Option<Ty>, span: Span) -> (Ty, Value) {
        let mutable = self.literal_writes(expected);
        self.check_shared(mutable, s.len(), span);
        let ty = self.ck.array_of(Ty::Prim(Prim::U8), mutable);
        (
            ty,
            self.ck.push_data(s.as_bytes().to_vec(), 1, s.len() as u64),
        )
    }

    /// `module.name`, one of `module`'s constants. `module.static` is the
    /// static data section, as an `array(u8)`, which only reads it. `page_size` is the bytes in a
    /// wasm page, and `min` and `max` are the pages memory starts with and
    /// may grow to, `max` being the largest `uint` if it's unlimited. Each
    /// is a `uint`.
    fn module_property(&mut self, name: &Ident) -> (Ty, Value) {
        let count = match name.name.as_str() {
            "static" => {
                self.ck.read_unfitted |= self.ck.unfitted;
                let StaticSection { start, end } = self.ck.static_section;
                let ty = self.ck.array_of(Ty::Prim(Prim::U8), false);
                return (ty, self.ck.array_value(start, end - start));
            }
            "page_size" => PAGE_SIZE,
            "min" => {
                self.ck.read_unfitted |= self.ck.unfitted && self.ck.memory.min_pages.is_none();
                self.ck.min_pages()
            }
            "max" => self.ck.memory.max_pages.unwrap_or(self.ck.max_addr()),
            other => {
                let kind = if MODULE_FUNCS.contains(&other) {
                    TypeErrorKind::NotAValue(format!("module.{other}"))
                } else {
                    TypeErrorKind::UnknownModuleProperty(other.to_string())
                };
                self.error(kind, name.span);
                return (Ty::Error, Value::default());
            }
        };
        let count = Expr::Const(self.ck.addr_const(count));
        (Ty::Prim(Prim::Uint), scalar(self.ck.addr_type(), count))
    }

    /// `module.name(args)`, one of `module`'s functions, lowered to the
    /// memory instruction it stands for. `memory()` is all of memory as a
    /// `varray(u8)`, `size()` its size in pages as a `uint`, and `grow(pages)`
    /// adds pages, giving the old size as an `int`, or -1 if it can't.
    /// `fill(dst, value, len)` and
    /// `copy(dst, src, len)` set and copy bytes. `unreachable()` traps.
    /// `count_leading_zeros(value)` and `count_trailing_zeros(value)` are
    /// [`Self::count_zeros`].
    fn module_call(&mut self, name: &Ident, args: &[Arg], span: Span) -> (Ty, Value) {
        if [COUNT_LEADING_ZEROS, COUNT_TRAILING_ZEROS].contains(&name.name.as_str()) {
            return self.count_zeros(name, args, span);
        }
        let byte = Ty::Prim(Prim::U8);
        let count = Ty::Prim(Prim::Uint);
        let src = self.ck.ptr_to(byte, false);
        let dst = self.ck.ptr_to(byte, true);
        let params: &[(&str, Ty)] = match name.name.as_str() {
            "memory" | "size" | "unreachable" => &[],
            "grow" => &[("pages", count)],
            "fill" => &[("dst", dst), ("value", byte), ("len", count)],
            "copy" => &[("dst", dst), ("src", src), ("len", count)],
            other => {
                let kind = if MODULE_CONSTS.contains(&other) {
                    TypeErrorKind::NotCallable(format!("module.{other}"))
                } else {
                    TypeErrorKind::UnknownModuleProperty(other.to_string())
                };
                self.error(kind, name.span);
                for arg in args {
                    self.expr(&arg.value, None);
                }
                return (Ty::Error, Value::default());
            }
        };
        let params: Vec<_> = params.iter().map(|(n, ty)| (n.to_string(), *ty)).collect();
        let Value { mut pre, scalars } = self.args(&params, &[], args, false, span);
        // Missing or mistyped arguments, already reported.
        if scalars.len() != params.len() {
            return (Ty::Error, Value::default());
        }
        let mut operands = exprs(scalars).into_iter();
        let mut operand = || operands.next().unwrap();
        let vt = self.ck.addr_type();
        let (ty, scalars) = match name.name.as_str() {
            "memory" => {
                // Wraps to 0 if memory holds every address.
                let page_size = Expr::Const(self.ck.addr_const(PAGE_SIZE));
                let len = binary(vt, IrBinOp::Mul, Expr::MemorySize, page_size);
                let ptr = Expr::Const(self.ck.addr_const(0));
                let ty = self.ck.array_of(byte, true);
                (ty, vec![(vt, ptr), (vt, len)])
            }
            "size" => (count, vec![(vt, Expr::MemorySize)]),
            "grow" => {
                let grow = Expr::MemoryGrow(Box::new(operand()));
                (Ty::Prim(Prim::Int), vec![(vt, grow)])
            }
            "fill" => {
                let (dst, value, len) = (operand(), operand(), operand());
                pre.push(Stmt::MemoryFill { dst, value, len });
                (Ty::Unit, Vec::new())
            }
            "copy" => {
                let (dst, src, len) = (operand(), operand(), operand());
                pre.push(Stmt::MemoryCopy { dst, src, len });
                (Ty::Unit, Vec::new())
            }
            _ => {
                pre.push(Stmt::Unreachable);
                (Ty::Unit, Vec::new())
            }
        };
        (ty, Value { pre, scalars })
    }

    /// `module.count_leading_zeros(value)` and
    /// `module.count_trailing_zeros(value)`, wasm's `clz` and `ctz`: how many
    /// zero bits are above the highest set bit of an integer, or below its
    /// lowest, as a value of its own type. For 0 that is every bit of the
    /// type.
    fn count_zeros(&mut self, name: &Ident, args: &[Arg], span: Span) -> (Ty, Value) {
        let leading = name.name == COUNT_LEADING_ZEROS;
        // The operand may be of any integer type, so it's inferred rather
        // than checked against a parameter's.
        let params = [("value".to_string(), Ty::Error)];
        let binding = self.bind_args(&params, &[], args, false, span);
        let mut ty = Ty::Error;
        let mut checked = Vec::new();
        for (arg, param) in args.iter().zip(&binding) {
            checked.push(param.map(|_| {
                let operand = self.expr(&arg.value, None);
                ty = operand.0;
                operand
            }));
        }
        let value = self.bound_args(&params, &[], args, binding, checked);
        let prim = match ty {
            Ty::Prim(prim) if prim.is_int() => self.ck.fixed(prim),
            _ => {
                let op = match leading {
                    true => "module.count_leading_zeros",
                    false => "module.count_trailing_zeros",
                };
                return self.invalid_operand(op, ty, span);
            }
        };
        let vt = prim.val_type();
        let bits = prim.size() * 8;
        let count = |op, e| Expr::Unary(vt, op, Box::new(e));
        let konst = |n: u32| Expr::Const(Const::I32(n as i32));
        let lowered = |e| match (leading, bits < 32) {
            (true, false) => count(IrUnOp::Clz, e),
            (false, false) => count(IrUnOp::Ctz, e),
            // A narrow integer is held in an `i32`, whose bits above the
            // type's aren't counted. Those of a signed one are copies of its
            // sign, and are cleared first.
            (true, true) => {
                let low = match prim.is_signed() {
                    true => binary(vt, IrBinOp::And, e, konst((1 << bits) - 1)),
                    false => e,
                };
                binary(vt, IrBinOp::Sub, count(IrUnOp::Clz, low), konst(32 - bits))
            }
            // A set bit just above the type's ends the count there.
            (false, true) => count(IrUnOp::Ctz, binary(vt, IrBinOp::Or, e, konst(1 << bits))),
        };
        (ty, map1(value, vt, lowered))
    }

    /// An array literal, whose elements are typed like those of `expected`,
    /// or else like the first element. Its elements are placed in memory
    /// after any literals within them, and one that isn't constant is stored
    /// there when the initializer is run. It's a `varray` where one is
    /// expected.
    fn list(&mut self, items: &[parse::Expr], expected: Option<Ty>, span: Span) -> (Ty, Value) {
        let mutable = self.literal_writes(expected);
        self.check_shared(mutable, items.len(), span);
        let errors = self.ck.errors.len();
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
            let item_consts = self.constant(value, item.span);
            // A mistyped element's scalars don't fit the cells.
            consts.push(match self.ck.fits(ty, want) {
                true => item_consts,
                false => Ok(Vec::new()),
            });
        }
        let Some(elem) = elem else {
            self.error(TypeErrorKind::UntypedEmptyArray, span);
            return (Ty::Error, Value::default());
        };
        if !self.placeable(elem, errors, span) {
            return (Ty::Error, Value::default());
        }
        let (size, align) = self.ck.layout(elem);
        let cells = self.ck.cells(elem);
        let mut bytes = vec![0; size as usize * items.len()];
        for (i, consts) in consts.iter().enumerate() {
            let consts = consts.as_deref().unwrap_or_default();
            self.ck
                .write_consts(&mut bytes[i * size as usize..], &cells, consts);
        }
        let mut value = self.ck.push_data(bytes, align, items.len() as u64);
        let first = match value.scalars.first() {
            Some((_, Expr::Const(Const::I32(addr)))) => u64::from(*addr as u32),
            Some((_, Expr::Const(Const::I64(addr)))) => *addr as u64,
            _ => unreachable!("a literal is placed at a constant address"),
        };
        for (i, item) in consts.into_iter().enumerate() {
            if let Err(item) = item {
                let place = self.placed(elem, first + i as u64 * u64::from(size));
                self.assign(&place, item, &mut value.pre);
            }
        }
        (self.ck.array_of(elem, mutable), value)
    }

    /// Whether a constant of type `ty` can be placed in memory. One that
    /// holds an `externref` is reported at `span`, unless the literal it's
    /// in has an error already, having had `errors` before it: only a union
    /// that holds none in place of one is constant.
    fn placeable(&mut self, ty: Ty, errors: usize, span: Span) -> bool {
        if ty == Ty::Error {
            return false;
        }
        let storable = self.ck.storable(ty);
        if !storable && self.ck.errors.len() == errors {
            self.error(TypeErrorKind::NotStorable(self.ck.ty_name(ty)), span);
        }
        storable
    }

    /// `[value; len]`, an array of `len` copies of `value`, which is typed
    /// like the elements of `expected`. `len` is evaluated here, before the
    /// rest of the initializer, as the copies are placed by it. A `value`
    /// that isn't constant is evaluated once and stored when the initializer
    /// is run. A literal within `value` is placed in memory once, and every
    /// copy views it. It's a `varray` where one is expected.
    fn repeat(
        &mut self,
        value: &parse::Expr,
        len: &parse::Expr,
        expected: Option<Ty>,
        span: Span,
    ) -> (Ty, Value) {
        let mutable = self.literal_writes(expected);
        let want = match expected {
            Some(Ty::Array(id)) => Some(self.ck.element(id)),
            // An array type that failed to resolve, already reported.
            Some(Ty::Error) => Some(Ty::Error),
            _ => None,
        };
        let errors = self.ck.errors.len();
        let (ty, lowered) = self.expr(value, want);
        let elem = want.unwrap_or(ty);
        self.expect(ty, elem, value.span);
        let consts = self.constant(lowered, value.span);
        let lowered = self.check(len, Ty::Prim(Prim::Uint));
        let count = self.evaluate(lowered, len.span).unwrap_or_default();
        if !self.ck.fits(ty, elem) || !self.placeable(elem, errors, span) {
            return (Ty::Error, Value::default());
        }
        let count = match count[..] {
            [Const::I32(count)] => (count as u32).into(),
            [Const::I64(count)] => count as u64,
            _ => return (Ty::Error, Value::default()),
        };
        let len = usize::try_from(count).unwrap_or(usize::MAX);
        self.check_shared(mutable, len, span);
        let (consts, stored) = match consts {
            Ok(consts) => (consts, None),
            Err(stored) => (Vec::new(), Some(stored)),
        };
        let offset = self.ck.repeat_data(elem, consts, count);
        let mut value = self.ck.array_value(offset, count);
        if let Some(stored) = stored {
            value.pre = self.fill(elem, stored, offset, count);
        }
        (self.ck.array_of(elem, mutable), value)
    }

    /// An integer literal, typed by `expected` and defaulting to `i32`. Where
    /// a pointer is expected, it is an address.
    fn int_literal(&mut self, n: i128, expected: Option<Ty>, span: Span) -> (Ty, Value) {
        if let Some(ptr @ Ty::Ptr(_)) = expected {
            if n < 0 || n > self.ck.max_addr().into() {
                self.error(TypeErrorKind::IntOutOfRange(self.ck.ty_name(ptr)), span);
            }
            let addr = Expr::Const(self.ck.addr_const(n as u64));
            return (ptr, scalar(self.ck.addr_type(), addr));
        }
        let prim = match expected {
            Some(Ty::Prim(prim)) if prim.is_numeric() => prim,
            _ => Prim::I32,
        };
        if prim.is_float() {
            return float_literal(n as f64, expected);
        }
        let fixed = self.ck.fixed(prim);
        let (min, max) = fixed.range();
        if n < min || n > max {
            self.error(TypeErrorKind::IntOutOfRange(prim.name().to_string()), span);
        }
        let value = match fixed.val_type() {
            ValType::I64 => Const::I64(n as i64),
            _ => Const::I32(n as i32),
        };
        (Ty::Prim(prim), scalar(fixed.val_type(), Expr::Const(value)))
    }

    /// The value of the variable or item `name`. `expected` picks the
    /// instance of a generic function.
    fn name(&mut self, name: &str, expected: Option<Ty>, span: Span) -> (Ty, Value) {
        if let Some(var) = self.lookup(name) {
            let ty = var.ty;
            let reads = var.slots.iter().map(|l| Expr::Local(*l)).collect();
            let value = self.scalars(ty, reads);
            return (ty, self.read_variable(name, value));
        }
        match self.ck.item(name) {
            Some(item) => self.item_value(item, name, expected, span),
            None => {
                self.error(TypeErrorKind::UnknownName(name.to_string()), span);
                (Ty::Error, Value::default())
            }
        }
    }

    /// The value of `item`, named `name` at `span`. `expected` picks the
    /// instance of a generic function.
    fn item_value(
        &mut self,
        item: Item,
        name: &str,
        expected: Option<Ty>,
        span: Span,
    ) -> (Ty, Value) {
        match item {
            Item::Func(id) => self.func_value(id),
            Item::GenericFn(generic) => self.generic_fn_value(generic, expected, span),
            Item::Global(_) => match self.item_place(item, name, span) {
                Some(place) => (place.ty, self.read_place(&place)),
                None => (Ty::Error, Value::default()),
            },
            // Struct and enum names are types, which `expr` makes values.
            Item::Struct(_) | Item::Enum(_) | Item::Module(_) => {
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
    /// a pointer to one of those, or a function type.
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
            ExprKind::AddrOf(_, pointee) => self.is_type_expr(pointee),
            ExprKind::FnType(_) => true,
            _ => false,
        }
    }

    /// Reports the type `ty`, written at `span` where a value belongs. A
    /// type is no value: it is written as the argument of a type parameter,
    /// or for its `size` or `align`, neither of which is read here.
    fn type_value(&mut self, ty: Ty, span: Span) -> (Ty, Value) {
        if ty != Ty::Error {
            self.error(TypeErrorKind::NotAValue(self.ck.ty_name(ty)), span);
        }
        (Ty::Error, Value::default())
    }

    /// `ty.field`, where `ty` is a type written at `span` and `field` is
    /// `size` or `align`: how many bytes a `ty` takes in memory, or what its
    /// address is a multiple of. So `ty` must be storable.
    fn type_field(&mut self, ty: Ty, field: &Ident, span: Span) -> (Ty, Value) {
        if ty == Ty::Error {
            return (Ty::Error, Value::default());
        }
        if !self.ck.storable(ty) {
            self.error(TypeErrorKind::NotStorable(self.ck.ty_name(ty)), span);
            return (Ty::Error, Value::default());
        }
        let (size, align) = self.ck.layout(ty);
        let bytes = match field.name == TYPE_FIELDS[0] {
            true => size,
            false => align,
        };
        let value = Expr::Const(self.ck.addr_const(bytes.into()));
        (Ty::Prim(Prim::Uint), scalar(self.ck.addr_type(), value))
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
        let prim = match ty {
            Ty::Prim(prim) => self.ck.fixed(prim),
            _ => {
                let symbol = if op == UnaryOp::Neg { "-" } else { "~" };
                return self.invalid_operand(symbol, ty, span);
            }
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

    /// Reports that `op` can't be applied to a `ty`, unless `ty` is an
    /// error.
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
            // `x + 1` and `1 + x` work for any integer `x`, and so does a
            // `.name`, as in `.red == c`.
            if is_typed_by_other(lhs) && !is_typed_by_other(rhs) {
                let (ty, rhs) = self.expr(rhs, expected);
                let ty = self.compared(op, ty);
                (ty, self.check(lhs, ty), rhs)
            } else {
                let (ty, lhs) = self.expr(lhs, expected);
                let ty = self.compared(op, ty);
                (ty, lhs, self.check(rhs, ty))
            }
        };
        self.binary_values(op, ty, lhs, rhs, span)
    }

    /// The type both operands of `op` have when one is a `ty`. Comparing
    /// writes nothing, so a `&var T` compares as a `&T`, with either, and a
    /// `varray(T)` as an `array(T)`.
    fn compared(&mut self, op: BinOp, ty: Ty) -> Ty {
        match is_comparison(op) {
            true => self.ck.with_writes(ty, false),
            false => ty,
        }
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
            Ty::Prim(prim) => self.ck.fixed(prim),
            // A type parameter is no type that an operator takes.
            Ty::Param(_) => return self.invalid_operand(binop_symbol(op), ty, span),
            // Pointers compare as unsigned addresses.
            Ty::Ptr(_) if is_comparison(op) => self.ck.fixed(Prim::Uint),
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

    /// `operand as ty`, or `operand as! ty` if `unchecked`.
    ///
    /// `as` makes a value of one type a value of another that it is, or is
    /// near enough: a number of another, a struct of one that it starts as,
    /// a union or an enum of a wider one. `as!` makes an address one of any
    /// type, which it is only if what is there is, and an integer or a float
    /// the other, of its width, that has its bits.
    fn cast(
        &mut self,
        operand: &parse::Expr,
        ty: &parse::Type,
        unchecked: bool,
        span: Span,
    ) -> (Ty, Value) {
        let to = self.ck.resolve_ty(ty);
        let expected = match to {
            // An integer literal cast to a pointer is an address, and to a
            // function pointer an index in the table.
            Ty::Ptr(_) | Ty::Fn(_) => Some(Ty::Prim(Prim::Uint)),
            // An integer literal cast to the float with its bits is as wide
            // as the float.
            Ty::Prim(Prim::F32) if unchecked => Some(Ty::Prim(Prim::U32)),
            Ty::Prim(Prim::F64) if unchecked => Some(Ty::Prim(Prim::U64)),
            _ => None,
        };
        let (from, value) = self.expr(operand, expected);
        if from == Ty::Error || to == Ty::Error {
            return (Ty::Error, Value::default());
        }
        // A bounded type parameter casts as its bound does, which every
        // type argument casts to.
        let written = from;
        let from = match self.ck.known(from) {
            bound if !matches!(to, Ty::Param(_)) => bound,
            _ => from,
        };
        // Two enums are compared by the values of their members.
        if let (Ty::Enum(a), Ty::Enum(b)) = (from, to)
            && a != b
            && !(self.fold_enum(a, span) && self.fold_enum(b, span))
        {
            return (Ty::Error, Value::default());
        }
        let reinterprets = self.ck.reinterprets(from, to);
        if unchecked && reinterprets {
            return (to, value);
        }
        if let (true, Ty::Prim(have), Ty::Prim(want)) =
            (unchecked && self.ck.shares_bits(from, to), from, to)
        {
            let bits = |e| Expr::Unary(have.val_type(), IrUnOp::Reinterpret, Box::new(e));
            return (to, map1(value, want.val_type(), bits));
        }
        if !unchecked {
            // An enum casts as the type of its values does.
            let mut held = from;
            while let (Ty::Enum(id), false) = (held, matches!(to, Ty::Enum(_))) {
                held = self.ck.enum_ty(id);
            }
            if let Some(len) = self.ck.starting_scalars(held, to) {
                let len = len.min(value.scalars.len());
                return (to, self.project(value, 0..len));
            }
            if let Some(cast) = self.ck.cast_value(from, to, value) {
                return cast;
            }
        }
        let address = self.ck.casts_address(from, to);
        let is_address = matches!(to, Ty::Ptr(_) | Ty::Fn(_) | Ty::Array(_));
        let (from, to) = (self.ck.ty_name(written), self.ck.ty_name(to));
        let kind = match (unchecked, reinterprets, address) {
            (true, _, _) if !is_address => TypeErrorKind::UncheckedValue { from, to },
            (false, true, _) => TypeErrorKind::UncheckedCast { from, to },
            (_, _, true) => TypeErrorKind::AddressCast { from, to },
            _ => TypeErrorKind::InvalidCast { from, to },
        };
        self.error(kind, span);
        (Ty::Error, Value::default())
    }

    /// `&place` or `&var place`, the address of memory reached through a
    /// pointer or array, which must write its memory for `&var`. In a global
    /// initializer, what isn't in memory is a constant that is placed there.
    fn addr_of(
        &mut self,
        mutability: Mutability,
        inner: &parse::Expr,
        expected: Option<Ty>,
        span: Span,
    ) -> (Ty, Value) {
        let mutable = mutability == Mutability::Var;
        let want = match expected {
            Some(Ty::Ptr(id)) => Some(self.ck.pointee(id)),
            _ => None,
        };
        // An enum member, a union's variant and a module's function are
        // written like fields.
        let is_value = match &inner.kind {
            ExprKind::Field(of, _) => {
                self.enum_name(of).is_some()
                    || self.names_union(of)
                    || matches!(self.named(inner), Some(item) if !matches!(item, Item::Global(_)))
            }
            ExprKind::Deref(_) | ExprKind::Index(..) => false,
            _ => true,
        };
        if is_value {
            if self.global.is_none() {
                self.error(TypeErrorKind::NotAddressable, span);
                return (Ty::Error, Value::default());
            }
            let (ty, value) = self.expr(inner, want);
            return self.cell(mutable, ty, value, want, span);
        }
        let Some(place) = self.place(inner) else {
            return (Ty::Error, Value::default());
        };
        let Slots::Memory { addr, offset } = place.slots else {
            if self.global.is_none() {
                self.error(TypeErrorKind::NotAddressable, span);
                return (Ty::Error, Value::default());
            }
            let value = self.read_place(&place);
            return self.cell(mutable, place.ty, value, want, span);
        };
        if place.ty == Ty::Error {
            return (Ty::Error, Value::default());
        }
        if let Some(ty) = place.behind.filter(|_| mutable && !place.mutable) {
            let (ty, needs, element) = self.read_only(ty);
            self.error(TypeErrorKind::ReadOnlyAddr { ty, needs, element }, span);
        }
        let vt = self.ck.addr_type();
        let addr = match offset {
            0 => addr,
            _ => {
                let offset = Expr::Const(self.ck.addr_const(offset.into()));
                binary(vt, IrBinOp::Add, addr, offset)
            }
        };
        let value = Value {
            pre: place.pre,
            scalars: vec![(vt, addr)],
        };
        (self.ck.ptr_to(place.ty, mutable), value)
    }

    /// `&value` or `&var value` in a global initializer, where `value` is a
    /// `ty` that isn't in memory: it is placed there after any literals
    /// within it, and stored there when the initializer is run if it isn't
    /// constant. It's a `want` if it fits one, as a literal is of the type
    /// expected of it.
    fn cell(
        &mut self,
        mutable: bool,
        ty: Ty,
        value: Value,
        want: Option<Ty>,
        span: Span,
    ) -> (Ty, Value) {
        if self.default && mutable {
            self.error(TypeErrorKind::SharedPointee, span);
        }
        let errors = self.ck.errors.len();
        let consts = self.constant(value, span);
        if !self.placeable(ty, errors, span) {
            return (Ty::Error, Value::default());
        }
        let ty = want.filter(|want| self.ck.fits(ty, *want)).unwrap_or(ty);
        let (consts, stored) = match consts {
            Ok(consts) => (consts, None),
            Err(stored) => (Vec::new(), Some(stored)),
        };
        let offset = self.ck.repeat_data(ty, consts, 1);
        let addr = Expr::Const(self.ck.addr_const(offset));
        let mut value = scalar(self.ck.addr_type(), addr);
        if let Some(stored) = stored {
            value.pre = self.fill(ty, stored, offset, 1);
        }
        (self.ck.ptr_to(ty, mutable), value)
    }

    fn call(&mut self, callee: &parse::Expr, args: &[Arg], span: Span) -> (Ty, Value) {
        // `Err(None)` once the callee has been reported.
        let item = match &callee.kind {
            ExprKind::Module(name) => return self.module_call(name, args, span),
            ExprKind::Name(name) if self.lookup(name).is_some() => {
                return self.call_value(callee, args, span);
            }
            ExprKind::Name(name) if self.ck.takes_type_args(name) => {
                return self.generic_call(callee, args, span);
            }
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
            ExprKind::Field(inner, field) if self.names_union(inner) => {
                return match self.union_variant(inner, field, Some(args)) {
                    Some(variant) => variant,
                    // A field of the union as a `type`, which isn't called.
                    None => self.call_value(callee, args, span),
                };
            }
            // A type given type arguments, such as `array(u8)`.
            ExprKind::Call(inner, targs) if self.names_type(inner, targs) => {
                let ty = self.expr_type(callee);
                return self.construct(ty, args, span);
            }
            _ => return self.call_value(callee, args, span),
        };
        match item {
            Ok(Item::Func(id)) => {
                let mut sig = self.ck.funcs[id.0 as usize].clone();
                let binding = self.bind_args(&sig.params, &sig.defaults, args, false, span);
                let item = self.ck.func_items[id.0 as usize];
                if self.takes_defaults(item, &sig, &binding, span) {
                    sig = self.ck.funcs[id.0 as usize].clone();
                }
                let checked = args.iter().map(|_| None).collect();
                let value = self.bound_args(&sig.params, &sig.defaults, args, binding, checked);
                self.call_func(id, value)
            }
            Ok(Item::GenericFn(generic)) => self.generic_fn_call(generic, args, span),
            Ok(Item::Struct(id)) => self.construct(Ty::Struct(id), args, span),
            Ok(Item::Global(_)) => self.call_value(callee, args, span),
            Ok(Item::Enum(_) | Item::Module(_)) | Err(_) => {
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

    /// Whether a call spanning `span` that binds its arguments as `binding`
    /// takes a default of `sig`, the function that `item` of the program
    /// declares, that is folded only now, so that `sig` has it no longer.
    /// The defaults are folded when the first of them is used.
    fn takes_defaults(
        &mut self,
        item: usize,
        sig: &FuncSig,
        binding: &[Option<usize>],
        span: Span,
    ) -> bool {
        let mut taken = (0..)
            .zip(&sig.defaults)
            .filter(|(i, default)| default.is_some() && !binding.contains(&Some(*i)));
        let Some(first) = taken.next() else {
            return false;
        };
        let pending = |(_, default): &(usize, &Option<DefaultValue>)| {
            matches!(default, Some(DefaultValue::Pending))
        };
        let pending = pending(&first) || taken.any(|default| pending(&default));
        // A default that is folded names what its function may call.
        match pending {
            true => self.folded(item, &sig.name, span),
            false => {
                self.ck.note(Dep::Item(item));
                false
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
            let given = exprs(scalars.clone());
            for Ranged { leaf, prim, when } in self.ck.ranged(ret) {
                let held = narrow(leaf.ty, ValType::I32, given[leaf.index].clone());
                let in_range = widen(ValType::I32, leaf.ty, into_range(prim, held));
                let scalar = &mut scalars[leaf.index].1;
                // A leaf that variants share is brought into the range of
                // the one that is held.
                *scalar = match when.is_empty() {
                    true => in_range,
                    false => Expr::If {
                        ty: leaf.ty,
                        cond: Box::new(tags_are(&when, &given)),
                        then_expr: Box::new(in_range),
                        else_expr: Box::new(mem::replace(scalar, Expr::Const(Const::I32(0)))),
                    },
                };
            }
        }
        (ret, Value { pre, scalars })
    }

    /// A value of a struct or array type `ty`, built from its labelled
    /// fields.
    fn construct(&mut self, ty: Ty, args: &[Arg], span: Span) -> (Ty, Value) {
        let fields: Vec<_> = match ty {
            Ty::Struct(id) if self.ck.union_id(ty).is_none() => {
                return (ty, self.construct_struct(id, args, span));
            }
            Ty::Array(_) => ARRAY_FIELDS
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
        (ty, self.args(&fields, &[], args, true, span))
    }

    /// Checks call arguments against `params`. They are evaluated in source
    /// order, and their scalars are returned in parameter order. A parameter
    /// given no argument has its default, of `defaults`, which holds one for
    /// each parameter or is empty.
    fn args(
        &mut self,
        params: &[(String, Ty)],
        defaults: &[Option<DefaultValue>],
        args: &[Arg],
        require_labels: bool,
        span: Span,
    ) -> Value {
        let binding = self.bind_args(params, defaults, args, require_labels, span);
        let checked = args.iter().map(|_| None).collect();
        self.bound_args(params, defaults, args, binding, checked)
    }

    /// Checks call arguments against the parameters `binding` matches them
    /// with, as [`Self::args`] does. Those `checked` already, with their
    /// types, are only compared with their parameter's.
    fn bound_args(
        &mut self,
        params: &[(String, Ty)],
        defaults: &[Option<DefaultValue>],
        args: &[Arg],
        binding: Vec<Option<usize>>,
        checked: Vec<Option<(Ty, Value)>>,
    ) -> Value {
        // A parameter that no argument is bound to has the scalars of its
        // default, which are constant.
        let mut by_param = vec![Vec::new(); params.len()];
        for (i, default) in defaults.iter().enumerate() {
            let Some(default) = default else {
                continue;
            };
            if binding.contains(&Some(i)) {
                continue;
            }
            let types = self.ck.val_types(params[i].1);
            let consts = match default {
                DefaultValue::Folded(consts) => consts.clone(),
                // Reported, here or where it failed to fold.
                DefaultValue::Pending | DefaultValue::Failed => {
                    types.iter().map(|ty| zero(*ty)).collect()
                }
            };
            let consts = consts.into_iter().map(Expr::Const);
            by_param[i] = types.into_iter().zip(consts).collect();
        }
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
        let mut scalars = value.scalars.into_iter();
        for (i, count) in groups {
            by_param[i] = scalars.by_ref().take(count).collect();
        }
        value.scalars = by_param.into_iter().flatten().collect();
        value
    }

    /// Matches each argument to a parameter as [`Self::match_args`] does,
    /// reporting at `span` each parameter left without one that has no
    /// default in `defaults`.
    fn bind_args(
        &mut self,
        params: &[(String, Ty)],
        defaults: &[Option<DefaultValue>],
        args: &[Arg],
        require_labels: bool,
        span: Span,
    ) -> Vec<Option<usize>> {
        let binding = self.match_args(params, args, require_labels);
        for (i, (name, _)) in params.iter().enumerate() {
            let defaulted = matches!(defaults.get(i), Some(Some(_)));
            if !defaulted && !binding.contains(&Some(i)) {
                self.error(TypeErrorKind::MissingArg(name.clone()), span);
            }
        }
        binding
    }

    /// Matches each argument to a parameter, returning its index. Positional
    /// arguments fill parameters in order, then labels fill the rest.
    fn match_args(
        &mut self,
        params: &[(String, Ty)],
        args: &[Arg],
        require_labels: bool,
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
        binding
    }

    /// Reads a `ty` at `offset` bytes past the address in `ptr`. Of a union,
    /// only the variant it holds is read, and the leaves that the variant
    /// has nothing in are zero.
    fn load(&mut self, ptr: Value, offset: u32, ty: Ty) -> Value {
        let cells = self.ck.cells(ty);
        let (mut pre, addr) = if cells.len() > 1 {
            self.reusable_addr(ptr)
        } else {
            split1(ptr)
        };
        let types = self.ck.val_types(ty);
        let mut scalars: Vec<Expr> = Vec::new();
        for (leaf, slot) in types.iter().enumerate() {
            // A leaf that variants share is read from the cell of the one
            // that is held, which the first that isn't leaves to the next.
            let mut read = Expr::Const(zero(*slot));
            for cell in cells.iter().rev().filter(|cell| cell.leaf.index == leaf) {
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
                let load = widen(cell.ty, *slot, load);
                read = match cell.when.is_empty() {
                    true => load,
                    false => Expr::If {
                        ty: *slot,
                        cond: Box::new(tags_are(&cell.when, &scalars)),
                        then_expr: Box::new(load),
                        else_expr: Box::new(read),
                    },
                };
            }
            // A tag is read again for each cell of its variants.
            let is_tag = |cell: &Cell| cell.when.iter().any(|holds| holds.is_of(leaf));
            if cells.iter().any(is_tag) {
                let tmp = self.temp(*slot);
                pre.push(Stmt::SetLocal(tmp, read));
                read = Expr::Local(tmp);
            }
            scalars.push(read);
        }
        let scalars = types.into_iter().zip(scalars).collect();
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

    /// Makes each scalar of `value` as cheap to read again as to keep: one
    /// that isn't is moved into a temporary. In a global initializer, one
    /// that folds is its constant, so that a constant stays one.
    fn spill_simple(&mut self, value: &mut Value) {
        if self.global.is_none() {
            return self.spill(value, is_simple);
        }
        for (vt, scalar) in &mut value.scalars {
            match self.ck.fold(scalar) {
                Ok(c) => *scalar = Expr::Const(c),
                // Reported where the constant is folded.
                Err(Fold::Trap) => {}
                Err(Fold::NotConstant) if is_simple(scalar) => {}
                Err(Fold::NotConstant) => {
                    let tmp = self.push_local(TEMP.to_string(), *vt);
                    let expr = mem::replace(scalar, Expr::Local(tmp));
                    value.pre.push(Stmt::SetLocal(tmp, expr));
                }
            }
        }
    }

    /// The scalars of `value`, part of a global initializer, if they fold.
    /// Otherwise `value` itself, which is only known by running it. One
    /// that traps is reported at `span`, and has no scalars.
    fn constant(&mut self, value: Value, span: Span) -> Result<Vec<Const>, Value> {
        match self.ck.fold_value(&value) {
            Ok(consts) => Ok(consts),
            Err(Fold::NotConstant) => Err(value),
            Err(Fold::Trap) => {
                self.error(TypeErrorKind::ConstTrap, span);
                Ok(Vec::new())
            }
        }
    }

    /// The scalars of `value`, the whole of a constant in a global
    /// initializer, as [`Checker::evaluate`] finds them.
    fn evaluate(&mut self, value: Value, span: Span) -> Option<Vec<Const>> {
        let program = self.global?;
        self.ck.evaluate(program, self.locals.clone(), value, span)
    }

    /// The memory at `addr`, where a literal of type `ty` is placed, as a
    /// place to assign what isn't constant of it.
    fn placed(&self, ty: Ty, addr: u64) -> Place {
        Place {
            name: String::new(),
            ty,
            mutable: true,
            behind: None,
            pre: Vec::new(),
            slots: Slots::Memory {
                addr: Expr::Const(self.ck.addr_const(addr)),
                offset: 0,
            },
        }
    }

    /// Stores `value`, a `ty`, to each of the `count` elements placed at
    /// `addr`. It is evaluated once, whatever `count` is.
    fn fill(&mut self, ty: Ty, mut value: Value, addr: u64, count: u64) -> Vec<Stmt> {
        if count == 0 {
            self.spill(&mut value, is_pure);
            return value.pre;
        }
        let mut out = Vec::new();
        let place = self.placed(ty, addr);
        self.assign(&place, value, &mut out);
        let (size, _) = self.ck.layout(ty);
        if count == 1 || size == 0 {
            return out;
        }
        // The rest are copies of the first.
        let vt = self.ck.addr_type();
        let konst = |n: u64| Expr::Const(self.ck.addr_const(n));
        let (first, size, count) = (konst(addr), konst(size.into()), konst(count));
        let one = konst(1);
        let i = self.temp(vt);
        let at = binary(vt, IrBinOp::Mul, Expr::Local(i), size.clone());
        let next = binary(vt, IrBinOp::Add, Expr::Local(i), one.clone());
        out.push(Stmt::SetLocal(i, one));
        out.push(Stmt::Block(vec![Stmt::Loop(vec![
            Stmt::BrIf(1, binary(vt, IrBinOp::GeU, Expr::Local(i), count)),
            Stmt::MemoryCopy {
                dst: binary(vt, IrBinOp::Add, first.clone(), at),
                src: first,
                len: size,
            },
            Stmt::SetLocal(i, next),
            Stmt::Br(0),
        ])]));
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

/// Whether `expr` is a local or a constant, which is as cheap to read again
/// as to keep.
fn is_simple(expr: &Expr) -> bool {
    matches!(expr, Expr::Local(_) | Expr::Const(_))
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

/// Whether `expr` is a literal, or a `.name`, with or without arguments:
/// what only the type expected of it types.
fn is_typed_by_other(expr: &parse::Expr) -> bool {
    match &expr.kind {
        ExprKind::Dot(_) => true,
        ExprKind::Call(callee, _) => matches!(callee.kind, ExprKind::Dot(_)),
        _ => is_literal(expr),
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
        Const::Null => unreachable!("`externref` has no pointer type"),
    };
    let width = match store {
        StoreOp::Store8 => 1,
        StoreOp::Store16 => 2,
        StoreOp::Store => bytes.len(),
    };
    out[..width].copy_from_slice(&bytes[..width]);
}

fn zero(ty: ValType) -> Const {
    match ty {
        ValType::ExternRef => Const::Null,
        ValType::I32 => Const::I32(0),
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
        Expr::Const(_) | Expr::Local(_) | Expr::Global(_) | Expr::MemorySize => true,
        Expr::Unary(_, _, x) | Expr::Load { addr: x, .. } => is_pure(x),
        Expr::Binary(_, _, a, b) => is_pure(a) && is_pure(b),
        Expr::If {
            cond,
            then_expr,
            else_expr,
            ..
        } => is_pure(cond) && is_pure(then_expr) && is_pure(else_expr),
        Expr::Call(..) | Expr::CallIndirect { .. } | Expr::MemoryGrow(_) | Expr::Seq(..) => false,
    }
}

/// Whether `expr` is pure and its value can't be changed by side effects, so
/// it may be evaluated later than written. Calls can change globals and memory
/// but not the caller's locals, and a variable that an assignment changes is
/// read from temporaries, as [`Body::read_variable`] has it.
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
        Expr::Global(_)
        | Expr::Call(..)
        | Expr::CallIndirect { .. }
        | Expr::Load { .. }
        | Expr::MemorySize
        | Expr::MemoryGrow(_)
        | Expr::Seq(..) => false,
    }
}

/// The variables that the assignments within the expressions of `stmt`
/// change. An assignment that is the statement itself is not among them: its
/// target is written when nothing is left to read.
fn assigned_within(stmt: &parse::Stmt) -> Vec<String> {
    let mut names = Vec::new();
    match &stmt.kind {
        StmtKind::Expr(parse::Expr {
            kind: ExprKind::Assign { target, value, .. },
            ..
        }) => {
            push_assigned(target, &mut names);
            push_assigned(value, &mut names);
        }
        StmtKind::Binding(parse::Binding { value: expr, .. })
        | StmtKind::Expr(expr)
        | StmtKind::Return(Some(expr))
        | StmtKind::If { cond: expr, .. }
        | StmtKind::While { cond: expr, .. }
        | StmtKind::For { iter: expr, .. }
        | StmtKind::Match { value: expr, .. } => push_assigned(expr, &mut names),
        StmtKind::Return(None) | StmtKind::Break | StmtKind::Continue | StmtKind::Pass => {}
    }
    names
}

/// Pushes the name each assignment within `expr` changes a variable by, if
/// its target is one or a field of one.
fn push_assigned(expr: &parse::Expr, names: &mut Vec<String>) {
    match &expr.kind {
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Unit
        | ExprKind::Name(_)
        | ExprKind::Module(_)
        | ExprKind::FnType(_)
        | ExprKind::Placeholder
        | ExprKind::Dot(_) => {}
        ExprKind::Tuple(items) | ExprKind::List(items) => {
            for item in items {
                push_assigned(item, names);
            }
        }
        ExprKind::Unary(_, inner)
        | ExprKind::Field(inner, _)
        | ExprKind::Deref(inner)
        | ExprKind::AddrOf(_, inner)
        | ExprKind::Cast(inner, ..) => push_assigned(inner, names),
        ExprKind::Repeat(a, b)
        | ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::Pipe(a, b) => {
            push_assigned(a, names);
            push_assigned(b, names);
        }
        ExprKind::Call(callee, args) => {
            push_assigned(callee, names);
            for arg in args {
                push_assigned(&arg.value, names);
            }
        }
        ExprKind::Assign { target, value, .. } => {
            let mut root = &**target;
            while let ExprKind::Field(inner, _) = &root.kind {
                root = inner;
            }
            if let ExprKind::Name(name) = &root.kind {
                names.push(name.clone());
            }
            push_assigned(target, names);
            push_assigned(value, names);
        }
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
    [ARRAY, VARRAY, TUPLE, EXTERNREF, TYPE, OPTION, RESULT].contains(&name)
        || Prim::from_name(name).is_some()
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
            PatternKind::Variant(..) | PatternKind::Literal(_) | PatternKind::Array(_) => {
                unreachable!("only an arm of a `match` has one")
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
        ItemKind::Fn(f) if !f.sig.is_generic() => Some((item, f)),
        _ => None,
    })
}

/// Every generic function, in [`Item::GenericFn`] order, with the item that
/// declares it.
fn generic_fn_decls(program: &Program) -> impl Iterator<Item = (&parse::Item, &parse::FnDecl)> {
    program.items.iter().filter_map(|item| match &item.kind {
        ItemKind::Fn(f) if f.sig.is_generic() => Some((item, f)),
        _ => None,
    })
}

/// A default not yet folded for each parameter of `sig` that has one.
fn pending_defaults(sig: &FnSig) -> Vec<Option<DefaultValue>> {
    let defaults = sig.params.iter().map(|param| &param.default);
    defaults
        .map(|default| default.as_ref().map(|_| DefaultValue::Pending))
        .collect()
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
        StmtKind::Expr(expr) => is_unreachable_call(expr),
        StmtKind::If {
            then_body,
            else_body: Some(else_body),
            ..
        } => diverges(then_body) && diverges(else_body),
        StmtKind::While { cond, body } => {
            matches!(cond.kind, ExprKind::Bool(true)) && !breaks(body)
        }
        // One of its arms runs, or it traps.
        StmtKind::Match { arms, .. } => arms.iter().all(|arm| diverges(&arm.body)),
        _ => false,
    })
}

/// Whether `expr` is `module.unreachable()`, which traps.
fn is_unreachable_call(expr: &parse::Expr) -> bool {
    let ExprKind::Call(callee, _) = &expr.kind else {
        return false;
    };
    matches!(&callee.kind, ExprKind::Module(name) if name.name == "unreachable")
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
        StmtKind::Match { arms, .. } => arms.iter().any(|arm| breaks(&arm.body)),
        _ => false,
    })
}

fn fold_unary(op: IrUnOp, c: Const) -> Result<Const, Fold> {
    use Const::*;
    Ok(match (op, c) {
        (IrUnOp::Eqz, I32(x)) => I32((x == 0) as i32),
        (IrUnOp::Eqz, I64(x)) => I32((x == 0) as i32),
        (IrUnOp::Clz, I32(x)) => I32(x.leading_zeros() as i32),
        (IrUnOp::Clz, I64(x)) => I64(x.leading_zeros() as i64),
        (IrUnOp::Ctz, I32(x)) => I32(x.trailing_zeros() as i32),
        (IrUnOp::Ctz, I64(x)) => I64(x.trailing_zeros() as i64),
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
        (IrUnOp::Reinterpret, I32(x)) => F32(f32::from_bits(x as u32)),
        (IrUnOp::Reinterpret, I64(x)) => F64(f64::from_bits(x as u64)),
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
        Const::Null => unreachable!("only numbers convert"),
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
    use crate::file::{DummyManager, FileManager, MemoryLimits, StaticSection};
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
            Stmt::MemoryFill { dst, value, len } => {
                format!("(memory.fill {} {} {})", e(dst), e(value), e(len))
            }
            Stmt::MemoryCopy { dst, src, len } => {
                format!("(memory.copy {} {} {})", e(dst), e(src), e(len))
            }
            Stmt::Call { func, args, dests } => {
                let dests: Vec<_> = dests.iter().map(|d| local(f, *d)).collect();
                let name = func_name(m, *func);
                format!("(call {name} [{}] -> [{}])", list(args), dests.join(" "))
            }
            Stmt::CallIndirect {
                args, index, dests, ..
            } => {
                let dests: Vec<_> = dests.iter().map(|d| local(f, *d)).collect();
                let index = e(index);
                format!(
                    "(call_indirect {index} [{}] -> [{}])",
                    list(args),
                    dests.join(" ")
                )
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
            Expr::MemorySize => "memory.size".to_string(),
            Expr::MemoryGrow(pages) => format!("(memory.grow {})", ex(pages)),
            Expr::Binary(ty, op, a, b) => format!("({ty:?}.{op:?} {} {})", ex(a), ex(b)),
            Expr::Call(func, args) => {
                let args: Vec<_> = args.iter().map(ex).collect();
                format!("(call {} {})", func_name(m, *func), args.join(" "))
            }
            Expr::CallIndirect { args, index, .. } => {
                let args: Vec<_> = args.iter().map(ex).collect();
                format!("(call_indirect {} {})", ex(index), args.join(" "))
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
            Const::Null => "null".to_string(),
        }
    }

    /// The name of the function at each index of the table, from 1 up.
    fn table(module: &Module) -> Vec<&str> {
        let funcs = module.table.iter().flat_map(|table| &table.funcs);
        funcs.map(|id| func_name(module, *id)).collect()
    }

    /// The offset and bytes of each data segment.
    fn data(module: &Module) -> Vec<(u64, &[u8])> {
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
                 (call logs [0 12] -> [])"
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
                ("greeting.ptr", false, Const::I32(0)),
                ("greeting.len", false, Const::I32(12)),
                ("primes.ptr", false, Const::I32(12)),
                ("primes.len", false, Const::I32(4)),
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
    fn pipe_evaluates_its_value_once() {
        let src = "\
fn add(a: i32, b: i32) -> i32:
    return a + b
fn next() -> i32:
    return 1
fn f() -> i32:
    return next() |> add(_, _)
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set tmp0 (call next )) (return (call add tmp0 tmp0))"
        );
    }

    #[test]
    fn pipe_reads_locals_and_constants_in_place() {
        let src = "\
fn add(a: i32, b: i32) -> i32:
    return a + b
fn f(x: i32) -> i32:
    return x |> add(_, 1) |> add(_, _)
fn g(x: i32) -> i32:
    return 2 |> add(_, x |> add(_, _))
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(set tmp1 (call add x 1)) (return (call add tmp1 tmp1))"
        );
        assert_eq!(body(&module, "g"), "(return (call add 2 (call add x x)))");
    }

    #[test]
    fn pipe_value_is_evaluated_before_its_body() {
        let src = "\
var g = 0
fn tick() -> i32:
    g += 1
    return g
fn sub(a: i32, b: i32) -> i32:
    return a - b
fn f() -> i32:
    return g |> sub(tick(), _)
fn h() -> i32:
    return tick() |> sub(_, 1) |> sub(tick(), _)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(set tmp0 @g) (return (call sub (call tick ) tmp0))"
        );
        assert_eq!(
            body(&module, "h"),
            "(set tmp0 (call tick )) (set tmp1 (call sub tmp0 1)) \
             (return (call sub (call tick ) tmp1))"
        );
    }

    #[test]
    fn pipe_types_its_value_like_a_binding() {
        let src = "\
fn byte(x: u8) -> u8:
    return x
fn f(x: u8) -> u8:
    let a: u8 = x |> _ + 1
    return 1 as u8 |> byte(_) |> byte(_ + a)
";
        lower(src);
        let src = "\
fn byte(x: u8) -> u8:
    return x
fn f() -> u8:
    return 1 |> byte(_)
";
        assert_eq!(
            errors(src),
            vec![TypeErrorKind::Mismatch {
                expected: "u8".into(),
                found: "i32".into()
            }]
        );
    }

    #[test]
    fn constant_pipes_fold_in_globals() {
        let src = "\
pub let KIB = 4 |> _ * 1024
pub let PAIR = (KIB |> _ + _, 1.5 |> -_)
";
        let inits: Vec<_> = lower(src).globals.iter().map(|g| konst(g.init)).collect();
        assert_eq!(inits, vec!["4096", "8192", "-1.5f64"]);

        // What doesn't fold is evaluated once, however often it is read.
        let src = "\
var calls = 0
fn one() -> i32:
    calls += 1
    return calls
var v = 1
pub let a = one() |> _ + _
pub let b = v |> _ + 1
";
        let module = lower(src);
        let exported = module.globals.iter().filter(|g| g.export.is_some());
        let inits: Vec<_> = exported.map(|g| konst(g.init)).collect();
        assert_eq!(inits, vec!["2", "2"]);
    }

    #[test]
    fn pipes_carry_any_value() {
        let src = "\
struct P:
    x: i32
    y: i32
fn make() -> P:
    return P(x: 1, y: 2)
fn nothing() -> tuple():
    return ()
fn take(u: tuple(), n: i32) -> i32:
    return n
fn double(x: i32) -> i32:
    return x * 2
fn sum() -> i32:
    return make() |> _.x + _.y
fn unit() -> i32:
    return nothing() |> take(_, 1)
fn callee() -> i32:
    return double |> _(3)
fn field(p: &P) -> &i32:
    return p |> &_.y
";
        let module = lower(src);
        assert_eq!(
            body(&module, "sum"),
            "(call make [] -> [tmp0 tmp1]) (return (I32.Add tmp0 tmp1))"
        );
        assert_eq!(
            body(&module, "unit"),
            "(call nothing [] -> []) (return (call take 1))"
        );
        assert_eq!(body(&module, "callee"), "(return (call_indirect 1 3))");
        assert_eq!(body(&module, "field"), "(return (I32.Add p 4))");
    }

    #[test]
    fn placeholder_is_a_value_not_a_place_or_type() {
        let src = "\
struct(T) Box:
    value: T
fn f(x: i32):
    let p = x |> &_
    let b = i32 |> Box(_)(value: 1)
";
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::NotAddressable,
                TypeErrorKind::NotAValue("i32".into()),
                TypeErrorKind::NotAType
            ]
        );
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
    fn assignment_is_its_value() {
        let src = "\
var g: i32 = 0
fn next() -> i32:
    return 1
fn f(p: &var i32) -> i32:
    var a = 0
    var b = 0
    a = b = 1
    a = g = p.* = next()
    let c = (a += 2) * b
    while (a = next()) != 0:
        pass
    return c
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set a 0) (set b 0) \
             (set b 1) (set a 1) \
             (set tmp3 (call next )) (I32.Store offset=0 p tmp3) (set @g tmp3) (set a tmp3) \
             (set tmp4 a) (set tmp5 (I32.Add tmp4 2)) (set a tmp5) (set c (I32.Mul tmp5 b)) \
             (block (loop (set tmp7 (call next )) (set a tmp7) \
             (br_if 1 (I32.Eqz (I32.Ne tmp7 0))) (br 0))) \
             (return c)"
        );
    }

    #[test]
    fn assigned_variables_are_read_as_they_were() {
        let src = "\
struct P:
    x: i32
    y: i32
fn g(a: i32, b: i32) -> i32:
    return a
fn f(n: i32) -> i32:
    var x = n
    let a = x + (x = 5) + x
    let b = g(b: x = 6, a: x)
    x += x = n
    var p = P(x: 1, y: 2)
    let q = p = P(x: p.y, y: p.x)
    return x |> (x = 7) + _
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set x n) \
             (set tmp2 x) (set x 5) (set tmp3 x) (set a (I32.Add (I32.Add tmp2 5) tmp3)) \
             (set x 6) (set tmp5 x) (set b (call g tmp5 6)) \
             (set tmp7 x) (set x n) (set x (I32.Add tmp7 n)) \
             (set p.x 1) (set p.y 2) \
             (set tmp10 p.x) (set tmp11 p.y) (set tmp12 p.x) (set tmp13 p.y) \
             (set p.x tmp11) (set p.y tmp12) (set q.x tmp11) (set q.y tmp12) \
             (set tmp16 x) (set x 7) (return (I32.Add 7 tmp16))"
        );
    }

    #[test]
    fn assignment_checks_its_target_and_value() {
        let src = "\
fn f(n: i32) -> i64:
    var a = 0
    var b: i64 = 0
    let c = 0
    b = a = 1
    a = c = 2
    a = n = 3
    if a = 4:
        pass
    return b = 5
";
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::Mismatch {
                    expected: "i64".into(),
                    found: "i32".into()
                },
                TypeErrorKind::ImmutableAssign("c".into()),
                TypeErrorKind::ImmutableAssign("n".into()),
                TypeErrorKind::Mismatch {
                    expected: "bool".into(),
                    found: "i32".into()
                },
            ]
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
pub struct P:
    x: i32
    y: i32
pub let a: u8 = 200 + 100
pub let b = a as i64 * 2
pub let origin = P(y: 2, x: -1)
pub let flag = a > 3 and not false
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
        ];
        let expected: Vec<_> = expected
            .into_iter()
            .map(|(n, m, i)| (n.to_string(), m, i.to_string()))
            .collect();
        assert_eq!(globals, expected);
    }

    #[test]
    fn global_initializers_that_trap_are_errors() {
        let src = "\
fn f() -> i32:
    return 1
let c = f()
let d = 1 / 0
var m = 1
let n = m
";
        assert_eq!(errors(src), vec![TypeErrorKind::ConstTrap]);
    }

    #[test]
    fn constants_are_folded_when_first_used() {
        let src = "\
pub let a = b + Later.x as i32
pub let b = Late().y * 2
pub let (c, d) = (e, \"ab\")
pub let e = \"cde\"
pub var f = a
struct Late:
    x: i32 = 1
    y: i32 = LAST + x
enum(i32) Later:
    x = LAST * 10
let x = 4
let LAST = 3
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| format!("{} {}", g.name, konst(g.init)))
            .collect();
        // A global follows those its initializer is first to use, as its
        // literals do theirs.
        let expected = [
            "b 14", "a 44", "e.ptr 0", "e.len 3", "c.ptr 0", "c.len 3", "d.ptr 3", "d.len 2",
            "f 44",
        ];
        assert_eq!(globals, expected);
        assert_eq!(data(&module), [(0, &b"cde"[..]), (3, &b"ab"[..])]);
    }

    #[test]
    fn constants_are_not_used_in_their_own_definitions() {
        use TypeErrorKind::*;
        let src = "\
let own = own
let a: i32 = b + 1
let b = c
let c = a
let (p, q) = (1, p)
enum(i32) E:
    x = 1
    y = E.x as i32
    z = F.w as i32
enum(i32) F:
    w = E.x as i32
struct S:
    s: i32 = S().s
    t: i32 = S(s: 1, t: 2).t
struct A:
    a: i32 = B().b
struct B:
    b: i32 = A().a
fn f() -> i32:
    return a + b + c + E.z as i32 + S().t + A().a
";
        let recursive = |name: &str, text: &'static str| (RecursiveConstant(name.into()), text);
        assert_eq!(
            errors_at(src),
            [
                recursive("own", "own"),
                recursive("a", "a"),
                recursive("p", "p"),
                recursive("E", "x"),
                recursive("E", "x"),
                recursive("S", "S()"),
                recursive("A", "A()"),
            ]
        );
    }

    #[test]
    fn constants_nest_only_so_deep() {
        // Each but the last is first to use the next.
        let chain = |last: usize| {
            let uses = (0..last).map(|i| format!("let a{i} = a{} + 1\n", i + 1));
            uses.collect::<String>() + &format!("let a{last} = 0\npub let first = a0\n")
        };
        let module = lower(&chain(MAX_CONSTANT_DEPTH - 1));
        assert_eq!(module.globals[0].init, Const::I32(63));
        let name = format!("a{MAX_CONSTANT_DEPTH}");
        assert_eq!(
            errors(&chain(MAX_CONSTANT_DEPTH)),
            [TypeErrorKind::ConstantTooDeep(name)]
        );
        // Declared before those that use them, any number nest.
        let uses = (1..1000).map(|i| format!("let a{i} = a{} + 1\n", i - 1));
        let src = "let a0 = 0\n".to_string() + &uses.collect::<String>() + "pub let last = a999\n";
        assert_eq!(lower(&src).globals[0].init, Const::I32(999));
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
pub struct P:
    x: f32
    y: f32
pub let g: f32 = 1.0
pub let p = P(y: g, x: 2.0)
";
        let inits: Vec<_> = lower(src).globals.iter().map(|g| konst(g.init)).collect();
        assert_eq!(inits, vec!["1f32", "2f32", "1f32"]);
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
        assert!(module.globals.is_empty());
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
var hidden = 2
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
            ]
        );
    }

    #[test]
    fn lets_are_inlined() {
        let src = "\
struct P:
    x: i32
    y: f32
let limit = 10
let origin = P(x: 1, y: 2.0)
let name = \"duck\"
var count = limit
pub let top = limit + origin.x
fn f() -> uint:
    count += limit
    let p = origin
    let y = origin.y
    let t = top
    return name.len
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        assert_eq!(
            globals,
            [("count", Const::I32(10)), ("top", Const::I32(11))]
        );
        assert_eq!(data(&module), [(0, &b"duck"[..])]);
        assert_eq!(
            body(&module, "f"),
            "(set @count (I32.Add @count 10)) (set p.x 1) (set p.y 2f32) \
             (set y 2f32) (set t 11) (return 4)"
        );
        assert_eq!(
            errors("let a = (1, 2)\nfn f():\n    a = (3, 4)\n    a.0 = 5\n"),
            vec![
                TypeErrorKind::ImmutableAssign("a".into()),
                TypeErrorKind::ImmutableAssign("a".into()),
            ]
        );
    }

    #[test]
    fn pointers_are_i32_addresses() {
        let src = "\
pub struct P:
    x: f64
var null = 0 as! &u32
pub let top = 4294967295 as! &&P
pub fn f(p: &P, a: uint, n: int) -> &u32:
    let q = a as! &P
    let b = p as uint
    let s = p as int
    let c = p as! &u32
    let d = p == q
    let e = p != q
    let g = p < q
    let h = p >= q
    let r = n as! &P
    return c
";
        let module = lower(src);
        assert_eq!(
            module.memory,
            ir::Memory {
                min_pages: 0,
                max_pages: None,
                memory64: false,
                export: "memory".to_string()
            }
        );
        let globals: Vec<_> = module.globals.iter().map(|g| (g.ty, g.init)).collect();
        assert_eq!(
            globals,
            vec![
                (ValType::I32, Const::I32(0)),
                (ValType::I32, Const::I32(-1)),
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
fn f(p: &u8, q: &i8, a: i64, n: u32, g: fn()):
    let b = p as! &i8 == q
    let c = p == q
    let d = p < q
    let e = p + 1
    let h = a as &u8
    let i = p as u64
    let j = n as &u8
    let k = p as i32
    let l = g as u32
    let m = p as f32
";
        // Only `int` and `uint` are as wide as an address.
        let address = |from: &str, to: &str| TypeErrorKind::AddressCast {
            from: from.into(),
            to: to.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                mismatch("&u8", "&i8"),
                mismatch("&u8", "&i8"),
                invalid_operand("+", "&u8"),
                address("i64", "&u8"),
                address("&u8", "u64"),
                address("u32", "&u8"),
                address("&u8", "i32"),
                address("fn()", "u32"),
                TypeErrorKind::InvalidCast {
                    from: "&u8".into(),
                    to: "f32".into()
                },
            ]
        );
    }

    #[test]
    fn int_and_uint_are_as_wide_as_an_address() {
        let src = "\
enum(uint) Slot:
    first
    second
struct S:
    a: u8
    n: uint
    i: int
pub let BIG: uint = 4294967295
pub let LOW: int = -2147483648
fn f(n: uint, i: int, s: &S, a: array(u8)) -> uint:
    let narrow = n as u32
    let wide = narrow as uint
    let signed = n as int
    let long = i as i64
    let back = long as int
    let half = n / 2 + a.len
    let neg = -i >> 1
    let zeros = module.count_leading_zeros(n)
    let slot = Slot.second as uint
    match n:
        4294967295:
            pass
        else:
            pass
    return s.n + s.i as uint + S.size
";
        let module = lower(src);
        let globals: Vec<_> = module.globals.iter().map(|g| (g.ty, g.init)).collect();
        assert_eq!(
            globals,
            [
                (ValType::I32, Const::I32(-1)),
                (ValType::I32, Const::I32(i32::MIN))
            ]
        );
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        assert_eq!(f.params, [ValType::I32; 5]);
        assert_eq!(f.results, [ValType::I32]);
        assert_eq!(
            body(&module, "f"),
            "(set narrow n) (set wide narrow) (set signed n) (set long (I32.ExtendS i)) \
             (set back (I64.Wrap long)) (set half (I32.Add (I32.DivU n 2) a.len)) \
             (set neg (I32.ShrS (I32.Sub 0 i) 1)) (set zeros (I32.Clz n)) (set slot 1) \
             (set tmp14 n) (block (if (I32.Eq tmp14 -1) (then (br 1)) (else ))) \
             (return (I32.Add (I32.Add (I32.Load offset=4 s) (I32.Load offset=8 s)) 12))"
        );
        // Neither mixes with a type of a fixed size, or with the other.
        let src = "\
fn f(n: uint, i: int, w: u32):
    let a = n + w
    let b = n + i
    let c: uint = -1
    let d: uint = 4294967296
    let e: int = 2147483648
    let g: u32 = n
    let h: i32 = i
";
        assert_eq!(
            errors(src),
            vec![
                mismatch("uint", "u32"),
                mismatch("uint", "int"),
                invalid_operand("-", "uint"),
                TypeErrorKind::IntOutOfRange("uint".into()),
                TypeErrorKind::IntOutOfRange("int".into()),
                mismatch("u32", "uint"),
                mismatch("i32", "int"),
            ]
        );
    }

    /// Lowers `src` with addresses 64 bits wide.
    fn lower64(src: &str) -> Module {
        let settings = Settings {
            memory64: true,
            ..Settings::default()
        };
        match check_with(src, &settings) {
            Ok(module) => module,
            Err(errors) => panic!("unexpected type errors: {errors:#?}"),
        }
    }

    #[test]
    fn memory64_widens_addresses_and_what_counts_them() {
        let src = "\
pub struct S:
    a: u8
    p: &u8
    n: uint
pub let BIG: uint = 5000000000
pub let top = 18446744073709551615 as! &u8
pub fn f(n: uint, i: int, w: u32, p: &var S) -> uint:
    let narrow = n as u32
    let wide = w as uint
    let signed = n as int
    let short = i as i32
    let addr = p as uint
    p.n = addr + 8
    let q = p.p < (addr + 8) as! &u8
    let r = &var p.n
    let t = (fn()).size
    return S.size + (&u8).align + array(u8).size + t + module.count_leading_zeros(n)
";
        let module = lower64(src);
        assert!(module.memory.memory64);
        let globals: Vec<_> = module.globals.iter().map(|g| (g.ty, g.init)).collect();
        assert_eq!(
            globals,
            [
                (ValType::I64, Const::I64(5000000000)),
                (ValType::I64, Const::I64(-1))
            ]
        );
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        let wide = ValType::I64;
        assert_eq!(f.params, [wide, wide, ValType::I32, wide]);
        assert_eq!(f.results, [wide]);
        assert_eq!(
            body(&module, "f"),
            "(set narrow (I64.Wrap n)) (set wide (I32.ExtendU w)) (set signed n) \
             (set short (I64.Wrap i)) (set addr p) (I64.Store offset=16 p (I64.Add addr 8i64)) \
             (set q (I64.LtU (I64.Load offset=8 p) (I64.Add addr 8i64))) \
             (set r (I64.Add p 16i64)) (set t 8i64) \
             (return (I64.Add (I64.Add (I64.Add (I64.Add 24i64 8i64) 16i64) t) \
             (I64.Clz n)))"
        );
        // Neither constant is an address that 32 bits hold.
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::IntOutOfRange("uint".into()),
                TypeErrorKind::IntOutOfRange("uint".into()),
            ]
        );
    }

    #[test]
    fn memory64_indexes_arrays_with_wide_addresses() {
        let src = "\
let names: array(array(u8)) = [\"ab\"]
fn at(a: array(u64), i: uint) -> u64:
    return a[i]
fn sum(a: array(u16)) -> u16:
    var total: u16 = 0
    for x in a:
        total += x
    return total
fn first(a: array(u8)) -> u8:
    match a:
        [x, _]:
            return x
        else:
            return 0
fn same(a: array(u16), b: array(u16)) -> bool:
    return a == b
";
        let module = lower64(src);
        assert_eq!(
            body(&module, "at"),
            "(if (I64.GeU i a.len) (then unreachable) (else )) \
             (set tmp3 (I64.Add a.ptr (I64.Mul i 8i64))) (return (I64.Load offset=0 tmp3))"
        );
        assert_eq!(
            body(&module, "sum"),
            "(set total 0) (set tmp3 a.ptr) (set tmp4 a.len) (set tmp5 0i64) \
             (block (loop (br_if 1 (I64.GeU tmp5 tmp4)) \
             (set x (I32.Load16U offset=0 (I64.Add tmp3 (I64.Mul tmp5 2i64)))) \
             (set tmp5 (I64.Add tmp5 1i64)) (set total (I32.And (I32.Add total x) 65535)) \
             (br 0))) (return total)"
        );
        assert_eq!(
            body(&module, "first"),
            "(set tmp2 a.ptr) (set tmp3 a.len) \
             (block (if (if (I64.Eq tmp3 2i64) (seq (set x (I32.Load8U offset=0 tmp2)) 1) 0) \
             (then (return x)) (else )) (return 0)) unreachable"
        );
        assert_eq!(
            body(&module, "==(array(u16))"),
            "(if (I64.Ne a.len b.len) (then (return 0)) (else )) (set tmp4 0i64) \
             (block (loop (br_if 1 (I64.GeU tmp4 a.len)) \
             (if (I32.Ne (I32.Load16U offset=0 (I64.Add a.ptr (I64.Mul tmp4 2i64))) \
             (I32.Load16U offset=0 (I64.Add b.ptr (I64.Mul tmp4 2i64)))) \
             (then (return 0)) (else )) (set tmp4 (I64.Add tmp4 1i64)) (br 0))) (return 1)"
        );
        let at = module.funcs.iter().find(|f| f.name == "at").unwrap();
        assert_eq!(at.params, [ValType::I64; 3]);
        // An array in memory is a `ptr` and a `len` of 8 bytes each.
        let mut name = [0u8; 16];
        name[8] = 2;
        assert_eq!(data(&module), [(0, &b"ab"[..]), (8, &name[..])]);
    }

    #[test]
    fn memory64_widens_the_functions_and_constants_of_module() {
        let src = "\
pub let limits = (module.page_size, module.min, module.max)
fn all() -> varray(u8):
    return module.memory()
fn size() -> uint:
    return module.size()
fn grow(n: uint) -> int:
    return module.grow(n)
fn fill(p: &var u8, n: uint):
    module.fill(p, 7, n)
fn copy(a: varray(u8), b: array(u8)):
    module.copy(src: b.ptr, dst: a.ptr, len: a.len)
";
        let module = lower64(src);
        let globals: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        assert_eq!(globals, [Const::I64(65536), Const::I64(0), Const::I64(-1)]);
        assert_eq!(
            body(&module, "all"),
            "(return 0i64 (I64.Mul memory.size 65536i64))"
        );
        assert_eq!(body(&module, "size"), "(return memory.size)");
        assert_eq!(body(&module, "grow"), "(return (memory.grow n))");
        assert_eq!(body(&module, "fill"), "(memory.fill p 7 n)");
        assert_eq!(body(&module, "copy"), "(memory.copy a.ptr b.ptr a.len)");
        for name in ["size", "grow"] {
            let func = module.funcs.iter().find(|f| f.name == name).unwrap();
            assert_eq!(func.results, [ValType::I64], "{name}");
        }
    }

    #[test]
    fn memory64_places_literals_past_what_32_bits_address() {
        let far = 1 << 32;
        let settings = Settings {
            memory: MemoryLimits {
                min_pages: Some(1 << 17),
                max_pages: Some(1 << 30),
            },
            memory64: true,
            static_section: Some(StaticSection {
                start: far,
                end: far + 16,
            }),
            ..Settings::default()
        };
        let src = "\
pub let s = \"abc\"
pub let cell = &var 7
pub let all = module.static
pub let max = module.max
";
        let module = check_with(src, &settings).unwrap();
        assert_eq!(
            data(&module),
            [(far, &b"abc"[..]), (far + 4, &[7, 0, 0, 0][..])]
        );
        let globals: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        let far = far as i64;
        assert_eq!(globals, [far, 3, far + 4, far, 16, 1 << 30].map(Const::I64));
        assert_eq!(
            (module.memory.min_pages, module.memory.max_pages),
            (1 << 17, Some(1 << 30))
        );
        // More elements than 32 bits count, in the memory fitted to them.
        let module = lower64("pub let zeros: array(u8) = [0; 5000000000]\n");
        assert_eq!(module.memory.min_pages, 76294);
        assert_eq!(module.globals[1].init, Const::I64(5000000000));
        let unfit = "let a: array(u64) = [1; 18446744073709551615]\n";
        let settings = Settings {
            memory64: true,
            ..Settings::default()
        };
        let errors = check_with(unfit, &settings).unwrap_err();
        assert_eq!(
            errors.into_iter().map(|e| e.kind).collect::<Vec<_>>(),
            [TypeErrorKind::DataTooLarge {
                bytes: 8 * u128::from(u64::MAX),
                capacity: u64::MAX
            }]
        );
    }

    #[test]
    fn memory64_widens_function_pointers_and_the_table() {
        let src = "\
struct S:
    a: u8
    f: fn(i32) -> i32
fn inc(x: i32) -> i32:
    return x + 1
fn f(p: &var S, g: fn(i32) -> i32, i: uint) -> i32:
    p.f = g
    let h = i as! fn(i32) -> i32
    let n = inc as uint
    return p.f(1) + h(2) + S.size as i32
";
        let module = lower64(src);
        assert!(module.table.as_ref().unwrap().table64);
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        assert_eq!(f.params, [ValType::I64; 3]);
        assert_eq!(
            body(&module, "f"),
            "(I64.Store offset=8 p g) (set h i) (set n 1i64) \
             (return (I32.Add (I32.Add (call_indirect (I64.Load offset=8 p) 1) \
             (call_indirect h 2)) (I64.Wrap 16i64)))"
        );
        assert!(
            !lower("fn f():\n    pass\nlet g = f\n")
                .table
                .unwrap()
                .table64
        );
    }

    #[test]
    fn memory64_widens_the_leaves_unions_share_with_addresses() {
        let src = "\
union U:
    at: uint
    ratio: f32
    byte: &u8
let units: array(U) = [.at(5000000000), .ratio(1.0)]
fn f(u: U, p: &var U) -> uint:
    p.* = u
    match u:
        .at(n):
            return n
        else:
            return U.size
";
        let module = lower64(src);
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        assert_eq!(f.params, [ValType::I32, ValType::I64, ValType::I64]);
        assert_eq!(
            body(&module, "f"),
            "(I32.Store8 offset=0 p u) \
             (if (I32.Eq u 0) (then (I64.Store offset=8 p u.0)) (else )) \
             (if (I32.Eq u 1) \
             (then (F32.Store offset=8 p (I32.Reinterpret (I64.Wrap u.0)))) (else )) \
             (if (I32.Eq u 2) (then (I64.Store offset=8 p u.0)) (else )) \
             (set tmp3 u) (set n u.0) \
             (block (if (I32.Eq tmp3 0) (then (return n)) (else )) (return 16i64)) unreachable"
        );
        let mut bytes = [0u8; 32];
        bytes[8..16].copy_from_slice(&5000000000u64.to_le_bytes());
        bytes[16] = 1;
        bytes[24..28].copy_from_slice(&1f32.to_le_bytes());
        assert_eq!(data(&module), [(0, &bytes[..])]);
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
var q = 0 as! &var P
fn make() -> P:
    return P(x: 1, y: 2, z: 3)
fn tick() -> i32:
    return 1
fn f(p: &var P, pp: &&var P):
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
    fn address_of_a_constant_in_a_global_places_it() {
        let src = "\
pub enum(u8) Mode:
    idle
    busy = 7
pub struct P:
    a: u8 = 1
    b: i32 = -2
let N: i16 = 3
pub let n = &N
pub let m = &N
pub let zero = &var 0
pub let wide: &var u64 = &var 5
pub let p = &var P()
pub let b = &p.b
pub let mode = &var Mode.busy
pub let name = &\"hi\"
fn take(n: &i16, zero: &var i32, wide: &var u64, p: &var P, b: &i32):
    pass
fn more(mode: &var Mode, name: &array(u8)):
    pass
fn f() -> i32:
    take(n, zero, wide, p, b)
    more(mode, name)
    p.b += 1
    zero.* = 4
    return p.b
";
        let module = lower(src);
        // A zeroed value adds no data, and one behind a pointer isn't copied.
        assert_eq!(
            data(&module),
            [
                (0, &[3, 0][..]),
                (2, &[3, 0]),
                (8, &[5, 0, 0, 0, 0, 0, 0, 0]),
                (16, &[1, 0, 0, 0, 0xfe, 0xff, 0xff, 0xff]),
                (24, &[7]),
                (25, b"hi"),
                (28, &[25, 0, 0, 0, 2, 0, 0, 0]),
            ]
        );
        let inits: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        assert_eq!(
            inits,
            [
                ("n", Const::I32(0)),
                ("m", Const::I32(2)),
                ("zero", Const::I32(4)),
                ("wide", Const::I32(8)),
                ("p", Const::I32(16)),
                ("b", Const::I32(20)),
                ("mode", Const::I32(24)),
                ("name", Const::I32(28)),
            ]
        );
        assert_eq!(
            body(&module, "f"),
            "(call take [0 4 8 16 20] -> []) (call more [24 28] -> []) \
             (I32.Store offset=4 16 (I32.Add (I32.Load offset=4 16) 1)) \
             (I32.Store offset=0 4 4) (return (I32.Load offset=4 16))"
        );
    }

    #[test]
    fn address_of_a_constant_errors() {
        let src = "\
enum(u8) Mode:
    idle
struct S:
    r: &i32 = &1
    w: &var i32 = &var 1
fn make() -> i32:
    return 1
var v = 1
let a = &v
let b = &make()
let c: &var i32 = &1
fn f(x: i32):
    let d = &1
    let e = &Mode.idle
";
        use TypeErrorKind::*;
        assert_eq!(
            errors(src),
            vec![
                SharedPointee,
                mismatch("&var i32", "&i32"),
                NotAddressable,
                NotAddressable,
            ]
        );
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
fn generic(T: type):
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
pub let g: u8 = 1 << 9
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
var (_, hidden) = (1, pos.1.1)
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
            ]
        );
    }

    #[test]
    fn tuples_behind_pointers_use_c_layout() {
        let src = "\
fn f(p: &var tuple(u8, tuple(f64, i16)), q: &&var tuple(i32, i32)) -> &i16:
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
    fn parameters_of_type_type_are_type_parameters() {
        let src = "\
var heap: uint = 1024
fn malloc(T: type, count: uint = 1) -> &var T:
    heap += T.size * count
    return (heap - T.size * count) as! &var T
fn(T) boxed(val: T) -> &var T:
    let p = malloc(T)
    p.* = val
    return p
fn f() -> &u8:
    let p = malloc(count: 2, T: f64)
    let q: &tuple(u8, &i64) = malloc(tuple(u8, &i64))
    return boxed(1 as u8)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(set p (call malloc(f64) 2)) (set q (call malloc(tuple(u8, &i64)) 1)) \
             (return (call boxed(u8) (I32.And 1 255)))"
        );
        assert_eq!(
            body(&module, "boxed(u8)"),
            "(set p (call malloc(u8) 1)) (I32.Store8 offset=0 p val) (return p)"
        );
        assert_eq!(
            body(&module, "malloc(f64)"),
            "(set @heap (I32.Add @heap (I32.Mul 8 count))) \
             (return (I32.Sub @heap (I32.Mul 8 count)))"
        );
        let malloc = module.funcs.iter().find(|f| f.name == "malloc(f64)");
        assert_eq!(malloc.unwrap().params, [ValType::I32]);

        use TypeErrorKind::*;
        let src = "\
fn pick(T: type, U: type, x: T) -> T:
    return x
fn g(x: i32):
    pass
fn zero(T: type = u8) -> uint:
    return T.size
fn(T) lost() -> &T:
    return 0 as! &T
fn(T) twice(T: type, x: T):
    pass
fn f():
    pick(i32)
    pick(1, u8, 2)
    pick(i32, u8, true)
    g(i32)
    let t = i32
    let p: fn(i32) -> i32 = pick
";
        assert_eq!(
            errors(src),
            vec![
                TypeParamDefault("T".into()),
                NeverInferred {
                    func: "lost".into(),
                    param: "T".into()
                },
                DuplicateParam("T".into()),
                MissingArg("U".into()),
                MissingArg("x".into()),
                NotAType,
                mismatch("i32", "bool"),
                NotAValue("i32".into()),
                NotAValue("i32".into()),
                CannotInfer {
                    func: "pick".into(),
                    param: "U".into()
                },
            ]
        );
        assert_eq!(
            NeverInferred {
                func: "lost".into(),
                param: "T".into()
            }
            .to_string(),
            "no parameter of `lost` has `T` in its type, so no call infers it; \
             make it a parameter: `T: type`"
        );
    }

    #[test]
    fn type_arguments_no_argument_settles_are_reported() {
        let src = "\
fn(T, U) make(x: T, rest: array(U) = []) -> T:
    return x
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
struct(T) Box:
    value: T
fn(T) sized(x: T) -> uint:
    let y: T = x
    let b = Box(T)(value: y)
    return T.size + (&T).size
fn f():
    sized(1 as u16)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "sized(u16)"),
            "(set y x) (set b.value y) (return (I32.Add 2 4))"
        );
    }

    #[test]
    fn errors_in_a_generic_fn_are_reported_where_it_is_declared() {
        let src = "\
fn(T) add(a: T, b: T) -> T:
    return a + b
fn(T) twice(x: T) -> T:
    return add(x, x)
fn f():
    twice(1)
    twice(true)
";
        let errors = check_src(src).unwrap_err();
        assert_eq!(errors.len(), 1, "{errors:#?}");
        let operand = TypeErrorKind::InvalidOperand {
            op: "+",
            ty: "T".to_string(),
        };
        assert_eq!(errors[0].kind, operand);
        let span = errors[0].span.unwrap();
        assert_eq!(&src[span.start..span.end], "a + b");
        assert!(errors[0].instances.is_empty());
    }

    #[test]
    fn generic_fn_bodies_are_checked_as_declared() {
        use TypeErrorKind::*;
        let src = "\
struct(T) Box:
    v: T
fn(T) a(x: T) -> Box(T):
    return x
fn(T) b(x: &T) -> T:
    return -x
fn(T) c(x: Box(T)) -> T:
    return x.w
fn(T) d(x: T):
    x = x
fn(T) e(xs: array(T)):
    xs[0] = xs[1]
fn(T) g(x: T) -> u8:
    if x == x:
        return 1
fn(T) h(x: T) -> bool:
    return nope(x) and Box(T)(v: x) == Box(u8)(v: true)
";
        let name = |ty: &str| ty.to_string();
        assert_eq!(
            errors(src),
            vec![
                Mismatch {
                    expected: name("Box(T)"),
                    found: name("T")
                },
                InvalidOperand {
                    op: "-",
                    ty: name("&T")
                },
                NoField {
                    ty: name("Box(T)"),
                    field: name("w")
                },
                ImmutableAssign(name("x")),
                ReadOnlyWrite {
                    ty: name("array(T)"),
                    needs: name("varray(T)"),
                    element: true
                },
                InvalidOperand {
                    op: "==",
                    ty: name("T")
                },
                MissingReturn(name("g")),
                UnknownName(name("nope")),
                Mismatch {
                    expected: name("u8"),
                    found: name("bool")
                },
                Mismatch {
                    expected: name("Box(T)"),
                    found: name("Box(u8)")
                },
            ]
        );
    }

    #[test]
    fn type_parameters_are_types_of_which_only_the_layout_is_known() {
        use TypeErrorKind::*;
        // Each of these is right for some type arguments, and wrong as
        // declared.
        let src = "\
struct(T) Box:
    v: T
fn one(x: i32) -> i32:
    return x
fn(T) only_i32(x: T) -> i32:
    return one(x)
fn(T) only_unit(x: T) -> T:
    pass
fn(T) boxed(x: T) -> bool:
    return Box(T)(v: x) == Box(u8)(v: 1)
fn(T) duck(p: T, q: T) -> T:
    let n: T = 300
    let m = p + q
    let o = -p
    let e = p == q
    let c = p as i32
    let (a, b) = p
    let f = p.x
    let g = q.*
    let h = p(1)
    for c in T:
        pass
    let i = T.red
    return T(x: -1)
fn f():
    duck(1, 2)
";
        let name = |ty: &str| ty.to_string();
        assert_eq!(
            errors(src),
            vec![
                mismatch("i32", "T"),
                MissingReturn(name("only_unit")),
                mismatch("Box(T)", "Box(u8)"),
                mismatch("T", "i32"),
                invalid_operand("+", "T"),
                invalid_operand("-", "T"),
                invalid_operand("==", "T"),
                InvalidCast {
                    from: name("T"),
                    to: name("i32")
                },
                mismatch("tuple(_, _)", "T"),
                NoField {
                    ty: name("T"),
                    field: name("x")
                },
                invalid_operand(".*", "T"),
                NotCallable(name("p")),
                NotAValue(name("T")),
                NotAValue(name("T")),
                NotCallable(name("T")),
            ]
        );
        // What needs nothing but the layout is right for every type.
        let src = "\
struct(T) Box:
    v: T
fn(T) swap(a: &var T, b: &var Box(T)) -> uint:
    let held = a.*
    a.* = b.v
    b.v = held
    let p = a as! &u8
    let q = p as! &T
    match held:
        other:
            return T.size + T.align
fn f(a: &var i64, b: &var Box(i64)) -> uint:
    return swap(a, b)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "swap(i64)"),
            "(set held (I64.Load offset=0 a)) (I64.Store offset=0 a (I64.Load offset=0 b)) \
             (I64.Store offset=0 b held) (set p a) (set q p) (set other held) \
             (block (return (I32.Add 8 8))) unreachable"
        );
    }

    #[test]
    fn errors_in_a_generic_fns_declaration_are_reported_once() {
        let src = "\
fn(T) add(a: T, b: T) -> T:
    nope()
    return a
fn f():
    add(1, 2)
    add(true, false)
";
        let errors = check_src(src).unwrap_err();
        let kinds: Vec<_> = errors.iter().map(|e| e.kind.clone()).collect();
        assert_eq!(kinds, vec![TypeErrorKind::UnknownName("nope".to_string())]);
        assert!(errors[0].instances.is_empty());
    }

    #[test]
    fn type_parameters_give_the_size_of_any_type() {
        let src = "\
enum(u16) Unit:
    size
    align = 7
fn bytes(T: type) -> uint:
    return T.size + T.align
fn f() -> uint:
    let member = Unit.size
    return bytes(Unit)
";
        let module = lower(src);
        assert_eq!(body(&module, "bytes(Unit)"), "(return (I32.Add 2 2))");
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
            assert!(["deep(1)", "wide(1)"].contains(&&src[span.start..span.end]));
            let needs = error.instances.iter().map(|site| site.span);
            let needs: Vec<_> = needs.map(|span| &src[span.start..span.end]).collect();
            assert!(
                needs
                    .iter()
                    .all(|need| ["deep((x, 1))", "wide((x, x))"].contains(need))
            );
        }
        let deep = errors
            .iter()
            .find(|e| e.kind == TypeErrorKind::InstanceTooDeep("deep".to_string()))
            .unwrap();
        assert_eq!(deep.instances.len(), generic_fn::MAX_INSTANCE_DEPTH);
    }

    #[test]
    fn generic_fn_declarations_are_checked_without_calls() {
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
                UnknownName("nope".to_string()),
            ]
        );
    }

    #[test]
    fn type_arguments_are_storable() {
        let src = "\
extern:
    fn host() -> externref
struct R:
    r: externref
fn(T) f(x: T):
    pass
fn g(T: type) -> array(T):
    return g(T)
fn h(r: R):
    f(host())
    g(externref)
    f(r)
    f(1)
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
        let not_storable = |ty: &str| TypeErrorKind::NotStorable(ty.to_string());
        assert_eq!(
            found,
            vec![
                (not_storable("externref"), "f(host())"),
                (not_storable("externref"), "g(externref)"),
                (not_storable("R"), "f(r)"),
            ]
        );
    }

    #[test]
    fn bounded_type_parameters_take_structs_that_start_with_the_bound() {
        let src = "\
struct A:
    a: i32
struct B:
    a: i32
    b: i64
struct C:
    a: i32
    b: i64
    c: u8
struct(T: B) Held:
    item: &var T
fn(T: A) first(x: T) -> i32:
    return x.a
fn(T: B) bump(p: &var T) -> i64:
    p.b += 1
    p.a = first(p.*)
    let q = p as &B
    return q.b
fn(T: B) held(h: Held(T)) -> i64:
    return bump(h.item)
fn f(a: A, b: &var B, c: &var C) -> i64:
    let n = first(a) + first(b.*) + first(c.*)
    return bump(b) + bump(c) + held(Held(C)(item: c))
";
        let module = lower(src);
        let names: Vec<_> = module.funcs.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(
            names,
            [
                "f", "first(A)", "first(B)", "first(C)", "bump(B)", "bump(C)", "held(C)"
            ]
        );
        let first = module.funcs.iter().find(|f| f.name == "first(C)").unwrap();
        assert_eq!(first.params, [ValType::I32, ValType::I64, ValType::I32]);
        assert_eq!(body(&module, "first(C)"), "(return x.a)");
        assert_eq!(
            body(&module, "bump(C)"),
            "(I64.Store offset=8 p (I64.Add (I64.Load offset=8 p) 1i64)) \
             (I32.Store offset=0 p (call first(C) (I32.Load offset=0 p) \
             (I64.Load offset=8 p) (I32.Load8U offset=16 p))) \
             (set q p) (return (I64.Load offset=8 q))"
        );
        assert_eq!(body(&module, "held(C)"), "(return (call bump(C) h.item))");
    }

    #[test]
    fn bounds_name_the_type_parameters_before_them() {
        let src = "\
struct(T) Box:
    v: T
struct(T) Tagged:
    v: T
    tag: u8
struct Counted:
    v: f64
    count: i32
struct(B) Wrap:
    inner: &B
struct(T, B: Box(T)) Pair:
    first: &B
    second: T
fn(T, B: Box(T)) get(b: &B) -> T:
    return b.v
fn(T, B: Box(T)) put(b: &var B, value: T):
    b.v = value
fn(T, B: Box(T), W: Wrap(B)) deep(w: W) -> T:
    return get(w.inner)
fn(B: Box(T)) typed(T: type, b: &B) -> T:
    return b.v
fn f(t: &var Tagged(i64), c: &var Counted, b: &Box(u8)) -> f64:
    put(t, 5)
    put(c, 1.5)
    let p = Pair(f64, Counted)(first: c, second: 2.0)
    let g: fn(&Counted) -> f64 = get
    let n = get(t) + deep(Wrap(Tagged(i64))(inner: t))
    return get(c) + get(b) as f64 + typed(f64, c) + g(c)
";
        let module = lower(src);
        let names: Vec<_> = module.funcs.iter().map(|f| f.name.as_str()).collect();
        assert_eq!(
            names,
            [
                "f",
                "put(i64, Tagged(i64))",
                "put(f64, Counted)",
                "get(f64, Counted)",
                "get(i64, Tagged(i64))",
                "deep(i64, Tagged(i64), Wrap(Tagged(i64)))",
                "get(u8, Box(u8))",
                "typed(Counted, f64)"
            ]
        );
        assert_eq!(
            body(&module, "put(i64, Tagged(i64))"),
            "(I64.Store offset=0 b value)"
        );
        assert_eq!(
            body(&module, "get(f64, Counted)"),
            "(return (F64.Load offset=0 b))"
        );

        use TypeErrorKind::*;
        let src = "\
struct(T) Box:
    v: T
struct Counted:
    v: f64
    count: i32
struct Empty:
    pass
struct(T, B: Box(T)) Pair:
    first: &B
fn(T, B: Box(T)) put(b: &var B, value: T):
    b.v = value
fn(T, B: Box(T)) lost(b: &B, value: T) -> i32:
    return b.v
fn f(c: &var Counted, e: &Empty, p: Pair(i32, Counted)):
    put(c, true)
    put(e, 1)
    put(c)
";
        let not_met = |ty: &str, bound: &str| BoundNotMet {
            ty: ty.into(),
            bound: bound.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                not_met("Counted", "Box(i32)"),
                mismatch("i32", "T"),
                mismatch("f64", "bool"),
                not_met("Empty", "Box(i32)"),
                MissingArg("value".into()),
            ]
        );
    }

    #[test]
    fn unions_and_enums_are_bounded_by_those_that_start_as_they_do() {
        let src = "\
union IoError:
    closed
    timeout: u32
    denied
    big: tuple(i64, f32)
union ReadError:
    closed
    timeout: u32
pub enum(u8) Color:
    red
    green = 5
    blue
enum(u8) Warm:
    red
    green = 5
struct(C: Color) Paint:
    c: C
    under: &Paint(Warm)
pub let widened = Warm.green as Color
fn(E: IoError) code(e: E) -> i32:
    match e:
        .closed:
            return 1
        .timeout(ms):
            return ms as i32
        .denied:
            return 3
        .big((n, x)):
            return 4
fn(E: IoError) again(p: &E) -> bool:
    return p.* as IoError == .denied or code(p.*) == 1
fn(C: Color) shade(c: C) -> u8:
    match c:
        .red:
            return 1
        else:
            return c as Color as u8
fn f(r: ReadError, p: &ReadError, w: Warm) -> i32:
    let io = r as IoError
    let c = w as Color
    return code(r) + code(io) + shade(w) as i32 + shade(c) as i32
fn g(p: &ReadError) -> bool:
    return again(p)
";
        let module = lower(src);
        let globals: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        assert_eq!(globals, [Const::I32(5)]);
        assert_eq!(
            body(&module, "f"),
            "(set io r) (set io.0 (I32.ExtendU r.0)) (set io.1 0f32) (set c w) (return \
             (I32.Add (I32.Add (I32.Add (call code(ReadError) r r.0) (call \
             code(IoError) io io.0 io.1)) (call shade(Warm) w)) (call shade(Color) c)))"
        );
        assert_eq!(
            body(&module, "code(ReadError)"),
            "(set tmp2 e) (set n (I32.ExtendU e.0)) (set x 0f32) (block (if (I32.Eq \
             tmp2 0) (then (return 1)) (else )) (if (if (I32.Eq tmp2 1) (seq (set ms \
             (I64.Wrap n)) 1) 0) (then (return ms)) (else )) (if (I32.Eq tmp2 2) (then \
             (return 3)) (else )) (if (I32.Eq tmp2 3) (then (return 4)) (else )) \
             unreachable) unreachable"
        );
        assert_eq!(
            body(&module, "shade(Warm)"),
            "(set tmp1 c) (block (if (I32.Eq tmp1 0) (then (return 1)) (else )) (return \
             c)) unreachable"
        );
        assert_eq!(
            body(&module, "again(ReadError)"),
            "(set tmp1 (I32.Load8U offset=0 p)) (set tmp2 (I32.ExtendU (if (I32.Eq tmp1 \
             1) (I32.Load offset=4 p) 0))) (return (if (I32.Eq tmp1 2) 1 (seq (set tmp3 \
             (I32.Load8U offset=0 p)) (I32.Eq (call code(ReadError) tmp3 (if (I32.Eq \
             tmp3 1) (I32.Load offset=4 p) 0)) 1))))"
        );
    }

    #[test]
    fn union_and_enum_bound_errors() {
        use TypeErrorKind::*;
        let src = "\
union IoError:
    closed
    timeout: u32
    denied
union ReadError:
    closed
    timeout: u32
union Swapped:
    timeout: u32
    closed
union Retyped:
    closed
    timeout: i32
union Held:
    closed: tuple()
union More:
    closed
    timeout: u32
    denied
    other
struct Closed:
    closed: tuple()
enum(u8) Color:
    red
    green = 5
    blue
enum(u8) Warm:
    red
    green = 5
enum(u8) Cool:
    red
    green
enum(i8) Signed:
    red
struct(C: Color) Paint:
    c: C
    under: &Paint(Cool)
fn(E: IoError) code(e: E) -> E:
    match e:
        .closed:
            pass
    let a = E.closed
    let b: E = .closed
    let c = e == e
    return IoError.denied
fn(C: Color) shade(c: C) -> u8:
    return c as u8
fn(S: Closed) field(s: S):
    pass
fn f(io: IoError, r: ReadError, s: Swapped, t: Retyped, h: Held, m: More, k: Closed):
    code(s)
    code(t)
    code(h)
    code(m)
    code(k)
    field(h)
    shade(Cool.red)
    shade(Signed.red)
    shade(io)
    let a = io as ReadError
    let b = Color.red as Warm
    let c = Cool.red as Color
    let d = r as More
    let e = r as Swapped
";
        let not_within = |ty: &str, bound: &str, what| NotWithin {
            ty: ty.into(),
            bound: bound.into(),
            what,
        };
        let cast = |from: &str, to: &str| InvalidCast {
            from: from.into(),
            to: to.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                not_within("Cool", "Color", "members"),
                NonExhaustive(".timeout(_)".into()),
                NotAValue("E".into()),
                UntypedDot("closed".into()),
                invalid_operand("==", "E"),
                mismatch("E", "IoError"),
                not_within("Swapped", "IoError", "variants"),
                not_within("Retyped", "IoError", "variants"),
                not_within("Held", "IoError", "variants"),
                not_within("More", "IoError", "variants"),
                not_within("Closed", "IoError", "variants"),
                BoundNotMet {
                    ty: "Held".into(),
                    bound: "Closed".into()
                },
                not_within("Cool", "Color", "members"),
                not_within("Signed", "Color", "members"),
                not_within("IoError", "Color", "members"),
                cast("IoError", "ReadError"),
                cast("Color", "Warm"),
                cast("Cool", "Color"),
                cast("ReadError", "Swapped"),
            ]
        );
        assert_eq!(
            not_within("Cool", "Color", "members").to_string(),
            "`Cool` doesn't have only the first members of `Color`, in order"
        );
        assert_eq!(
            NotABound("i32".into()).to_string(),
            "`i32` can't bound a type parameter; only a struct, a union or an enum can"
        );
    }

    #[test]
    fn a_union_with_a_variant_that_failed_to_resolve_is_widened_to() {
        // The variant holds nothing, so the wider union lacks the leaf that
        // the narrower one has for it.
        let src = "\
union IoError:
    closed
    timeout: Nope
    denied
union ReadError:
    closed
    timeout: u32
fn(E: IoError) code(e: E) -> i32:
    match e:
        .timeout(ms):
            return 1
        else:
            return 2
fn f(r: ReadError) -> i32:
    let io = r as IoError
    return code(r) + code(io)
";
        assert_eq!(errors(src), vec![TypeErrorKind::UnknownType("Nope".into())]);
    }

    #[test]
    fn bound_errors() {
        use TypeErrorKind::*;
        let src = "\
struct A:
    a: i32
struct B:
    a: i32
    b: i64
struct Swapped:
    b: i64
    a: i32
struct Renamed:
    x: i32
struct Retyped:
    a: u32
struct Embeds:
    inner: A
union U:
    a: i32
struct(T) Box:
    v: T
struct(T: B) Held:
    item: &T
fn(T: A) first(x: T) -> i32:
    return x.a
fn(T: B) second(x: T) -> i64:
    return x.b
fn plain(x: A) -> i32:
    return x.a
fn(T: i32) a(x: T):
    pass
fn(T: U) b(x: T):
    pass
fn(V: Box(T), T) c(x: T, y: V):
    pass
fn(T: Box(T)) c2(x: T):
    pass
fn(T: A) d(x: T, y: &var T) -> i64:
    x.a = 1
    y.b = 1
    let z = T(a: 1)
    let w: A = x
    return second(x)
fn(T) e(x: T) -> i32:
    return first(x)
fn f(b: B, s: Swapped, r: Renamed, t: Retyped, u: U, h: Held(A), e: Embeds):
    first(e)
    first(s)
    first(r)
    first(t)
    first(u)
    first(1)
    plain(b)
    second(A(a: 1))
";
        let not_met = |ty: &str, bound: &str| BoundNotMet {
            ty: ty.into(),
            bound: bound.into(),
        };
        let names_later = BoundNamesLater {
            bound: "Box(T)".into(),
            param: "T".into(),
        };
        assert_eq!(
            errors(src),
            vec![
                not_met("A", "B"),
                NotABound("i32".into()),
                names_later.clone(),
                names_later.clone(),
                ImmutableAssign("x".into()),
                NoField {
                    ty: "T".into(),
                    field: "b".into()
                },
                NotCallable("T".into()),
                mismatch("A", "T"),
                not_met("T", "B"),
                not_met("T", "A"),
                not_met("Embeds", "A"),
                not_met("Swapped", "A"),
                not_met("Renamed", "A"),
                not_met("Retyped", "A"),
                not_met("U", "A"),
                not_met("i32", "A"),
                mismatch("A", "B"),
                not_met("A", "B"),
            ]
        );
        assert_eq!(
            not_met("Swapped", "A").to_string(),
            "`Swapped` doesn't start as `A` does"
        );

        assert_eq!(
            names_later.to_string(),
            "the bound `Box(T)` names `T`, which isn't declared before the type parameter it bounds"
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
                NotAValue("Box(i32)".into()),
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
    fn type_arguments_cannot_make_a_type_contain_itself() {
        use TypeErrorKind::*;
        let src = "\
union(T) Opt:
    some: T
    none
union(T) R:
    me: Opt(R(T))
    end
struct(T) W:
    x: T
struct(T) S:
    w: W(S(T))
fn f(r: &R(i32)) -> uint:
    return R(i32).size + S(u8).size + S(u8).align
fn(T) g(s: S(T)) -> uint:
    return 1
";
        assert_eq!(
            errors_at(src),
            vec![
                (RecursiveUnion("Opt(R(i32))".into()), "R(i32)"),
                (RecursiveStruct("W(S(T))".into()), "S(T)"),
                (RecursiveStruct("W(S(u8))".into()), "S(u8)"),
            ]
        );
    }

    #[test]
    fn structs_and_unions_nest_only_so_deep() {
        use TypeErrorKind::*;
        // Each struct holds the one before it twice over, so it holds one
        // more than twice as many as that one does: the sixth holds 63.
        let doubling = |levels: usize| -> String {
            let mut src = "struct(T) L1:\n    x: T\n".to_string();
            for level in 2..=levels {
                let below = level - 1;
                src += &format!("struct(T) L{level}:\n    x: L{below}(L{below}(T))\n");
            }
            src + &format!("fn f() -> uint:\n    return L{levels}(u8).size\n")
        };
        assert_eq!(body(&lower(&doubling(6)), "f"), "(return 1)");
        // The declaration nests too deep whatever it is given, so it is
        // reported and no use of it is.
        let too_deep = vec![(NestedTooDeep("L1".into()), "L6(L6(T))")];
        assert_eq!(errors_at(&doubling(7)), too_deep);
        assert_eq!(errors_at(&doubling(40)), too_deep);

        // A union written with as many type arguments as may nest, and one
        // more.
        let written = |depth: usize| -> String {
            let ty = format!("{}u8{}", "Opt(".repeat(depth), ")".repeat(depth));
            format!(
                "union(T) Opt:\n    some: T\n    none\nfn f(o: &{ty}) -> uint:\n    return {ty}.size\n"
            )
        };
        assert_eq!(body(&lower(&written(64)), "f"), "(return 65)");
        let src = written(65);
        let errors = errors_at(&src);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert_eq!(errors[0].0, NestedTooDeep("Opt".into()));
        assert!(errors[0].1.starts_with("Opt(Opt(") && errors[0].1.len() == 4 * 65 + 2 + 65);

        // Structs that are no instances, each holding the next.
        let chain = |len: usize| -> String {
            let structs = (1..len).map(|i| format!("struct S{i}:\n    x: S{}\n", i + 1));
            structs.collect::<String>() + &format!("struct S{len}:\n    x: u8\n")
        };
        assert_eq!(check_src(&chain(64)).err(), None);
        assert_eq!(
            errors_at(&chain(65)),
            vec![(NestedTooDeep("S1".into()), "x: S2")]
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
                NotAValue("tuple(i32, u8)".into()),
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
    fn types_have_a_size_and_an_alignment() {
        let src = "\
struct Point:
    x: f32
    y: f64
struct(T) Box:
    value: T
pub let WORD = i32.size
fn f() -> uint:
    let u = tuple().size + (&tuple()).size
    return Box(u8).size + array(u8).align + tuple(u8, i64).size + (&Point).size + Point.align
fn g(i32: u32) -> u32:
    return i32
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        assert_eq!(globals[..1], [("WORD", Const::I32(4))]);
        assert_eq!(
            body(&module, "f"),
            "(set u (I32.Add 0 4)) \
             (return (I32.Add (I32.Add (I32.Add (I32.Add 1 4) 16) 4) 8))"
        );
        assert_eq!(body(&module, "g"), "(return i32)");
    }

    #[test]
    fn types_are_not_values() {
        use TypeErrorKind::*;
        let src = "\
struct type:
    pass
struct(T) Box:
    value: T
fn g(t: &type) -> type:
    pass
fn f(T: type):
    let a = externref
    let b = Box(tuple(externref, i32)).size
    let c = Box
    let d = i32(1)
    i32 = 1
    let e = type(size: 1)
    let g = T.len
    let h = Box(T)
    let i: type = i32
";
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("type".into()),
                TypeOutsideParam,
                TypeOutsideParam,
                NotAValue("externref".into()),
                NotStorable("Box(tuple(externref, i32))".into()),
                MissingTypeArgs("Box".into()),
                NotCallable("i32".into()),
                NotAssignable,
                NotCallable("type".into()),
                NotAValue("T".into()),
                NotAValue("Box(T)".into()),
                TypeOutsideParam,
                NotAValue("i32".into()),
            ]
        );
        assert_eq!(
            TypeOutsideParam.to_string(),
            "`type` is only the type of a function's parameter, which it makes a type parameter"
        );
    }

    #[test]
    fn arrays_are_a_pointer_then_a_length() {
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
        assert_eq!(locals, ["a.ptr", "a.len"]);
        assert_eq!(body(&module, "f"), "(return a.ptr a.len)");
    }

    #[test]
    fn array_fields_are_places_laid_out_like_a_struct() {
        let src = "\
struct S:
    tag: u8
    name: array(u16)
fn f(a: array(u8), s: &var S) -> uint:
    var b = a
    b.len = 2
    s.name.ptr = b.ptr as! &u16
    return s.name.len
fn g(t: &tuple(u8, array(i32))) -> &i32:
    return t.1.ptr
";
        let module = lower(src);
        assert_eq!(body(&module, "g"), "(return (I32.Load offset=4 t))");
        assert_eq!(
            body(&module, "f"),
            "(set b.ptr a.ptr) (set b.len a.len) (set b.len 2) \
             (I32.Store offset=4 s b.ptr) (return (I32.Load offset=8 s))"
        );
    }

    #[test]
    fn arrays_are_constructed_from_a_pointer_and_length() {
        let src = "\
fn f(n: uint, p: &u8) -> array(u8):
    let b = array(u8)(len: n, ptr: p)
    let c = array(u8)(ptr: p, len: 3)
    return array(u8)(len: 0, ptr: 0)
";
        assert_eq!(
            body(&lower(src), "f"),
            "(set b.ptr p) (set b.len n) (set c.ptr p) (set c.len 3) (return 0 0)"
        );
        let src = "\
fn f(n: uint, p: &u8, q: &i8, a: array(u8)):
    let b = array(u8)(len: n, ptr: q)
    let c = array(u8)(len: -1, ptr: 4294967296)
    let d = (n, p) as array(u8)
    let e = a as tuple(uint, &u8)
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
                    ty: "uint".into()
                },
                TypeErrorKind::IntOutOfRange("&u8".into()),
                cast("tuple(uint, &u8)", "array(u8)"),
                cast("array(u8)", "tuple(uint, &u8)"),
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
    fn tick() -> uint
fn f(a: array(u16), i: uint) -> u16:
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
            vec![mismatch("uint", "i32"), invalid_operand("[]", "i32"),]
        );
    }

    #[test]
    fn elements_are_assignable_and_addressable() {
        let src = "\
struct P:
    x: i32
    y: f64
fn f(a: varray(P), i: uint) -> &P:
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
    fn var_pointers_and_varrays_fit_where_readers_are_expected() {
        let src = "\
struct Node:
    val: i32
    next: &var Node
struct View:
    bytes: array(u8)
let text: varray(u8) = \"duck\"
let zeros: varray(i32) = [0; 4]
let nested: varray(varray(u8)) = [\"a\", \"b\"]
let views: array(array(u8)) = [text]
var kept: &Node = 0
fn read(n: &Node) -> i32:
    return n.val
fn len(a: array(u8)) -> uint:
    return a.len
fn(T) first(a: array(T)) -> T:
    return a[0]
fn(T) at(p: &T) -> T:
    return p.*
fn(T) same(a: T, b: T):
    pass
fn f(p: &var Node, q: &Node, b: varray(u8)) -> &Node:
    let r: &Node = p
    var s: array(u8) = b
    s = b
    kept = p
    let v = View(bytes: b)
    let t: tuple(&Node, array(u8)) = (p, b)
    let n = read(p) + at(p).val + first(b) as i32
    same(q, p)
    let eq = p == q and q == p and p < q and b == s and s == b
    let w = q.next
    w.val = n
    q.next.val = 1
    let x = &var p.val
    x.* = 2
    let y: &i32 = &var p.val
    let c = q as! &var Node
    c.val = 3
    let d = s as! varray(u8)
    d[0] = 1
    let e = (&var Node).size + varray(u8).size
    let z: &var u8 = 16
    text[0] = 68
    zeros[1] += 1
    nested[0][0] = 1
    module.copy(dst: b.ptr, src: s.ptr, len: len(b))
    return p
";
        let module = lower(src);
        // A `varray` compares through the function of its `array`.
        let eq_funcs = module.funcs.iter().filter(|f| f.name.starts_with("=="));
        assert_eq!(
            eq_funcs.map(|f| f.name.as_str()).collect::<Vec<_>>(),
            ["==(array(u8))"]
        );
    }

    #[test]
    fn read_only_memory_is_not_written() {
        use TypeErrorKind::*;
        let src = "\
struct Node:
    val: i32
    next: &Node
let text = \"duck\"
fn g(p: &var Node):
    pass
fn h(a: varray(u8)):
    pass
fn r(p: &Node):
    pass
fn(T) k(p: &var T):
    pass
fn(T) same(a: T, b: T):
    pass
fn f(p: &Node, a: array(u8), v: &var Node, pp: &var &Node):
    p.val = 1
    p.* = Node(val: 1, next: 0)
    a[0] = 1
    text[0] += 1
    v.next.val = 1
    pp.*.val = 2
    let x = &var p.val
    let y = &var a[0]
    g(p)
    h(a)
    k(p)
    same(v, p)
    let t: tuple(&var Node, i32) = (p, 1)
    let m: &&Node = 0 as! &&var Node
    let fp: fn(&var Node) = r
    let w = a as varray(u16)
    let s: &var u8 = \"duck\"
";
        let write = |ty: &str, needs: &str, element| ReadOnlyWrite {
            ty: ty.into(),
            needs: needs.into(),
            element,
        };
        let addr = |ty: &str, needs: &str, element| ReadOnlyAddr {
            ty: ty.into(),
            needs: needs.into(),
            element,
        };
        assert_eq!(
            errors(src),
            vec![
                write("&Node", "&var Node", false),
                write("&Node", "&var Node", false),
                write("array(u8)", "varray(u8)", true),
                write("array(u8)", "varray(u8)", true),
                write("&Node", "&var Node", false),
                write("&Node", "&var Node", false),
                addr("&Node", "&var Node", false),
                addr("array(u8)", "varray(u8)", true),
                mismatch("&var Node", "&Node"),
                mismatch("varray(u8)", "array(u8)"),
                mismatch("&var Node", "&Node"),
                mismatch("&var Node", "&Node"),
                mismatch("tuple(&var Node, i32)", "tuple(&Node, i32)"),
                mismatch("&&Node", "&&var Node"),
                mismatch("fn(&var Node)", "fn(&Node)"),
                InvalidCast {
                    from: "array(u8)".into(),
                    to: "varray(u16)".into()
                },
                LiteralOutsideGlobal,
            ]
        );
        assert_eq!(
            write("&Node", "&var Node", false).to_string(),
            "can't write through `&Node`; it needs a `&var Node`"
        );
        assert_eq!(
            write("array(u8)", "varray(u8)", true).to_string(),
            "can't write to an element of `array(u8)`; it needs a `varray(u8)`"
        );
        assert_eq!(
            addr("&Node", "&var Node", false).to_string(),
            "can't take `&var` through `&Node`; it needs a `&var Node`"
        );
        assert_eq!(
            addr("array(u8)", "varray(u8)", true).to_string(),
            "can't take `&var` of an element of `array(u8)`; it needs a `varray(u8)`"
        );
        let src = "\
let s: &var u8 = \"duck\"
let a: varray(&var u8) = [0 as! &u8]
fn varray():
    pass
";
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("varray".into()),
                mismatch("&var u8", "array(u8)"),
                mismatch("&var u8", "&u8"),
            ]
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
            "(set tmp2 a.ptr) (set tmp3 a.len) (set tmp4 0) (block (loop \
             (br_if 1 (I32.GeU tmp4 tmp3)) \
             (set x (I32.Load16U offset=0 (I32.Add tmp2 (I32.Mul tmp4 2)))) \
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
                ("greeting.ptr", Some("greeting.ptr"), Const::I32(0)),
                ("greeting.len", Some("greeting.len"), Const::I32(2)),
                ("duck.ptr", None, Const::I32(2)),
                ("duck.len", None, Const::I32(4)),
            ]
        );
    }

    #[test]
    fn array_literals_are_aligned_data_placed_inner_first() {
        let src = "\
pub struct P:
    a: u8
    b: i32
pub let names = [\"foo\", \"bar\"]
let table: array(u16) = [1, 2, 65535]
pub let points = [P(a: 1, b: -2)]
pub let empty: array(f64) = []
pub let flags = [true, false]
pub let nested: array(array(i8)) = [[], [-1]]
";
        let module = lower(src);
        assert_eq!(
            data(&module),
            [
                (0, &b"foo"[..]),
                (3, b"bar"),
                (8, &[0, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0, 3, 0, 0, 0]),
                (24, &[1, 0, 2, 0, 0xff, 0xff]),
                (32, &[1, 0, 0, 0, 0xfe, 0xff, 0xff, 0xff]),
                (40, &[1, 0]),
                (42, &[0xff]),
                (44, &[42, 0, 0, 0, 0, 0, 0, 0, 42, 0, 0, 0, 1, 0, 0, 0]),
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
    fn repeated_array_literals_copy_one_element() {
        let src = "\
pub struct P:
    a: u8
    b: i32
let n: uint = 2
pub let bytes: array(u8) = [7; 3]
pub let points = [P(a: 1, b: -2); n + 1]
pub let zeros: array(u64) = [0; 1000]
pub let names = [\"ab\"; 2]
pub let none = [1.5; 0]
pub let last: array(u8) = [1; 1]
";
        let module = lower(src);
        let point = [1, 0, 0, 0, 0xfe, 0xff, 0xff, 0xff];
        // `"ab"` is at 8032, which is 0x1f60.
        let name = [0x60, 0x1f, 0, 0, 2, 0, 0, 0];
        assert_eq!(
            data(&module),
            [
                (0, &[7, 7, 7][..]),
                (4, &point.repeat(3)),
                // Nothing is written for `zeros`, which memory already is.
                (8032, b"ab"),
                (8036, &name.repeat(2)),
                (8052, &[1]),
            ]
        );
        let inits: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        for global in [
            ("points.len", Const::I32(3)),
            ("points.ptr", Const::I32(4)),
            ("zeros.len", Const::I32(1000)),
            ("zeros.ptr", Const::I32(32)),
            ("none.len", Const::I32(0)),
            ("none.ptr", Const::I32(8052)),
        ] {
            assert!(inits.contains(&global), "{global:?} in {inits:?}");
        }
    }

    #[test]
    fn repeated_array_literal_errors() {
        use TypeErrorKind::*;
        let src = "\
fn get() -> u8:
    return 1
var n: uint = 2
let i = 3
let a = [get(); 2]
let b = [0; n]
let c = [0; i]
let d = [0; 2.5]
let e = [0; -1]
let g: array(u8) = [256; 2]
let h: array(u8) = [true; 2]
let j = [0; 1 / 0]
fn f():
    let l = [1; 2]
";
        assert_eq!(
            errors(src),
            vec![
                mismatch("uint", "i32"),
                mismatch("uint", "f64"),
                invalid_operand("-", "uint"),
                IntOutOfRange("u8".into()),
                mismatch("u8", "bool"),
                ConstTrap,
                LiteralOutsideGlobal,
            ]
        );
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
                IntOutOfRange("u8".into()),
                ConstTrap,
                NotStorable("externref".into()),
                LiteralOutsideGlobal,
                LiteralOutsideGlobal,
            ]
        );
    }

    #[test]
    fn module_static_is_the_static_data_section() {
        let settings = Settings {
            static_section: Some(StaticSection {
                start: 1025,
                end: 2048,
            }),
            ..Settings::default()
        };
        let src = "\
pub let s = \"abc\"
pub let t: array(i32) = [1]
pub let all = module.static
fn f() -> uint:
    return module.static.len
";
        let module = check_with(src, &settings).unwrap();
        assert_eq!(
            data(&module),
            [(1025, &b"abc"[..]), (1028, &[1, 0, 0, 0][..])]
        );
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        assert_eq!(
            globals,
            [
                ("s.ptr", Const::I32(1025)),
                ("s.len", Const::I32(3)),
                ("t.ptr", Const::I32(1028)),
                ("t.len", Const::I32(1)),
                ("all.ptr", Const::I32(1025)),
                ("all.len", Const::I32(1023)),
            ]
        );
        assert_eq!(body(&module, "f"), "(return 1023)");
        // Nothing is exported but what the source makes `pub`.
        assert!(check_src("pub let data_end = 1\n").is_ok());
        assert_eq!(
            errors("let x = module.heap\n"),
            [TypeErrorKind::UnknownModuleProperty("heap".into())]
        );
    }

    #[test]
    fn module_constants_describe_memory() {
        let settings = |max_pages| Settings {
            memory: MemoryLimits {
                min_pages: Some(2),
                max_pages,
            },
            ..Settings::default()
        };
        let src = "\
pub let page = module.page_size
pub let min = module.min
pub let max = module.max
";
        let inits = |max_pages| -> Vec<_> {
            let module = check_with(src, &settings(max_pages)).unwrap();
            module.globals.iter().map(|g| g.init).collect()
        };
        assert_eq!(
            inits(Some(16)),
            [Const::I32(65536), Const::I32(2), Const::I32(16)]
        );
        // `u32::MAX` when memory may grow without limit.
        assert_eq!(
            inits(None),
            [Const::I32(65536), Const::I32(2), Const::I32(-1)]
        );
    }

    #[test]
    fn module_functions_are_inlined() {
        let src = "\
fn all() -> varray(u8):
    return module.memory()
fn size() -> uint:
    return module.size()
fn grow(n: uint) -> int:
    return module.grow(n)
fn fill(p: &var u8, n: uint):
    module.fill(p, 7, n)
fn copy(a: varray(u8), b: array(u8)):
    module.copy(src: b.ptr, dst: a.ptr, len: a.len)
";
        let module = lower(src);
        assert_eq!(module.funcs.len(), 5);
        assert_eq!(
            body(&module, "all"),
            "(return 0 (I32.Mul memory.size 65536))"
        );
        assert_eq!(body(&module, "size"), "(return memory.size)");
        assert_eq!(body(&module, "grow"), "(return (memory.grow n))");
        assert_eq!(body(&module, "fill"), "(memory.fill p 7 n)");
        assert_eq!(body(&module, "copy"), "(memory.copy a.ptr b.ptr a.len)");
    }

    #[test]
    fn module_unreachable_traps_and_diverges() {
        let src = "\
fn f(x: u32) -> u32:
    if x == 0:
        return 1
    module.unreachable()
fn g():
    module.unreachable()
    pass
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(if (I32.Eq x 0) (then (return 1)) (else )) unreachable"
        );
        assert_eq!(body(&module, "g"), "unreachable");
        // Only a statement of its own ends a function.
        assert_eq!(
            errors("fn h() -> u32:\n    let u = module.unreachable()\n"),
            [TypeErrorKind::MissingReturn("h".into())]
        );
        assert_eq!(
            errors("fn k():\n    module.unreachable(1)\n"),
            [TypeErrorKind::TooManyArgs {
                expected: 0,
                found: 1
            }]
        );
    }

    #[test]
    fn module_counts_zeros_of_any_integer() {
        let src = "\
pub let top = module.count_leading_zeros(1)
pub let wide: u64 = module.count_trailing_zeros(0 as u64)
pub let narrow = module.count_leading_zeros(-1 as i8)
pub let none = module.count_trailing_zeros(0 as u16)
fn a(x: u32) -> u32:
    return module.count_leading_zeros(x)
fn b(x: i64) -> i64:
    return module.count_trailing_zeros(value: x)
fn c(x: u8) -> u8:
    return module.count_leading_zeros(x)
fn d(x: i16) -> i16:
    return module.count_leading_zeros(x)
fn e(x: i8) -> i8:
    return module.count_trailing_zeros(x)
";
        let module = lower(src);
        assert_eq!(module.funcs.len(), 5);
        let inits: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        assert_eq!(
            inits,
            [
                Const::I32(31),
                Const::I64(64),
                Const::I32(0),
                Const::I32(16)
            ]
        );
        assert_eq!(body(&module, "a"), "(return (I32.Clz x))");
        assert_eq!(body(&module, "b"), "(return (I64.Ctz x))");
        // The bits an `i32` has above a narrow integer's aren't counted.
        assert_eq!(body(&module, "c"), "(return (I32.Sub (I32.Clz x) 24))");
        assert_eq!(
            body(&module, "d"),
            "(return (I32.Sub (I32.Clz (I32.And x 65535)) 16))"
        );
        assert_eq!(body(&module, "e"), "(return (I32.Ctz (I32.Or x 256)))");
    }

    #[test]
    fn module_counts_zeros_of_integers_only() {
        use TypeErrorKind::*;
        let src = "\
fn f(x: f32, p: &u8, n: u64):
    module.count_leading_zeros(x)
    module.count_trailing_zeros(p)
    module.count_leading_zeros(true)
    module.count_trailing_zeros()
    module.count_leading_zeros(1, 2)
    let a = module.count_trailing_zeros
    let b: u32 = module.count_leading_zeros(n)
";
        assert_eq!(
            errors(src),
            [
                invalid_operand("module.count_leading_zeros", "f32"),
                invalid_operand("module.count_trailing_zeros", "&u8"),
                invalid_operand("module.count_leading_zeros", "bool"),
                MissingArg("value".into()),
                TooManyArgs {
                    expected: 1,
                    found: 2
                },
                NotAValue("module.count_trailing_zeros".into()),
                Mismatch {
                    expected: "u32".into(),
                    found: "u64".into()
                },
            ]
        );
    }

    #[test]
    fn module_functions_and_constants_are_not_interchangeable() {
        use TypeErrorKind::*;
        let src = "\
fn f(p: &var u8):
    let a = module.size
    let b = module.page_size()
    let c = module.heap()
    module.fill(p, 0)
    module.grow(1, 2)
    let d: u32 = module.grow(1)
";
        assert_eq!(
            errors(src),
            [
                NotAValue("module.size".into()),
                NotCallable("module.page_size".into()),
                UnknownModuleProperty("heap".into()),
                MissingArg("len".into()),
                TooManyArgs {
                    expected: 1,
                    found: 2
                },
                Mismatch {
                    expected: "u32".into(),
                    found: "int".into()
                },
            ]
        );
    }

    #[test]
    fn data_must_fit_in_the_static_section() {
        use TypeErrorKind::{DataTooLarge, StaticOutsideMemory};
        let errors = |src: &str, start, end, min_pages| -> Vec<TypeError> {
            let settings = Settings {
                memory: MemoryLimits {
                    min_pages: Some(min_pages),
                    max_pages: None,
                },
                static_section: Some(StaticSection { start, end }),
                ..Settings::default()
            };
            check_with(src, &settings).err().unwrap_or_default()
        };
        let spanless = |kind| TypeError {
            kind,
            span: None,
            instances: Vec::new(),
        };
        assert_eq!(errors("let s = \"\"\n", 0, 0, 0), []);
        assert_eq!(errors("let s = \"ab\"\n", 4, 6, 1), []);
        assert_eq!(
            errors("let s = \"abc\"\n", 4, 6, 1),
            [spanless(DataTooLarge {
                bytes: 3,
                capacity: 2
            })]
        );
        // Padding to align the `u32`s counts.
        assert_eq!(
            errors("let s = \"a\"\nlet t: array(u32) = [1]\n", 0, 6, 1),
            [spanless(DataTooLarge {
                bytes: 8,
                capacity: 6
            })]
        );
        // Nothing so large is built to find that it doesn't fit, zeroed or
        // not.
        assert_eq!(
            errors(
                "let a: array(u64) = [0; 4294967295]\nlet b: array(u64) = [1; 4294967295]\n",
                8,
                16,
                1
            ),
            [spanless(DataTooLarge {
                bytes: 68719476720,
                capacity: 8
            })]
        );
        assert_eq!(
            errors("let s = \"\"\n", 0, 65537, 1),
            [spanless(StaticOutsideMemory {
                end: 65537,
                min_pages: 1
            })]
        );
    }

    #[test]
    fn an_unset_static_section_fits_the_literals() {
        let spanless = |kind| TypeError {
            kind,
            span: None,
            instances: Vec::new(),
        };
        let limits = |min_pages, max_pages| Settings {
            memory: MemoryLimits {
                min_pages,
                max_pages,
            },
            ..Settings::default()
        };
        let globals = |module: &Module| -> Vec<_> {
            let globals = module.globals.iter();
            globals.map(|g| (g.name.clone(), g.init)).collect()
        };

        // Without literals it is empty, and memory starts with nothing.
        let module = lower("fn f() -> array(u8):\n    return module.static\n");
        assert_eq!(module.memory.min_pages, 0);
        assert_eq!(body(&module, "f"), "(return 0 0)");

        // It starts at address 0 and ends where the literals do, however
        // early it is read.
        let src = "\
pub let all = module.static
pub let pages = module.min
pub let s = \"abc\"
pub let t: array(i32) = [1]
fn f() -> uint:
    return module.static.len + module.min
";
        let module = lower(src);
        assert_eq!(data(&module), [(0, &b"abc"[..]), (4, &[1, 0, 0, 0][..])]);
        assert_eq!(module.memory.min_pages, 1);
        assert_eq!(
            globals(&module)[..3],
            [
                ("all.ptr".to_string(), Const::I32(0)),
                ("all.len".to_string(), Const::I32(8)),
                ("pages".to_string(), Const::I32(1)),
            ]
        );
        assert_eq!(body(&module, "f"), "(return (I32.Add 8 1))");

        // Memory starts with the pages that hold it, unless told otherwise.
        let src = "pub let a: array(u8) = [0; 65537]\npub let pages = module.min\n";
        let module = lower(src);
        assert_eq!(module.memory.min_pages, 2);
        assert_eq!(globals(&module)[2].1, Const::I32(2));
        let module = check_with(src, &limits(Some(3), None)).unwrap();
        assert_eq!(module.memory.min_pages, 3);
        assert_eq!(globals(&module)[2].1, Const::I32(3));
        assert_eq!(
            check_with(src, &limits(Some(1), None)).unwrap_err(),
            [spanless(TypeErrorKind::StaticOutsideMemory {
                end: 65537,
                min_pages: 1
            })]
        );
        assert_eq!(
            check_with(src, &limits(None, Some(1))).unwrap_err(),
            [spanless(TypeErrorKind::StaticOutsideMax {
                end: 65537,
                max_pages: 1
            })]
        );
        assert!(check_with(src, &limits(None, Some(2))).is_ok());

        // A section that is set is not fitted, but still sets where memory
        // starts.
        let settings = Settings {
            static_section: Some(StaticSection {
                start: 4,
                end: 65537,
            }),
            ..Settings::default()
        };
        let module = check_with("pub let s = \"abc\"\n", &settings).unwrap();
        assert_eq!(data(&module), [(4, &b"abc"[..])]);
        assert_eq!(module.memory.min_pages, 2);

        // A literal may be sized by the section only if that leaves the
        // section as large as it was.
        let module = lower("pub let a: array(u8) = [1; module.static.len]\n");
        assert_eq!(globals(&module)[0].1, Const::I32(0));
        assert_eq!(
            check_src("let a: array(u8) = [1; module.static.len + 1]\n").unwrap_err(),
            [spanless(TypeErrorKind::SelfSizedStatic)]
        );
        assert_eq!(
            check_src("let a: array(u8) = [1; module.min + 1]\n").unwrap_err(),
            [spanless(TypeErrorKind::SelfSizedStatic)]
        );
        // What the first guess at its size got wrong is not reported.
        let src = "let s = \"abc\"\nlet a: array(u8) = [1; 6 / module.static.len]\n";
        assert_eq!(
            check_src(src).unwrap_err(),
            [spanless(TypeErrorKind::SelfSizedStatic)]
        );

        // Literals still have to fit in memory.
        assert_eq!(
            check_src("let a: array(u64) = [1; 4294967295]\n").unwrap_err(),
            [spanless(TypeErrorKind::DataTooLarge {
                bytes: 34359738360,
                capacity: u32::MAX.into()
            })]
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
                RecursiveConstant("Bad".into()),
                mismatch("i32", "bool"),
            ]
        );
    }

    #[test]
    fn unions_are_a_tag_and_the_leaves_their_variants_share() {
        let src = "\
union Shape:
    circle: f32
    rect: tuple(f32, i64)
    empty
fn f(s: Shape) -> Shape:
    let a = Shape.circle(1.5)
    let b = Shape.rect((2.0, 3))
    let c = Shape.empty
    return s
";
        let module = lower(src);
        let f = &module.funcs[0];
        let wasm = [ValType::I32, ValType::F32, ValType::I64];
        assert_eq!(f.params, wasm);
        assert_eq!(f.results, wasm);
        let names: Vec<_> = f.locals[..3].iter().map(|l| l.name.as_str()).collect();
        assert_eq!(names, ["s", "s.0", "s.1"]);
        assert_eq!(
            body(&module, "f"),
            "(set a 0) (set a.0 1.5f32) (set a.1 0i64) \
             (set b 1) (set b.0 2f32) (set b.1 3i64) \
             (set c 2) (set c.0 0f32) (set c.1 0i64) \
             (return s s.0 s.1)"
        );
    }

    #[test]
    fn leaves_that_variants_share_are_as_wide_as_what_each_holds() {
        use ValType::*;
        let src = "\
union Mixed:
    int: i32
    float: f32
    pair: tuple(u8, f64)
    long: i64
union Refs:
    one: tuple(externref, f32)
    two: tuple(i32, externref, externref)
    none
extern:
    fn get() -> externref
    fn number() -> f32
fn order() -> Refs:
    return .one((get(), number()))
fn shapes(a: result(i32, f32), b: result(array(u8), f64), c: result(f32, f32), d: Refs):
    pass
fn build(x: i32, y: f32, z: f64, b: u8) -> Mixed:
    if x == 0:
        return .int(x)
    if x == 1:
        return .float(y)
    if x == 2:
        return .float(1.5)
    return .pair((b, z))
fn read(m: Mixed) -> f64:
    match m:
        .int(x):
            return x as f64
        .float(y):
            return y as f64
        .pair((b, z)):
            return z
        .long(_):
            return 0.0
";
        let module = lower(src);
        // An `i32` and an `f32` share an `i32`, any others that differ an
        // `i64`, and `externref`s only leaves of their own, after the rest.
        let shapes = module.funcs.iter().find(|f| f.name == "shapes").unwrap();
        let (a, b, c) = ([I32, I32], [I32, I64, I32], [I32, F32]);
        let d = [I32, I32, ExternRef, ExternRef];
        assert_eq!(shapes.params, [&a[..], &b[..], &c[..], &d[..]].concat());
        // What a variant holds is evaluated in the order it's written,
        // whichever leaves hold it.
        assert_eq!(
            body(&module, "order"),
            "(set tmp0 (call get )) (set tmp1 (call number )) \
             (return 0 (F32.Reinterpret tmp1) tmp0 null)"
        );
        let build = module.funcs.iter().find(|f| f.name == "build").unwrap();
        assert_eq!(build.results, [I32, I64, F64]);
        // A leaf holds the bits of a scalar narrower than it, and zeroes
        // above them.
        assert_eq!(
            body(&module, "build"),
            "(if (I32.Eq x 0) (then (return 0 (I32.ExtendU x) 0f64)) (else )) \
             (if (I32.Eq x 1) \
             (then (return 1 (I32.ExtendU (F32.Reinterpret y)) 0f64)) (else )) \
             (if (I32.Eq x 2) (then (return 1 1069547520i64 0f64)) (else )) \
             (return 2 (I32.ExtendU b) z)"
        );
        // An arm reads what its variant holds out of a leaf wider than it,
        // once the value is known to hold the variant.
        assert_eq!(
            body(&module, "read"),
            "(set tmp3 m) (set tmp4 m.0) (set z m.1) \
             (block \
             (if (if (I32.Eq tmp3 0) (seq (set x (I64.Wrap tmp4)) 1) 0) \
             (then (return (I32.ConvertS(F64) x))) (else )) \
             (if (if (I32.Eq tmp3 1) (seq (set y (I32.Reinterpret (I64.Wrap tmp4))) 1) 0) \
             (then (return (F32.Promote y))) (else )) \
             (if (if (I32.Eq tmp3 2) (seq (set b (I64.Wrap tmp4)) 1) 0) \
             (then (return z)) (else )) \
             (if (I32.Eq tmp3 3) (then (return 0f64)) (else )) \
             unreachable) \
             unreachable"
        );
    }

    #[test]
    fn dot_names_are_of_the_type_expected_of_them() {
        let src = "\
enum(u8) Color:
    red
    green
union Shape:
    circle: f32
    tinted: Color
    empty
struct Pen:
    color: Color
    shape: Shape = .empty
let ink: Color = .green
fn paint(c: Color, s: Shape) -> Shape:
    return s
fn f(c: Color) -> Shape:
    let a: Shape = .circle(1.5)
    var p = Pen(color: .green)
    p.color = .red
    if c == .green or .red == c:
        return paint(.red, .tinted(.green))
    let (x, y): tuple(Color, Shape) = (.red, .empty)
    return .empty
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(set a 0) (set a.0 1069547520) \
             (set p.color 1) (set p.shape 2) (set p.shape.0 0) \
             (set p.color 0) \
             (if (if (I32.Eq c 1) 1 (I32.Eq 0 c)) \
             (then (call paint [0 1 1] -> [tmp6 tmp7]) (return tmp6 tmp7)) (else )) \
             (set x 0) (set y 2) (set y.0 0) \
             (return 2 0)"
        );
    }

    #[test]
    fn dot_names_need_a_union_or_enum_to_be_of() {
        use TypeErrorKind::*;
        let src = "\
enum(u8) Color:
    red
union Shape:
    circle: f32
    empty
fn(T) g(x: T) -> T:
    return .red
fn f(c: Color, s: Shape, n: i32) -> Color:
    let a = .red
    let b: i32 = .red
    let d: Color = .blue
    let e: Color = .size
    let h: Color = .red(1)
    let i: Shape = .square
    let j: Shape = .empty()
    let k: Shape = .circle
    let l: Shape = .circle(1.0, 2.0)
    let m: Shape = .circle(r: 1.0)
    let o: Shape = .circle(true)
    .red
    return g(.red)
";
        let untyped = || UntypedDot("red".into());
        let needs_value = || VariantNeedsValue {
            variant: "circle".into(),
            ty: "f32".into(),
        };
        assert_eq!(
            errors(src),
            vec![
                untyped(),
                untyped(),
                untyped(),
                NoMember {
                    ty: "Color".into(),
                    member: "blue".into()
                },
                NoMember {
                    ty: "Color".into(),
                    member: "size".into()
                },
                NotCallable(".red".into()),
                NoVariant {
                    ty: "Shape".into(),
                    variant: "square".into()
                },
                VariantTakesNothing("empty".into()),
                needs_value(),
                needs_value(),
                needs_value(),
                mismatch("f32", "bool"),
                untyped(),
                untyped(),
            ]
        );
    }

    #[test]
    fn union_variants_are_built_by_name_and_read_by_nothing() {
        use TypeErrorKind::*;
        let src = "\
union Shape:
    circle: f32
    size
    unit: tuple()
union Shape:
    a
union Dup:
    a
    a: i32
struct Wrap:
    inner: Loop
union Loop:
    next: Wrap
union(T) Opt:
    some: T
    none
fn f(s: Shape) -> uint:
    let a = Shape(circle: 1.0)
    let b = s.circle
    let c = Shape.square
    let d = Shape.circle
    let e = Shape.size(1)
    let g = Opt.none
    let h = Opt(i32).some(true)
    let i = Shape.unit(())
    let j = Shape.unit
    return Shape.align + Opt(i64).size
";
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("Shape".into()),
                DuplicateVariant("a".into()),
                RecursiveUnion("Loop".into()),
                NotCallable("Shape".into()),
                NoField {
                    ty: "Shape".into(),
                    field: "circle".into()
                },
                NoVariant {
                    ty: "Shape".into(),
                    variant: "square".into()
                },
                VariantNeedsValue {
                    variant: "circle".into(),
                    ty: "f32".into()
                },
                VariantTakesNothing("size".into()),
                MissingTypeArgs("Opt".into()),
                mismatch("i32", "bool"),
                VariantNeedsValue {
                    variant: "unit".into(),
                    ty: "tuple()".into()
                },
            ]
        );
        let variants = |count: usize| -> String {
            let variants = (0..count).map(|i| format!("    v{i}\n"));
            format!("union Big:\n{}", variants.collect::<String>())
        };
        assert_eq!(check_src(&variants(256)).err(), None);
        assert_eq!(errors(&variants(257)), vec![TooManyVariants("Big".into())]);
    }

    #[test]
    fn unions_in_memory_are_a_tag_and_room_for_the_largest_variant() {
        let src = "\
union Shape:
    circle: f32
    rect: tuple(u8, i64)
    empty
struct S:
    flag: bool
    shape: Shape
let shapes: array(Shape) = [.circle(1.0), .rect((2, 3)), .empty]
fn sizes() -> tuple(uint, uint, uint):
    return (Shape.size, Shape.align, S.size)
fn get(p: &Shape) -> Shape:
    return p.*
fn set(p: &var S, s: Shape):
    p.shape = s
";
        let module = lower(src);
        assert_eq!(body(&module, "sizes"), "(return 24 8 32)");
        let mut bytes = [0u8; 72];
        bytes[8..12].copy_from_slice(&1f32.to_le_bytes());
        (bytes[24], bytes[32], bytes[40], bytes[48]) = (1, 2, 3, 2);
        assert_eq!(data(&module), [(0, &bytes[..])]);
        // Only the variant the tag names is read or written.
        assert_eq!(
            body(&module, "get"),
            "(set tmp1 (I32.Load8U offset=0 p)) \
             (return tmp1 \
             (if (I32.Eq tmp1 0) (F32.Reinterpret (F32.Load offset=8 p)) \
             (if (I32.Eq tmp1 1) (I32.Load8U offset=8 p) 0)) \
             (if (I32.Eq tmp1 1) (I64.Load offset=16 p) 0i64))"
        );
        assert_eq!(
            body(&module, "set"),
            "(I32.Store8 offset=8 p s) \
             (if (I32.Eq s 0) (then (F32.Store offset=16 p (I32.Reinterpret s.0))) (else )) \
             (if (I32.Eq s 1) \
             (then (I32.Store8 offset=16 p s.0) (I64.Store offset=24 p s.1)) (else ))"
        );
    }

    #[test]
    fn unions_within_unions_are_read_where_every_tag_holds_them() {
        let src = "\
union Inner:
    a: bool
    b: i16
union Outer:
    none
    some: Inner
fn get(p: &Outer) -> Outer:
    return p.*
fn set(p: &var Outer, x: i16):
    p.* = .some(.b(x + 1))
";
        let module = lower(src);
        assert_eq!(
            body(&module, "get"),
            "(set tmp1 (I32.Load8U offset=0 p)) \
             (set tmp2 (if (I32.Eq tmp1 1) (I32.Load8U offset=2 p) 0)) \
             (return tmp1 tmp2 \
             (if (I32.And (I32.Eq tmp1 1) (I32.Eq tmp2 0)) \
             (I32.Ne (I32.Load8U offset=4 p) 0) \
             (if (I32.And (I32.Eq tmp1 1) (I32.Eq tmp2 1)) (I32.Load16S offset=4 p) 0)))"
        );
        assert_eq!(
            body(&module, "set"),
            "(set tmp2 (I32.Extend16S (I32.Add x 1))) \
             (I32.Store8 offset=0 p 1) \
             (I32.Store8 offset=2 p 1) \
             (I32.Store16 offset=4 p tmp2)"
        );
        // The tag of a union within a variant is in whatever leaf the
        // variants share, which another may widen.
        let src = "\
union Inner:
    a: bool
    b: i16
union Outer:
    wide: i64
    some: Inner
fn get(p: &Outer) -> Outer:
    return p.*
fn set(p: &var Outer, o: Outer):
    p.* = o
fn eq(a: Outer, b: Outer) -> bool:
    return a == b
fn held(o: Outer) -> i16:
    match o:
        .some(.b(x)):
            return x
        else:
            return 0
";
        let module = lower(src);
        let get = module.funcs.iter().find(|f| f.name == "get").unwrap();
        assert_eq!(get.results, [ValType::I32, ValType::I64, ValType::I32]);
        let inner = |tag: u8| format!("(I32.And (I32.Eq tmp1 1) (I32.Eq (I64.Wrap tmp2) {tag}))");
        assert_eq!(
            body(&module, "get"),
            format!(
                "(set tmp1 (I32.Load8U offset=0 p)) \
                 (set tmp2 (if (I32.Eq tmp1 0) (I64.Load offset=8 p) \
                 (if (I32.Eq tmp1 1) (I32.ExtendU (I32.Load8U offset=8 p)) 0i64))) \
                 (return tmp1 tmp2 \
                 (if {} (I32.Ne (I32.Load8U offset=10 p) 0) \
                 (if {} (I32.Load16S offset=10 p) 0)))",
                inner(0),
                inner(1)
            )
        );
        let inner = |tag: u8| format!("(I32.And (I32.Eq o 1) (I32.Eq (I64.Wrap o.0) {tag}))");
        assert_eq!(
            body(&module, "set"),
            format!(
                "(I32.Store8 offset=0 p o) \
                 (if (I32.Eq o 0) (then (I64.Store offset=8 p o.0)) (else )) \
                 (if (I32.Eq o 1) (then (I32.Store8 offset=8 p (I64.Wrap o.0))) (else )) \
                 (if {} (then (I32.Store8 offset=10 p o.1)) (else )) \
                 (if {} (then (I32.Store16 offset=10 p o.1)) (else ))",
                inner(0),
                inner(1)
            )
        );
        let inner = |tag: u8| format!("(I32.And (I32.Eq a 1) (I32.Eq (I64.Wrap a.0) {tag}))");
        assert_eq!(
            body(&module, "eq"),
            format!(
                "(return (I32.And (I32.And (I32.And (I32.And (I32.Eq a b) \
                 (if (I32.Eq a 0) (I64.Eq a.0 b.0) 1)) \
                 (if (I32.Eq a 1) (I32.Eq (I64.Wrap a.0) (I64.Wrap b.0)) 1)) \
                 (if {} (I32.Eq a.1 b.1) 1)) \
                 (if {} (I32.Eq a.1 b.1) 1)))",
                inner(0),
                inner(1)
            )
        );
        assert_eq!(
            body(&module, "held"),
            "(set tmp3 o) (set tmp4 o.0) (set x o.1) \
             (block \
             (if (if (I32.Eq tmp3 1) \
             (seq (set tmp6 (I64.Wrap tmp4)) (I32.Eq tmp6 1)) 0) \
             (then (return x)) (else )) \
             (return 0)) \
             unreachable"
        );
    }

    #[test]
    fn mistyped_values_are_not_stored_to_unions_in_memory() {
        // Neither has the tags that say which variants to store.
        let src = "\
let items: varray(option(option(u32))) = [.none; 1]
fn f():
    items[0] = missing
    items[0] = 5
";
        assert_eq!(
            errors(src),
            [
                TypeErrorKind::UnknownName("missing".into()),
                mismatch("option(option(u32))", "i32"),
            ]
        );
    }

    #[test]
    fn unions_compare_their_tags_and_the_variant_they_hold() {
        let src = "\
union Shape:
    circle: f32
    named: array(u8)
    empty
union Size:
    exact: f32
    any
let same = Size.exact(1.0 + 1.0) == Size.exact(2.0)
let differ = Size.exact(0.0) == Size.any
fn consts() -> tuple(bool, bool):
    return (same, differ)
fn eq(a: Shape, b: Shape) -> bool:
    return a == b
fn ne(a: Shape, b: Shape) -> bool:
    return a != b
fn empty(a: Shape) -> bool:
    return a == .empty
fn round(a: Shape) -> bool:
    return .circle(1.0) != a
";
        let module = lower(src);
        assert_eq!(body(&module, "consts"), "(return 1 0)");
        let named = "a.0 a.1 b.0 b.1";
        let circles = "(I32.Reinterpret a.0) (I32.Reinterpret b.0)";
        assert_eq!(
            body(&module, "eq"),
            format!(
                "(return (if \
                 (I32.And (I32.Eq a b) (if (I32.Eq a 0) (F32.Eq {circles}) 1)) \
                 (if (I32.Eq a 1) (call ==(array(u8)) {named}) 1) 0))"
            )
        );
        assert_eq!(
            body(&module, "ne"),
            format!(
                "(return (if \
                 (I32.Or (I32.Ne a b) (if (I32.Eq a 0) (F32.Ne {circles}) 0)) \
                 1 (if (I32.Eq a 1) (I32.Eqz (call ==(array(u8)) {named})) 0)))"
            )
        );
        // A variant built in place is all that is compared with.
        assert_eq!(body(&module, "empty"), "(return (I32.Eq a 2))");
        assert_eq!(
            body(&module, "round"),
            "(return (I32.Or (I32.Ne 0 a) \
             (if (I32.Eq a 0) (F32.Ne 1f32 (I32.Reinterpret a.0)) 0)))"
        );
        assert_eq!(
            errors(
                "union R:\n    r: externref\n    none\nfn f(a: R) -> bool:\n    return a == .none\n"
            ),
            vec![TypeErrorKind::InvalidOperand {
                op: "==",
                ty: "R".into()
            }]
        );
    }

    #[test]
    fn unions_holding_externrefs_are_constants_that_memory_cannot_hold() {
        use TypeErrorKind::*;
        let src = "\
union Ref:
    some: externref
    none
var held: Ref = .none
let a = &Ref.none
let b = [Ref.none]
let c = [Ref.none; 2]
fn f() -> u32:
    return Ref.size
";
        let not_storable = || NotStorable("Ref".into());
        assert_eq!(
            errors(src),
            vec![
                not_storable(),
                not_storable(),
                not_storable(),
                not_storable()
            ]
        );
    }

    #[test]
    fn option_and_result_are_unions_that_need_no_declaration() {
        let src = "\
struct Node:
    value: i32
    next: option(&Node)
let slots: array(option(u8)) = [.none, .some(7)]
fn find(n: &Node, v: i32) -> option(&Node):
    if n.value == v:
        return .some(n)
    match n.next:
        .some(next):
            return find(next, v)
        .none:
            return .none
fn parse(x: i32) -> result(u8, bool):
    if x < 0:
        return result(u8, bool).err(false)
    return .ok(x as u8)
fn sizes() -> tuple(uint, uint, uint):
    return (option(i64).size, result(u8, f64).size, Node.size)
fn nothing(o: option(result(i32, f32))) -> bool:
    return o == .none
";
        let module = lower(src);
        // `none` is the variant that zeroed memory holds.
        assert_eq!(data(&module), [(0, &[0, 0, 1, 7][..])]);
        assert_eq!(body(&module, "sizes"), "(return 16 16 12)");
        assert_eq!(
            body(&module, "parse"),
            "(if (I32.LtS x 0) (then (return 1 0)) (else )) (return 0 (I32.And x 255))"
        );
        let find = module.funcs.iter().find(|f| f.name == "find").unwrap();
        assert_eq!(find.results, [ValType::I32, ValType::I32]);
        let find = body(&module, "find");
        assert!(
            find.starts_with("(if (I32.Eq (I32.Load offset=0 n) v) (then (return 1 n)) (else ))"),
            "{find}"
        );
        assert!(find.contains("(then (return 0 0)) (else ))"), "{find}");
        assert_eq!(body(&module, "nothing"), "(return (I32.Eq o 0))");

        use TypeErrorKind::*;
        let src = "\
struct option:
    pass
fn result():
    pass
fn f(a: option, b: option(i32, u8), c: result(i32), o: option(bool)) -> option(i32):
    let x = option(i32).both(1)
    let y = result.ok(1)
    let z = option
    match o:
        .some(true):
            pass
        .none:
            pass
    return .ok(1)
";
        let no_variant = |variant: &str| NoVariant {
            ty: "option(i32)".into(),
            variant: variant.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                DuplicateItem("option".into()),
                DuplicateItem("result".into()),
                MissingTypeArgs("option".into()),
                TypeArgCount {
                    name: "option".into(),
                    expected: 1,
                    found: 2
                },
                TypeArgCount {
                    name: "result".into(),
                    expected: 2,
                    found: 1
                },
                no_variant("both"),
                MissingTypeArgs("result".into()),
                MissingTypeArgs("option".into()),
                NonExhaustive(".some(false)".into()),
                no_variant("ok"),
            ]
        );
    }

    #[test]
    fn generic_unions_are_instantiated_per_type_argument() {
        let src = "\
union(T) Option:
    some: T
    none
union(T, E) Result:
    ok: T
    err: E
struct(T) Node:
    value: T
    next: Option(&Node(T))
fn(T) wrap(x: T) -> Option(T):
    return .some(x)
fn nothing(T: type) -> Option(T):
    return Option(T).none
fn size() -> uint:
    return Node(i64).size
fn f(n: &Node(i64)) -> Result(i64, Option(u8)):
    let a = wrap(1 as u8)
    let b: Option(u8) = nothing(u8)
    if a == b:
        return .err(a)
    return .ok(n.value)
";
        let module = lower(src);
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        assert_eq!(f.results, [ValType::I32, ValType::I64, ValType::I32]);
        assert_eq!(body(&module, "size"), "(return 16)");
        assert_eq!(body(&module, "wrap(u8)"), "(return 0 x)");
        assert_eq!(body(&module, "nothing(u8)"), "(return 1 0)");

        use TypeErrorKind::*;
        let src = "\
union(T) Option:
    some: T
    none
union(T) Grow:
    more: &Grow(Option(T))
    done
fn f(o: Option(i32)) -> Option(u8):
    let a = Option.some(1)
    let b = Option(i32, u8).none
    return o
";
        assert_eq!(
            errors(src),
            vec![
                ExpansiveRecursion("Grow".into()),
                MissingTypeArgs("Option".into()),
                TypeArgCount {
                    name: "Option".into(),
                    expected: 1,
                    found: 2
                },
                mismatch("Option(u8)", "Option(i32)"),
            ]
        );
    }

    #[test]
    fn unions_cross_to_the_host_as_their_leaves() {
        let src = "\
extern:
    fn get() -> Shape
pub union Shape:
    circle: f32
    empty
pub let unit: Shape = .circle(1.0)
pub var current: Shape = .empty
pub fn f() -> Shape:
    current = get()
    return current
";
        let module = lower(src);
        assert_eq!(module.imports[0].results, [ValType::I32, ValType::F32]);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.export.as_deref().unwrap(), g.init))
            .collect();
        assert_eq!(
            globals,
            [
                ("unit", Const::I32(0)),
                ("unit.0", Const::F32(1.0)),
                ("current", Const::I32(1)),
                ("current.0", Const::F32(0.0)),
            ]
        );
        // The tag is as the host gives it: one that no variant has is told
        // from every one that a variant does.
        assert_eq!(
            body(&module, "f"),
            "(call get [] -> [tmp0 tmp1]) (set tmp2 tmp0) (set tmp3 tmp1) \
             (set @current tmp2) (set @current.0 tmp3) \
             (return @current @current.0)"
        );
        // A leaf that the host gives is brought into the range of what the
        // variant that is held has in it.
        let src = "\
extern:
    fn get() -> result(u8, bool)
    fn wide() -> result(i16, i64)
fn f() -> result(u8, bool):
    return get()
fn g() -> result(i16, i64):
    return wide()
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(call get [] -> [tmp0 tmp1]) \
             (return tmp0 (if (I32.Eq tmp0 1) (I32.Ne tmp1 0) \
             (if (I32.Eq tmp0 0) (I32.And tmp1 255) tmp1)))"
        );
        assert_eq!(
            body(&module, "g"),
            "(call wide [] -> [tmp0 tmp1]) \
             (return tmp0 (if (I32.Eq tmp0 0) \
             (I32.ExtendU (I32.Extend16S (I64.Wrap tmp1))) tmp1))"
        );
    }

    #[test]
    fn match_runs_the_first_arm_whose_pattern_matches() {
        let src = "\
union Shape:
    circle: f32
    rect: tuple(f32, f32)
    empty
enum(u8) Color:
    red
    green = 5
fn area(s: Shape) -> f32:
    match s:
        .circle(r):
            return r * r
        .rect((w, h)):
            return w * h
        .empty:
            return 0.0
fn code(c: Color) -> i32:
    var n = 0
    match c:
        .red:
            n = 1
        .green:
            n = 2
    return n
fn other(get: fn() -> Shape) -> f32:
    match get():
        .circle(_):
            pass
        whole:
            return area(whole)
    return 1.0
";
        let module = lower(src);
        // The value is read once, and each arm tests and reads its copy, in
        // which `w` is in the leaf that the first arm named for `r`. A
        // function ends in a trap where wasm can't tell that it has returned.
        assert_eq!(
            body(&module, "area"),
            "(set tmp3 s) (set r s.0) (set h s.1) \
             (block \
             (if (I32.Eq tmp3 0) (then (return (F32.Mul r r))) (else )) \
             (if (I32.Eq tmp3 1) (then (return (F32.Mul r h))) (else )) \
             (if (I32.Eq tmp3 2) (then (return 0f32)) (else )) \
             unreachable) \
             unreachable"
        );
        assert_eq!(
            body(&module, "code"),
            "(set n 0) (set tmp2 c) \
             (block \
             (if (I32.Eq tmp2 0) (then (set n 1) (br 1)) (else )) \
             (if (I32.Eq tmp2 5) (then (set n 2) (br 1)) (else )) \
             unreachable) \
             (return n)"
        );
        // An arm that matches every value needs no test, and ends the rest.
        assert_eq!(
            body(&module, "other"),
            "(call_indirect get [] -> [tmp1 tmp2 tmp3]) \
             (set whole tmp1) (set whole.0 tmp2) (set whole.1 tmp3) \
             (block \
             (if (I32.Eq whole 0) (then (br 1)) (else )) \
             (return (call area whole whole.0 whole.1))) \
             (return 1f32)"
        );
    }

    #[test]
    fn match_arms_break_and_continue_the_loop_around_them() {
        let src = "\
union Shape:
    circle: f32
    empty
fn count(shapes: array(Shape)) -> i32:
    var n = 0
    for s in shapes:
        match s:
            .empty:
                continue
            .circle(r):
                if r > 1.0:
                    break
        n += 1
    return n
";
        let count = body(&lower(src), "count");
        assert!(count.contains("(then (br 2)) (else ))"), "{count}");
        assert!(count.contains("(then (br 4)) (else ))"), "{count}");
        // A function whose `match` returns in every arm returns.
        let src = "\
enum(u8) Color:
    red
    green
fn f(c: Color) -> i32:
    match c:
        .red:
            return 1
        .green:
            module.unreachable()
fn g(c: Color) -> i32:
    match c:
        .red:
            return 1
        else:
            pass
";
        assert_eq!(errors(src), vec![TypeErrorKind::MissingReturn("g".into())]);
    }

    #[test]
    fn match_arms_cover_every_value_and_each_matches_some() {
        use TypeErrorKind::*;
        let src = "\
union Shape:
    circle: f32
    rect: tuple(f32, f32)
    empty
enum(u8) Color:
    red
    green
union(T) Option:
    some: T
    none
fn f(s: Shape, c: Color, o: Option(Color), n: i32):
    match s:
        .circle(r):
            pass
    match c:
        .green:
            pass
    match c:
        .red:
            pass
        else:
            pass
    match c:
        .red:
            pass
        .green:
            pass
        else:
            pass
    match s:
        x:
            pass
        .empty:
            pass
    match o:
        .some(a):
            pass
        .some(b):
            pass
        .none:
            pass
    match n:
        x:
            pass
    match n:
        .zero:
            pass
        else:
            pass
    match c:
        .blue:
            pass
        .red(x):
            pass
        else:
            pass
    match s:
        .square:
            pass
        .circle:
            pass
        .empty(x):
            pass
        .rect((a, a)):
            pass
        .rect((a, b, c)):
            pass
        else:
            pass
";
        assert_eq!(
            errors_at(src),
            vec![
                (NonExhaustive(".rect(_)".into()), "s"),
                (NonExhaustive(".red".into()), "c"),
                (UnreachableArm, "else"),
                (UnreachableArm, ".empty"),
                (UnreachableArm, ".some(b)"),
                (
                    NoVariant {
                        ty: "i32".into(),
                        variant: "zero".into()
                    },
                    "zero"
                ),
                (
                    NoMember {
                        ty: "Color".into(),
                        member: "blue".into()
                    },
                    "blue"
                ),
                (NotCallable(".red".into()), "red"),
                (
                    NoVariant {
                        ty: "Shape".into(),
                        variant: "square".into()
                    },
                    "square"
                ),
                (
                    VariantNeedsValue {
                        variant: "circle".into(),
                        ty: "f32".into()
                    },
                    "circle"
                ),
                (VariantTakesNothing("empty".into()), "empty"),
                (DuplicateBinding("a".into()), "a"),
                (mismatch("tuple(_, _, _)", "tuple(f32, f32)"), "(a, b, c)"),
            ]
        );
    }

    #[test]
    fn match_patterns_test_literals_tuples_and_arrays() {
        let src = "\
fn sign(n: i32, strict: bool) -> i32:
    match (n, strict):
        (0, _):
            return 0
        (-1, true):
            return -1
        (x, false):
            return x
        else:
            return 1
fn word(s: array(u8)) -> u8:
    match s:
        \"zero\":
            return 0
        [a, _, 3]:
            return a
        []:
            return 1
        else:
            return 2
fn half(x: f32, b: bool) -> bool:
    match x:
        0.5:
            return true
        -2:
            return b
        else:
            pass
    match b:
        true:
            return false
        false:
            return true
";
        let module = lower(src);
        // Each test of a pattern is made only if those before it passed.
        assert_eq!(
            body(&module, "sign"),
            "(set x n) (set tmp3 strict) \
             (block \
             (if (I32.Eq x 0) (then (return 0)) (else )) \
             (if (if (I32.Eq x -1) tmp3 0) (then (return -1)) (else )) \
             (if (I32.Eqz tmp3) (then (return x)) (else )) \
             (return 1)) \
             unreachable"
        );
        // A string is placed in memory, and an element is read once the
        // array is known to have it.
        assert_eq!(data(&module), [(0, &b"zero"[..])]);
        assert_eq!(
            body(&module, "word"),
            "(set tmp2 s.ptr) (set tmp3 s.len) \
             (block \
             (if (call ==(array(u8)) tmp2 tmp3 0 4) (then (return 0)) (else )) \
             (if (if (I32.Eq tmp3 3) \
             (seq (set a (I32.Load8U offset=0 tmp2)) \
             (seq (set tmp5 (I32.Load8U offset=2 tmp2)) (I32.Eq tmp5 3))) 0) \
             (then (return a)) (else )) \
             (if (I32.Eq tmp3 0) (then (return 1)) (else )) \
             (return 2)) \
             unreachable"
        );
        assert_eq!(
            body(&module, "half"),
            "(set tmp2 x) \
             (block \
             (if (F32.Eq tmp2 0.5f32) (then (return 1)) (else )) \
             (if (F32.Eq tmp2 -2f32) (then (return b)) (else ))) \
             (set tmp3 b) \
             (block \
             (if tmp3 (then (return 0)) (else )) \
             (if (I32.Eqz tmp3) (then (return 1)) (else )) \
             unreachable) \
             unreachable"
        );
    }

    #[test]
    fn strings_in_patterns_are_placed_once_with_the_literals() {
        let src = "\
let greeting = \"hi\"
fn(T) kind(s: array(u8), x: T) -> i32:
    match s:
        \"one\":
            return 1
        \"\":
            return 0
        else:
            return 2
fn f(s: array(u8)) -> i32:
    if s == greeting:
        match s:
            \"two\":
                return kind(s, 1) + kind(s, true)
            \"one\":
                return 1
            else:
                pass
    return module.static.len as i32
";
        let module = lower(src);
        assert_eq!(
            data(&module),
            [(0, &b"hi"[..]), (2, &b"one"[..]), (5, &b"two"[..])]
        );
        let f = body(&module, "f");
        assert!(f.contains("(call ==(array(u8)) tmp2 tmp3 5 3)"), "{f}");
        assert!(f.contains("(call ==(array(u8)) tmp2 tmp3 2 3)"), "{f}");
        assert!(f.ends_with("(return 8)"), "{f}");
    }

    #[test]
    fn nested_patterns_cover_every_value_between_them() {
        use TypeErrorKind::*;
        let src = "\
enum(u8) Color:
    red
    green
union(T) Option:
    some: T
    none
fn f(a: bool, b: bool, o: Option(bool), n: u8, s: array(u8), t: tuple(Color, bool)):
    match (a, b):
        (true, _):
            pass
        (false, true):
            pass
        (false, false):
            pass
    match (a, b):
        (true, _):
            pass
        (_, true):
            pass
    match o:
        .some(true):
            pass
        .none:
            pass
    match n:
        0:
            pass
        1:
            pass
    match n:
        0:
            pass
        0:
            pass
        else:
            pass
    match s:
        \"a\":
            pass
        [x]:
            pass
        [_]:
            pass
        \"a\":
            pass
        else:
            pass
    match s:
        [_]:
            pass
        \"b\":
            pass
        \"cd\":
            pass
        [99, 100]:
            pass
        [99, _]:
            pass
        else:
            pass
    match t:
        (.red, true):
            pass
        (_, false):
            pass
    match (a, b):
        (true, _):
            pass
        (_, _):
            pass
        else:
            pass
    match 0.0:
        0.0:
            pass
        -0.0:
            pass
        else:
            pass
";
        assert_eq!(
            errors_at(src),
            vec![
                (NonExhaustive("(false, false)".into()), "(a, b)"),
                (NonExhaustive(".some(false)".into()), "o"),
                (NonExhaustive("_".into()), "n"),
                (UnreachableArm, "0"),
                (UnreachableArm, "[_]"),
                (UnreachableArm, "\"a\""),
                (UnreachableArm, "\"b\""),
                (UnreachableArm, "[99, 100]"),
                (NonExhaustive("(.green, true)".into()), "t"),
                (UnreachableArm, "else"),
                (UnreachableArm, "-0.0"),
            ]
        );
    }

    #[test]
    fn literal_patterns_are_of_the_type_they_test() {
        use TypeErrorKind::*;
        let src = "\
union(T) Option:
    some: T
    none
fn(T) g(o: Option(T)):
    match o:
        .some(0):
            pass
        else:
            pass
fn f(n: u8, p: &u8, s: array(i32), w: varray(u8)):
    match n:
        255:
            pass
        300:
            pass
        -1:
            pass
        1.5:
            pass
        true:
            pass
        \"a\":
            pass
        [a]:
            pass
        else:
            pass
    match p:
        0:
            pass
        else:
            pass
    match s:
        \"a\":
            pass
        [1.5, b]:
            pass
        else:
            pass
    match w:
        \"a\":
            pass
        [1, 2]:
            pass
        else:
            pass
";
        assert_eq!(
            errors_at(src),
            vec![
                (mismatch("i32", "T"), "0"),
                (IntOutOfRange("u8".into()), "300"),
                (
                    InvalidOperand {
                        op: "-",
                        ty: "u8".into()
                    },
                    "-1"
                ),
                (mismatch("f64", "u8"), "1.5"),
                (mismatch("bool", "u8"), "true"),
                (mismatch("array(u8)", "u8"), "\"a\""),
                (mismatch("array(_)", "u8"), "[a]"),
                (mismatch("i32", "&u8"), "0"),
                (mismatch("array(u8)", "array(i32)"), "\"a\""),
                (mismatch("f64", "i32"), "1.5"),
            ]
        );
    }

    #[test]
    fn match_in_a_generic_function_binds_what_holds_its_type_parameters() {
        use TypeErrorKind::*;
        let src = "\
union(T) Option:
    some: T
    none
fn(T) unwrap_or(o: Option(T), d: T) -> T:
    match o:
        .some(x):
            return x
        .none:
            return d
fn(T) first(pair: T) -> i32:
    match pair:
        whole:
            return 1
fn(T) either(a: Option(T), b: Option(T)) -> Option(T):
    return a
fn f() -> i64:
    let a = either(.none, Option(u8).some(1))
    let b = either(Option(u8).some(1), .none)
    return unwrap_or(Option(i64).some(1), 2) + first(a == b) as i64
";
        let module = lower(src);
        assert_eq!(
            body(&module, "unwrap_or(i64)"),
            "(set tmp3 o) (set x o.0) \
             (block \
             (if (I32.Eq tmp3 0) (then (return x)) (else )) \
             (if (I32.Eq tmp3 1) (then (return d)) (else )) \
             unreachable) \
             unreachable"
        );
        // A type parameter is no union, enum or tuple until it's given a type.
        let src = "\
enum(u8) Color:
    red
fn(T) f(x: T) -> i32:
    match x:
        .red:
            return 1
        (a, b):
            return 2
        else:
            return 0
fn g() -> i32:
    return f(Color.red)
";
        assert_eq!(
            errors(src),
            vec![
                NoVariant {
                    ty: "T".into(),
                    variant: "red".into()
                },
                mismatch("tuple(_, _)", "T"),
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
pub let same = T.a == T.b
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
    fn units_and_structs_compare() {
        let src = "\
struct P:
    x: i32
    y: f32
pub let point = P(x: 1, y: 2.0) == P(x: 1, y: 2.0)
fn u():
    return
fn f() -> bool:
    let a = u() == u()
    return a
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.init))
            .collect();
        assert_eq!(globals[..1], [("point", Const::I32(1))]);
        assert_eq!(
            body(&module, "f"),
            "(call u [] -> []) (call u [] -> []) (set a 1) (return a)"
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
            "(set x (call ==(array(u8)) a.ptr a.len b.ptr b.len)) \
             (set y (if (I32.Ne s.n t.n) 1 \
             (I32.Eqz (call ==(array(u8)) s.name.ptr s.name.len t.name.ptr t.name.len)))) \
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
             (call ==(array(N)) a.kids.ptr a.kids.len b.kids.ptr b.kids.len) 0))"
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
    let e = S.size + S.align
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
             (set e (I32.Add 1 1)) (return b)"
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
    for b in S:
        pass
    for c in E:
        pass
";
        assert_eq!(
            errors(src),
            vec![
                TypeErrorKind::NotAValue("S".into()),
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
fn f(p: &var S) -> R:
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

    #[test]
    fn functions_are_values_called_through_the_table() {
        let src = "\
fn inc(x: i32) -> i32:
    return x + 1
fn dec(x: i32) -> i32:
    return x - 1
fn apply(f: fn(i32) -> i32, x: i32) -> i32:
    return f(x)
fn main() -> i32:
    var g = dec
    g = inc
    return apply(g, 1) + apply(dec, 2) + apply(inc, 3)
";
        let module = lower(src);
        // Indices are given in the order pointers are first taken.
        assert_eq!(table(&module), ["dec", "inc"]);
        assert_eq!(module.table.as_ref().unwrap().export, "table");
        assert_eq!(body(&module, "apply"), "(return (call_indirect f x))");
        assert_eq!(
            body(&module, "main"),
            "(set g 1) (set g 2) (return (I32.Add (I32.Add \
             (call apply g 1) (call apply 1 2)) (call apply 2 3)))"
        );
        let func = module.funcs.iter().find(|f| f.name == "apply").unwrap();
        let Stmt::Return(values) = &func.body[0] else {
            panic!()
        };
        let Expr::CallIndirect { ty, .. } = &values[0] else {
            panic!()
        };
        assert_eq!(ty.params, [ValType::I32]);
        assert_eq!(ty.results, [ValType::I32]);

        assert_eq!(lower("fn f():\n    pass\n").table, None);
    }

    #[test]
    fn any_function_pointer_can_be_called() {
        let src = "\
struct S:
    run: fn(i32) -> i32
    done: fn()
fn inc(x: i32) -> i32:
    return x + 1
fn nop():
    pass
fn pair(x: i32) -> tuple(i32, i32):
    return (x, x)
fn pick() -> fn(i32) -> i32:
    return inc
var handler = inc
fn field(s: S) -> i32:
    s.done()
    return s.run(1)
fn element(fs: array(fn(i32) -> i32)) -> i32:
    return fs[1](2)
fn returned() -> i32:
    return pick()(3)
fn deref(p: &fn(i32) -> tuple(i32, i32)) -> i32:
    let (a, b) = p.*(4)
    return a
fn global() -> i32:
    return handler(5)
fn param(inc: fn(i32) -> i32) -> i32:
    return inc(6)
fn cast(i: uint) -> i32:
    return (i as! fn(i32) -> i32)(7)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "field"),
            "(call_indirect s.done [] -> []) (return (call_indirect s.run 1))"
        );
        // After the bounds check, which leaves the element's address.
        let element = body(&module, "element");
        let call = "(return (call_indirect (I32.Load offset=0 tmp2) 2))";
        assert!(element.ends_with(call), "{element}");
        assert_eq!(
            body(&module, "returned"),
            "(return (call_indirect (call pick ) 3))"
        );
        assert_eq!(
            body(&module, "deref"),
            "(call_indirect (I32.Load offset=0 p) [4] -> [tmp1 tmp2]) \
             (set a tmp1) (set b tmp2) (return a)"
        );
        assert_eq!(
            body(&module, "global"),
            "(return (call_indirect @handler 5))"
        );
        // A variable is called before the function it shadows.
        assert_eq!(body(&module, "param"), "(return (call_indirect inc 6))");
        assert_eq!(body(&module, "cast"), "(return (call_indirect i 7))");
    }

    #[test]
    fn callees_are_evaluated_before_arguments() {
        let src = "\
var count = 0
var handler = inc
fn inc(x: i32) -> i32:
    return x + 1
fn pick() -> fn(i32) -> i32:
    count += 1
    return inc
fn next() -> i32:
    handler = pick()
    return count
fn impure_callee() -> i32:
    return pick()(count)
fn changed_callee() -> i32:
    return handler(next())
fn stable_callee(f: fn(i32) -> i32) -> i32:
    return f(next())
fn pure_both() -> i32:
    return handler(count)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "impure_callee"),
            "(set tmp0 (call pick )) (return (call_indirect tmp0 @count))"
        );
        assert_eq!(
            body(&module, "changed_callee"),
            "(set tmp0 @handler) (return (call_indirect tmp0 (call next )))"
        );
        assert_eq!(
            body(&module, "stable_callee"),
            "(return (call_indirect f (call next )))"
        );
        assert_eq!(
            body(&module, "pure_both"),
            "(return (call_indirect @handler @count))"
        );
    }

    #[test]
    fn pointers_to_imports_bring_results_into_range() {
        let src = "\
extern:
    fn log(n: i32)
    fn flag() -> bool
    fn small(x: i32) -> tuple(u8, i64)
fn f() -> bool:
    let a = log
    let b = flag
    let c = small
    let d = flag
    return b()
";
        let module = lower(src);
        // `log` is in the table itself; the others are called through
        // functions named after them.
        assert_eq!(table(&module), ["log", "extern flag", "extern small"]);
        assert_eq!(
            body(&module, "extern flag"),
            "(return (I32.Ne (call flag ) 0))"
        );
        assert_eq!(
            body(&module, "extern small"),
            "(call small [x] -> [tmp1 tmp2]) (return (I32.And tmp1 255) tmp2)"
        );
        assert_eq!(
            body(&module, "f"),
            "(set a 1) (set b 2) (set c 3) (set d 2) (return (call_indirect b ))"
        );
    }

    #[test]
    fn generic_function_pointers_take_the_expected_type() {
        let src = "\
fn(T) id(x: T) -> T:
    return x
fn(T, U) apply(x: T, f: fn(T) -> U) -> U:
    return f(x)
fn double(x: i32) -> i64:
    return x as i64 * 2
fn same(x: i32) -> i32:
    return x
fn take(f: fn(f32) -> f32):
    pass
fn f(n: i32) -> fn(i64) -> i64:
    let g: fn(u8) -> u8 = id
    let a = apply(n, double)
    let b = apply(2, same)
    let c = apply(g(3), g)
    take(id)
    return id
";
        let module = lower(src);
        assert_eq!(
            table(&module),
            ["id(u8)", "double", "same", "id(f32)", "id(i64)"]
        );
        let names: Vec<_> = module.funcs.iter().map(|f| f.name.as_str()).collect();
        for instance in ["apply(i32, i64)", "apply(i32, i32)", "apply(u8, u8)"] {
            assert!(names.contains(&instance), "{instance} in {names:?}");
        }

        use TypeErrorKind::*;
        let src = "\
fn(T) id(x: T) -> T:
    return x
fn(T, U) apply(x: T, f: fn(T) -> U) -> U:
    return f(x)
fn f():
    let a = id
    let b: fn(u8) -> i32 = id
    let c: fn(u8, u8) -> u8 = id
    let d: i32 = id
    let e = apply(1, id)
";
        let cannot_infer = |func: &str, param: &str| CannotInfer {
            func: func.into(),
            param: param.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                cannot_infer("id", "T"),
                mismatch("fn(u8) -> i32", "fn(u8) -> u8"),
                cannot_infer("id", "T"),
                cannot_infer("id", "T"),
                cannot_infer("apply", "U"),
            ]
        );
    }

    #[test]
    fn function_pointers_are_compared_cast_and_stored_as_indices() {
        let src = "\
struct S:
    a: u8
    f: fn(i32) -> i32
fn inc(x: i32) -> i32:
    return x + 1
fn f(p: &var S, g: fn(i32) -> i32) -> bool:
    p.f = g
    let i = g as uint
    let h = i as! fn(i32)
    let k = h as! fn() -> f32
    let z = 0 as! fn()
    let t = (fn(i32) -> i32).size
    let s = tuple(u8, fn(externref) -> externref).size
    return p.f == inc and g != inc
";
        let module = lower(src);
        let f = body(&module, "f");
        for part in [
            "(I32.Store offset=4 p g)",
            "(set i g) (set h i) (set k h) (set z 0)",
            "(set t 4) (set s 8)",
            "(I32.Eq (I32.Load offset=4 p) 1)",
            "(I32.Ne g 1)",
        ] {
            assert!(f.contains(part), "{part}\n{f}");
        }
    }

    #[test]
    fn function_pointers_are_constants() {
        let src = "\
fn inc(x: i32) -> i32:
    return x + 1
fn dec(x: i32) -> i32:
    return x - 1
pub let first = dec
pub var current: fn(i32) -> i32 = inc
let handlers: array(fn(i32) -> i32) = [inc, dec, inc]
enum(fn(i32) -> i32) Op:
    up = inc
    down = dec
fn f(op: Op) -> i32:
    var total = 0
    for o in Op:
        total = (o as fn(i32) -> i32)(total)
    return (op as fn(i32) -> i32)(total)
";
        let module = lower(src);
        assert_eq!(table(&module), ["dec", "inc"]);
        let inits: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        assert_eq!(inits[..2], [Const::I32(1), Const::I32(2)]);
        assert_eq!(
            data(&module),
            [(0, &[2, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0][..])]
        );
        assert_eq!(
            body(&module, "f"),
            "(set total 0) (block \
             (block (set o 2) (set total (call_indirect o total))) \
             (block (set o 1) (set total (call_indirect o total)))) \
             (return (call_indirect op total))"
        );

        let src = "\
fn nop():
    pass
enum(fn()) E:
    a = nop
    b = nop
";
        let duplicate = TypeErrorKind::DuplicateValue {
            member: "b".into(),
            same_as: "a".into(),
        };
        assert_eq!(errors(src), vec![duplicate]);
    }

    #[test]
    fn function_pointer_errors() {
        use TypeErrorKind::*;
        let src = "\
fn inc(x: i32) -> i32:
    return x + 1
enum(fn(i32) -> i32) Op:
    up = inc
fn f(g: fn(i32) -> i32, n: i32, h: fn(i32)):
    g(x: 1)
    g()
    g(1, 2)
    g(true)
    n(1)
    fn(i32)(1)
    Op.up(1)
    let a: fn(i32) = inc
    let b = g < g
    let c = g as &i32
    let d = g.x
    h(g)
    let e: fn(Nope) = inc
    inc(i32)(1)
";
        assert_eq!(
            errors(src),
            vec![
                LabelledPointerArg,
                TooFewArgs {
                    expected: 1,
                    found: 0
                },
                TooManyArgs {
                    expected: 1,
                    found: 2
                },
                mismatch("i32", "bool"),
                NotCallable("n".into()),
                NotAValue("fn(i32)".into()),
                NotCallable("Op.up".into()),
                mismatch("fn(i32)", "fn(i32) -> i32"),
                invalid_operand("<", "fn(i32) -> i32"),
                InvalidCast {
                    from: "fn(i32) -> i32".into(),
                    to: "&i32".into()
                },
                NoField {
                    ty: "fn(i32) -> i32".into(),
                    field: "x".into()
                },
                mismatch("i32", "fn(i32) -> i32"),
                UnknownType("Nope".into()),
                NotAValue("i32".into()),
                NotCallable("expression".into()),
            ]
        );
        assert_eq!(
            LabelledPointerArg.to_string(),
            "arguments of a call through a function pointer can't be labelled"
        );
    }

    #[test]
    fn function_types_are_checked_like_the_types_they_hold() {
        // A function pointer is an index, so it ends a cycle of structs and
        // is stored whatever it takes.
        let src = "\
struct Node:
    visit: fn(Node) -> Node
    host: fn(externref) -> externref
fn f(p: &Node) -> uint:
    return Node.size + Node.align
";
        let module = lower(src);
        assert_eq!(body(&module, "f"), "(return (I32.Add 8 4))");

        use TypeErrorKind::*;
        let src = "\
struct Hidden:
    x: i32
struct Host:
    r: externref
struct(T) Grow:
    next: fn(Grow(tuple(T, T)))
pub fn take(f: fn(Hidden) -> i32):
    pass
pub fn table():
    pass
fn g(f: fn(&Host)):
    pass
";
        assert_eq!(
            errors(src),
            vec![
                ReservedExport("table".into()),
                ExpansiveRecursion("Grow".into()),
                PrivateInPublic {
                    ty: "Hidden".into(),
                    item: "take".into()
                },
                NotStorable("Host".into()),
            ]
        );
    }

    #[test]
    fn omitted_fields_have_their_defaults() {
        let src = "\
pub enum(u8) Mode:
    off
    on = 3
let BASE = 10
fn inc(x: i32) -> i32:
    return x + 1
pub struct Inner:
    a: i32 = BASE * 2
    b: f32 = 1
pub struct Conf:
    pub n: i32
    step: i64 = 1
    mode: Mode = Mode.on
    inner: Inner = Inner(b: 2)
    name: array(u8) = \"duck\"
    next: &Conf = 0
    cb: fn(i32) -> i32 = inc
pub let made = Conf(n: 7)
fn f(x: i32) -> Conf:
    return Conf(mode: Mode.off, n: x)
fn g() -> Inner:
    return Inner()
";
        let module = lower(src);
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| format!("{} {}", g.name, konst(g.init)))
            .collect();
        let expected = [
            "made.n 7",
            "made.step 1i64",
            "made.mode 3",
            "made.inner.a 20",
            "made.inner.b 2f32",
            "made.name.ptr 0",
            "made.name.len 4",
            "made.next 0",
            "made.cb 1",
        ];
        assert_eq!(globals, expected);
        assert_eq!(body(&module, "f"), "(return x 1i64 0 20 2f32 0 4 0 1)");
        assert_eq!(body(&module, "g"), "(return 20 1f32)");
    }

    #[test]
    fn defaults_are_constant() {
        use TypeErrorKind::*;
        let src = "\
fn call() -> i32:
    return 1
struct C:
    c: i32 = 1 / 0
    d: i32 = call()
    e: u8 = 300
    f: bool = 1
    g: i32
fn f() -> i32:
    return C(g: 1).c + C().d
";
        assert_eq!(
            errors(src),
            vec![
                ConstTrap,
                IntOutOfRange("u8".into()),
                mismatch("bool", "i32"),
                MissingArg("g".into()),
            ]
        );
    }

    #[test]
    fn instances_share_the_defaults_of_a_generic_struct() {
        let src = "\
let pad = \"abc\"
struct(T) Vec:
    items: varray(T) = []
    head: &var T = 0
    len: u32 = 0
    elem: T
fn f() -> Vec(i64):
    return Vec(i64)(elem: 5)
fn g() -> Vec(u8):
    return Vec(u8)(len: 2, elem: 1)
";
        let module = lower(src);
        // The empty literal is at the end of the data so far.
        assert_eq!(body(&module, "f"), "(return 3 0 0 0 5i64)");
        assert_eq!(body(&module, "g"), "(return 3 0 0 2 1)");
    }

    #[test]
    fn defaults_cannot_depend_on_type_parameters() {
        use TypeErrorKind::*;
        let src = "\
fn(T) id(x: T) -> T:
    return x
struct(T) Box:
    value: &T = 0
struct(T, U) Bad:
    size: u32 = T.size
    value: U = 0
    pair: tuple(T, i32) = (0, 1)
    cast: &T = 0 as &U
    cb: fn(T) -> T = id
    inner: Box(U) = 0
    arg: Box(i32) = Box(T)()
    ok: &T = 0
fn f() -> Bad(u8, u8):
    return Bad(u8, u8)()
";
        let errors = check_src(src).unwrap_err();
        let found: Vec<_> = errors
            .iter()
            .map(|e| {
                let span = e.span.unwrap();
                (e.kind.clone(), &src[span.start..span.end])
            })
            .collect();
        let uses = |param: &str, text: &'static str| (DefaultUsesParam(param.into()), text);
        let mismatch_of = |param: &str, expected: &str, found: &str| DefaultMismatch {
            param: param.into(),
            expected: expected.into(),
            found: found.into(),
        };
        assert_eq!(
            found,
            vec![
                uses("T", "T"),
                uses("U", "U"),
                uses("T", "id"),
                (mismatch("Box(U)", "i32"), "0"),
                uses("T", "T"),
                (mismatch_of("value", "u8", "i32"), "Bad(u8, u8)()"),
                (
                    mismatch_of("pair", "tuple(u8, i32)", "tuple(i32, i32)"),
                    "Bad(u8, u8)()"
                ),
            ]
        );
    }

    #[test]
    fn field_defaults_have_the_types_their_fields_stand_for() {
        let src = "\
struct Head:
    id: i32
struct Named:
    id: i32
    name: array(u8)
let nobody = &Named(id: 3, name: \"\")
struct(T: Head) Holder:
    item: &T = nobody
    count: T = Named(id: 1, name: \"\")
struct(T) Slot:
    value: T = 7
fn f() -> i32:
    let h = Holder(Named)()
    let s = Slot(i32)()
    let t = Slot(u8)(value: 2)
    return h.item.id + h.count.id + s.value + t.value as i32
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(set h.item 0) (set h.count.id 1) (set h.count.name.ptr 12) \
             (set h.count.name.len 0) (set s.value 7) (set t.value 2) \
             (return (I32.Add (I32.Add (I32.Add (I32.Load offset=0 h.item) h.count.id) s.value) \
             t.value))"
        );

        use TypeErrorKind::*;
        let src = "\
struct Head:
    id: i32
struct Named:
    id: i32
    name: array(u8)
struct Other:
    x: f32
let nobody = &Named(id: 3, name: \"\")
let other = &Other(x: 1.0)
struct(T: Head) Holder:
    item: &T = nobody
struct(T: Head) Bad:
    item: &T = other
struct(T) Slot:
    value: T = 7
fn slot(T: type) -> Slot(T):
    return Slot(T)()
fn f(h: &Head):
    Holder(Head)()
    Holder(Head)(item: h)
    Slot(u8)()
";
        let mismatch_of = |param: &str, expected: &str, found: &str| DefaultMismatch {
            param: param.into(),
            expected: expected.into(),
            found: found.into(),
        };
        assert_eq!(
            errors(src),
            vec![
                BoundNotMet {
                    ty: "Other".into(),
                    bound: "Head".into()
                },
                mismatch_of("value", "T", "i32"),
                mismatch_of("item", "&Head", "&Named"),
                mismatch_of("value", "u8", "i32"),
            ]
        );
    }

    #[test]
    fn writable_literals_in_defaults_are_empty() {
        let src = "\
let N: uint = 0
let SHARED: varray(u8) = [0; 4]
struct S:
    a: array(u8) = \"ro\"
    b: varray(u8) = \"\"
    c: varray(i32) = []
    d: varray(i32) = [0; N]
    e: varray(varray(u8)) = []
    f: varray(u8) = SHARED
    g: varray(u8) = \"abc\" as! varray(u8)
    h: array(array(u8)) = [\"x\", \"y\"]
fn f() -> S:
    return S()
";
        lower(src);

        let src = "\
struct S:
    a: varray(u8) = \"abc\"
    b: varray(i32) = [1, 2]
    c: varray(i32) = [0; 4]
    d: varray(array(u8)) = [\"a\"]
    e: array(varray(u8)) = [\"a\"]
    f: tuple(varray(u8), i32) = (\"a\", 1)
";
        assert_eq!(errors(src), vec![TypeErrorKind::SharedLiteral; 6]);
    }

    #[test]
    fn omitted_arguments_have_their_defaults() {
        let src = "\
extern:
    fn log(n: i32, base: i32 = 10)
let STEP = 2
struct P:
    x: i32
    y: i32 = 3
fn inc(x: i32) -> i32:
    return x + 1
fn add(a: i32, b: i32 = STEP * 2, c: i64 = 1) -> i64:
    return (a + b) as i64 + c
fn mid(a: i32 = 7, b: i32) -> i32:
    return a - b
fn wide(p: P = P(x: 1), s: array(u8) = \"duck\", cb: fn(i32) -> i32 = inc) -> i32:
    return cb(p.x)
pub fn tick(dt: f64 = 0.5) -> f64:
    return dt
fn f(x: i32):
    log(x)
    log(x, 2)
    add(x)
    add(x, 5)
    add(x, c: 9)
    add(c: 9, a: x)
    x |> add(_, _)
fn g():
    mid(b: 1)
    mid(2, 3)
    wide()
    wide(cb: inc, p: P(x: 4, y: 5))
    tick()
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(call log [x 10] -> []) (call log [x 2] -> []) \
             (drop (call add x 4 1i64)) (drop (call add x 5 1i64)) \
             (drop (call add x 4 9i64)) (drop (call add x 4 9i64)) \
             (drop (call add x x 1i64))"
        );
        assert_eq!(
            body(&module, "g"),
            "(drop (call mid 7 1)) (drop (call mid 2 3)) \
             (drop (call wide 1 3 0 4 1)) (drop (call wide 4 5 0 4 1)) \
             (drop (call tick 0.5f64))"
        );
        assert_eq!(data(&module), [(0, &b"duck"[..])]);
        // Neither the host nor the function itself knows of a default.
        assert_eq!(module.imports[0].params, vec![ValType::I32; 2]);
        let tick = module.funcs.iter().find(|f| f.name == "tick").unwrap();
        assert_eq!(tick.params, vec![ValType::F64]);
    }

    /// Each error of `src`, with the text it points at.
    fn errors_at(src: &str) -> Vec<(TypeErrorKind, &str)> {
        let errors = check_src(src).unwrap_err();
        let at = |e: TypeError| {
            let span = e.span.unwrap();
            (e.kind, &src[span.start..span.end])
        };
        errors.into_iter().map(at).collect()
    }

    #[test]
    fn parameter_defaults_follow_every_global() {
        let src = "\
fn f(a: i32 = LATER, p: Late = Late()) -> i32:
    return a + p.x
let LATER = 2
struct Late:
    x: i32 = LATER * 2
fn g() -> i32:
    return f()
";
        assert_eq!(body(&lower(src), "g"), "(return (call f 2 4))");
    }

    #[test]
    fn parameter_defaults_are_constant() {
        use TypeErrorKind::*;
        let src = "\
let a = 5
var count = 0
fn call(n: i32 = 1) -> i32:
    return n
let early = call()
fn f(a: i32, b: i32 = a, c: i32 = b + 1, d: i32 = d, e: i32 = 2):
    pass
fn g(x: i32 = call(), y: i32 = count, z: u8 = 300, w: bool = 1, v: i32 = 1 / 0):
    pass
fn h(a: varray(u8) = \"abc\", b: &var i32 = &var 0, c: varray(i32) = [], d: &i32 = &1):
    pass
fn m():
    f(1)
    g()
    h()
";
        assert_eq!(
            errors_at(src),
            vec![
                (DefaultReadsParam("a".into()), "a"),
                (DefaultReadsParam("b".into()), "b"),
                (DefaultReadsParam("d".into()), "d"),
                (IntOutOfRange("u8".into()), "300"),
                (mismatch("bool", "i32"), "1"),
                (ConstTrap, "1 / 0"),
                (SharedLiteral, "\"abc\""),
                (SharedPointee, "&var 0"),
            ]
        );
    }

    #[test]
    fn arguments_without_defaults_are_still_counted() {
        use TypeErrorKind::*;
        let src = "\
fn k(a: i32, b: i32 = 1, c: i32 = 2) -> i32:
    return a
fn start(verbose: bool = false):
    pass
let p = k
fn m() -> i32:
    k()
    k(1, 2, 3, 4)
    k(1, b: 2, b: 3)
    k(1, d: 2)
    k(b: 2)
    let short: fn(i32) -> i32 = k
    return p(1) + k(1)
";
        assert_eq!(
            errors_at(src),
            vec![
                (MissingArg("a".into()), "k()"),
                (
                    TooManyArgs {
                        expected: 3,
                        found: 4
                    },
                    "4"
                ),
                (DuplicateArg("b".into()), "3"),
                (UnknownLabel("d".into()), "2"),
                (MissingArg("a".into()), "k(b: 2)"),
                (mismatch("fn(i32) -> i32", "fn(i32, i32, i32) -> i32"), "k"),
                (
                    TooFewArgs {
                        expected: 3,
                        found: 1
                    },
                    "p(1)"
                ),
            ]
        );
        // The host calls the start function, and gives no argument.
        let errors = check_start(src, "start").unwrap_err();
        assert!(
            errors
                .iter()
                .any(|e| e.kind == InvalidStart("start".into()))
        );
    }

    #[test]
    fn instances_share_the_defaults_of_a_generic_fn() {
        let src = "\
let buf: varray(i64) = [0; 4]
fn(T) fill(a: varray(T), n: u32 = 3, p: &T = 0) -> u32:
    return n
fn only(T: type, p: &T = 0, n: i32 = 1) -> i32:
    return n
fn(T) outer(a: varray(T)) -> u32:
    return fill(a) + fill(a, p: 8)
fn f() -> u32:
    return fill(buf) + fill(buf, 2) + outer(buf)
fn g() -> i32:
    return only(u8) + only(u8, n: 2)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(return (I32.Add (I32.Add (call fill(i64) 0 4 3 0) (call fill(i64) 0 4 2 0)) \
             (call outer(i64) 0 4)))"
        );
        assert_eq!(
            body(&module, "g"),
            "(return (I32.Add (call only(u8) 0 1) (call only(u8) 0 2)))"
        );
        assert_eq!(
            body(&module, "outer(i64)"),
            "(return (I32.Add (call fill(i64) a.ptr a.len 3 0) (call fill(i64) a.ptr a.len 3 8)))"
        );
    }

    #[test]
    fn parameter_defaults_cannot_depend_on_type_parameters() {
        use TypeErrorKind::*;
        let src = "\
fn(T) id(x: T) -> T:
    return x
fn(T, U) bad(a: T, size: u32 = T.size, v: U = 0, pair: tuple(T, i32) = (0, 1), cast: &T = 0 as &U, cb: fn(T) -> T = id, ok: &U = 0) -> T:
    return a
fn(T) only(p: &T = 0) -> i32:
    return 1
fn f() -> i32:
    return bad(1) + only()
";
        let uses = |param: &str, text: &'static str| (DefaultUsesParam(param.into()), text);
        let cannot_infer = CannotInfer {
            func: "only".into(),
            param: "T".into(),
        };
        assert_eq!(
            errors_at(src),
            vec![
                uses("T", "T"),
                uses("U", "U"),
                uses("T", "id"),
                (cannot_infer, "only()"),
            ]
        );
    }

    #[test]
    fn defaults_settle_the_type_parameters_that_no_argument_does() {
        let src = "\
struct Head:
    id: i32
struct Named:
    id: i32
    name: array(u8)
let first = &Named(id: 7, name: \"a\")
fn(T: Head) id(x: &T = first) -> i32:
    return x.id
fn(T) pick(a: T, b: T = 2) -> T:
    return b
fn(T) twice(x: T) -> i32:
    return id() * 2
fn f(h: &Head) -> i32:
    return id() + id(h) + pick(1) + pick(1 as i32, 3) + twice(true)
";
        let module = lower(src);
        assert_eq!(
            body(&module, "f"),
            "(return (I32.Add (I32.Add (I32.Add (I32.Add (call id(Named) 4) (call id(Head) h)) \
             (call pick(i32) 1 2)) (call pick(i32) 1 3)) (call twice(bool) 1)))"
        );
        assert_eq!(
            body(&module, "twice(bool)"),
            "(return (I32.Mul (call id(Named) 4) 2))"
        );

        use TypeErrorKind::*;
        let src = "\
struct Head:
    id: i32
struct Other:
    x: f32
let other = &Other(x: 1.0)
fn(T: Head) bad(x: &T = other):
    pass
fn(T) worse(x: &T = 1.5):
    pass
fn(T) pick(a: T, b: T = 2) -> T:
    return b
fn f():
    pick(true)
    pick(1, true)
";
        let default_mismatch = DefaultMismatch {
            param: "b".into(),
            expected: "bool".into(),
            found: "i32".into(),
        };
        assert_eq!(
            errors(src),
            vec![
                BoundNotMet {
                    ty: "Other".into(),
                    bound: "Head".into()
                },
                mismatch("&T", "f64"),
                default_mismatch.clone(),
                mismatch("bool", "i32"),
            ]
        );
        assert_eq!(
            default_mismatch.to_string(),
            "the default of `b` is a `i32`, where a `bool` is needed here: give `b` a value"
        );
    }

    #[test]
    fn a_use_gives_a_struct_the_fields_of_another() {
        use TypeErrorKind::*;
        let decls = "\
struct Head:
    id: i32
    tag: u8 = 7
struct Named:
    use Head
    len: u8
struct Last:
    len: u8
    use Head
fn(T: Head) id(x: &T) -> i32:
    return x.id
";
        let src = format!(
            "{decls}\
fn f(n: &Named) -> i32:
    let m = Named(id: 1, len: 2)
    let h = n as &Head
    return n.id + m.tag as i32 + id(n) + h.id
fn size() -> uint:
    return Named.size + Last.size
"
        );
        let module = lower(&src);
        assert_eq!(
            body(&module, "f"),
            "(set m.id 1) (set m.tag 7) (set m.len 2) (set h n) \
             (return (I32.Add (I32.Add (I32.Add (I32.Load offset=0 n) m.tag) \
             (call id(Named) n)) (I32.Load offset=0 h)))"
        );
        // The fields are its own, laid out where the `use` is: no `Head` is
        // within either.
        assert_eq!(body(&module, "size"), "(return (I32.Add 8 12))");

        // Only a struct that starts with them starts as `Head` does, and
        // neither is a `Head`.
        let src = format!(
            "{decls}\
fn g(l: &Last, n: Named) -> i32:
    let h: Head = n
    return id(l)
"
        );
        assert_eq!(
            errors(&src),
            vec![
                mismatch("Head", "Named"),
                BoundNotMet {
                    ty: "Last".into(),
                    bound: "Head".into()
                },
            ]
        );
    }

    #[test]
    fn used_fields_take_the_type_arguments_of_the_use() {
        let decls = "\
struct(T) Box:
    value: T
struct(T) Pair:
    use Box(T)
    other: T
struct Ints:
    first: u8
    use Pair(i64)
struct(N) Link:
    next: &N
struct Node:
    val: i32
    next: &Node
struct DNode:
    use Node
    prev: &DNode
struct Chain:
    use Link(Chain)
";
        let src = format!(
            "{decls}\
fn f(p: Pair(u8), i: Ints, d: &DNode, c: &Chain) -> i64:
    let n: &Node = d.next
    let m: &Chain = c.next
    return p.value as i64 + i.value + i.other
fn size() -> uint:
    return Ints.size + Pair(u8).size
"
        );
        let module = lower(&src);
        assert_eq!(
            body(&module, "f"),
            "(set n (I32.Load offset=4 d)) (set m (I32.Load offset=0 c)) \
             (return (I64.Add (I64.Add (I32.ExtendU p.value) i.value) i.other))"
        );
        assert_eq!(body(&module, "size"), "(return (I32.Add 24 2))");

        // A used field has the type it was declared with, which names the
        // struct it was declared in.
        let src = format!("{decls}fn g(d: &DNode):\n    let n: &DNode = d.next\n");
        assert_eq!(errors(&src), vec![mismatch("&DNode", "&Node")]);
    }

    #[test]
    fn used_fields_keep_their_defaults() {
        use TypeErrorKind::*;
        let decls = "\
struct(T) Slot:
    value: T = SEVEN
    p: &T = 0
let SEVEN = 7
struct A:
    use Slot(i32)
struct(T) W:
    use Slot(T)
    last: u8 = 1
struct B:
    use Slot(u8)
";
        let src = format!(
            "{decls}\
fn f() -> i32:
    let a = A()
    let w = W(i32)()
    let v = W(u8)(value: 2)
    let b = B(value: 3)
    return a.value + w.value
"
        );
        assert_eq!(
            body(&lower(&src), "f"),
            "(set a.value 7) (set a.p 0) (set w.value 7) (set w.p 0) (set w.last 1) \
             (set v.value 2) (set v.p 0) (set v.last 1) (set b.value 3) (set b.p 0) \
             (return (I32.Add a.value w.value))"
        );

        // A default is one value, of one type, wherever its field is used.
        let src = format!("{decls}fn g():\n    let b = B()\n    let w = W(u8)()\n");
        let default_mismatch = DefaultMismatch {
            param: "value".into(),
            expected: "u8".into(),
            found: "i32".into(),
        };
        assert_eq!(
            errors_at(&src),
            vec![
                (default_mismatch.clone(), "B()"),
                (default_mismatch, "W(u8)()"),
            ]
        );
    }

    #[test]
    fn a_use_gives_a_union_the_variants_of_another() {
        let src = "\
union ReadError:
    closed
    timeout: u32
union IoError:
    use ReadError
    denied
union(T) Maybe:
    unknown
    use option(T)
fn f(r: ReadError) -> i32:
    match r as IoError:
        .closed:
            return 1
        .timeout(ms):
            return ms as i32
        .denied:
            return 3
fn g(m: Maybe(i32)) -> i32:
    match m:
        .unknown:
            return -1
        .none:
            return 0
        .some(x):
            return x
fn h() -> Maybe(u8):
    return .some(4)
";
        let module = lower(src);
        // `none` is the second variant of `Maybe`, and `some` the third.
        assert_eq!(body(&module, "h"), "(return 2 4)");
        assert_eq!(
            body(&module, "g"),
            "(set tmp2 m) (set x m.0) (block \
             (if (I32.Eq tmp2 0) (then (return -1)) (else )) \
             (if (I32.Eq tmp2 1) (then (return 0)) (else )) \
             (if (I32.Eq tmp2 2) (then (return x)) (else )) unreachable) unreachable"
        );
        // A `ReadError` is the variant of `IoError` that it is of its own.
        assert_eq!(
            body(&module, "f"),
            "(set tmp2 r) (set ms r.0) (block \
             (if (I32.Eq tmp2 0) (then (return 1)) (else )) \
             (if (I32.Eq tmp2 1) (then (return ms)) (else )) \
             (if (I32.Eq tmp2 2) (then (return 3)) (else )) unreachable) unreachable"
        );
    }

    #[test]
    fn used_members_count_up_where_they_are_used() {
        let src = "\
enum(u8) A:
    x
    y = FIVE
    z
let FIVE: u8 = 5
enum(u8) B:
    p
    q
    use A
    r
enum(u8) Wide:
    use A
    w
enum(u8) Wider:
    use Wide
enum(tuple(u8, bool)) Pairs:
    one = (1, true)
enum(tuple(u8, bool)) More:
    zero = (0, false)
    use Pairs
fn b() -> tuple(u8, u8, u8, u8, u8, u8):
    return (B.p as u8, B.q as u8, B.x as u8, B.y as u8, B.z as u8, B.r as u8)
fn wide(a: A) -> tuple(Wider, u8):
    return (a as Wide as Wider, Wider.w as u8)
fn more() -> tuple(u8, bool):
    return More.one as tuple(u8, bool)
fn count() -> i32:
    var n = 0
    for m in More:
        n += 1
    return n
";
        let module = lower(src);
        // A member given a value keeps it, and one given none counts up from
        // the member before it where the `use` is.
        assert_eq!(body(&module, "b"), "(return 0 1 2 5 6 7)");
        // An enum that starts with a `use` is wider than what it uses.
        assert_eq!(body(&module, "wide"), "(return a 7)");
        assert_eq!(body(&module, "more"), "(return 1 1)");
        assert_eq!(body(&module, "count").matches("(set n ").count(), 3);

        let src = format!("{src}fn narrow(b: B) -> A:\n    return b as A\n");
        assert_eq!(
            errors(&src),
            vec![TypeErrorKind::InvalidCast {
                from: "B".into(),
                to: "A".into()
            }]
        );
    }

    #[test]
    fn a_use_names_a_type_of_the_kind_it_is_in() {
        use TypeErrorKind::*;
        let src = "\
struct S:
    x: i32
union U:
    a
enum(u8) E:
    m
enum(u16) F:
    n
struct(T) G:
    use T
    use U
    use E
    use array(u8)
    use tuple(i32, i32)
    use &S
    use Missing
    use G
union V:
    use S
    use E
    use option
enum(u8) H:
    use S
    use F
    use i32
";
        let other = |within: &'static str, ty: &str| UseOfOther {
            within,
            ty: ty.into(),
        };
        let values = UseOfValues {
            name: "F".into(),
            expected: "u8".into(),
            found: "u16".into(),
        };
        assert_eq!(
            errors_at(src),
            vec![
                (other("an enum", "S"), "S"),
                (values.clone(), "F"),
                (other("an enum", "i32"), "i32"),
                (other("a struct", "T"), "T"),
                (other("a struct", "U"), "U"),
                (other("a struct", "E"), "E"),
                (other("a struct", "array(u8)"), "array(u8)"),
                (other("a struct", "tuple(i32, i32)"), "tuple(i32, i32)"),
                (other("a struct", "&S"), "&S"),
                (UnknownType("Missing".into()), "Missing"),
                (MissingTypeArgs("G".into()), "G"),
                (other("a union", "S"), "S"),
                (other("a union", "E"), "E"),
                (MissingTypeArgs("option".into()), "option"),
            ]
        );
        assert_eq!(
            other("a union", "S").to_string(),
            "`use` in a union takes a union, which `S` isn't"
        );
        assert_eq!(
            values.to_string(),
            "`use` in an enum of `u8` takes one, and `F` is an enum of `u16`"
        );
    }

    #[test]
    fn used_names_are_not_repeated() {
        use TypeErrorKind::*;
        let src = "\
struct A:
    x: i32
    y: i32
struct B:
    y: u8
    use A
    x: u8
    use A
struct L:
    use A
struct R:
    use A
struct D:
    use L
    use R
union P:
    a
    b: i32
union Q:
    use P
    a: u8
    use P
enum(u8) M:
    a
    b
enum(u8) N:
    b
    use M
    a
fn f(b: B, n: N) -> tuple(u8, i32, u8):
    return (b.y, b.x, n as u8)
";
        let field = |name: &str| DuplicateField(name.into());
        let variant = |name: &str| DuplicateVariant(name.into());
        let member = |name: &str| DuplicateMember(name.into());
        // Whichever is written later is the one repeated, and is no field,
        // variant or member.
        assert_eq!(
            errors_at(src),
            vec![
                (member("b"), "M"),
                (field("y"), "A"),
                (field("x"), "x"),
                (field("x"), "A"),
                (field("y"), "A"),
                (field("x"), "R"),
                (field("y"), "R"),
                (variant("a"), "a"),
                (variant("a"), "P"),
                (variant("b"), "P"),
                (member("a"), "a"),
            ]
        );
    }

    #[test]
    fn a_use_never_leads_back_to_itself() {
        use TypeErrorKind::*;
        let src = "\
struct A:
    use B
    a: i32
struct B:
    use C
    b: i32
struct C:
    use A
    c: i32
struct S:
    use S
struct(T) G:
    use G(&T)
union U:
    use V
union V:
    use U
    v
enum(u8) E:
    use F
    e
enum(u8) F:
    use E
    f
fn f(a: A, b: B, c: C, u: U) -> i32:
    match u:
        .v:
            return a.a + a.b + a.c + b.b + b.c + c.c + E.f as i32 + E.e as i32
";
        let recursive = |ty: &str| RecursiveUse(ty.into());
        // Each is reported once, at the `use` that leads back, which gives
        // no fields: the others give what is left.
        assert_eq!(
            errors_at(src),
            vec![
                (recursive("E"), "E"),
                (recursive("A"), "A"),
                (recursive("S"), "S"),
                (recursive("G(&T)"), "G(&T)"),
                (recursive("U"), "U"),
            ]
        );
        assert_eq!(
            recursive("A").to_string(),
            "`use` of `A` leads back to itself"
        );
    }

    #[test]
    fn errors_in_used_fields_are_reported_at_the_use() {
        use TypeErrorKind::*;
        let src = "\
struct(T) Box:
    value: T
struct A:
    use Box(A)
struct Ext:
    p: &externref
struct Copy:
    use Ext
struct(T) Ptr:
    p: &T
struct E:
    use Ptr(externref)
struct(T) Open:
    use Ptr(tuple(T, externref))
struct Hidden:
    x: i32
struct Inner:
    pub h: Hidden
    i: Hidden
pub struct Outer:
    use Inner
pub union Sum:
    use option(Hidden)
struct(T: Hidden) Bounded:
    x: T
struct Unmet:
    use Bounded(Inner)
enum(u8) Top:
    a = 254
    b
enum(u8) Tail:
    t
    u
enum(u8) Over:
    use Top
    use Tail
enum(u8) Same:
    z = 254
    use Top
";
        let private = |item: &str| PrivateInPublic {
            ty: "Hidden".into(),
            item: item.into(),
        };
        let unstorable = || NotStorable("externref".into());
        assert_eq!(
            errors_at(src),
            vec![
                (private("h"), "Inner"),
                (private("some"), "option(Hidden)"),
                (RecursiveStruct("A".into()), "Box(A)"),
                // Reported once: where it is declared, or where the type
                // arguments that make it so are given.
                (unstorable(), "p: &externref"),
                (
                    NotStorable("tuple(T, externref)".into()),
                    "Ptr(tuple(T, externref))"
                ),
                (unstorable(), "Ptr(externref)"),
                (
                    BoundNotMet {
                        ty: "Inner".into(),
                        bound: "Hidden".into()
                    },
                    "Bounded(Inner)"
                ),
                (
                    MemberOutOfRange {
                        member: "t".into(),
                        ty: "u8".into()
                    },
                    "Tail"
                ),
                (
                    DuplicateValue {
                        member: "a".into(),
                        same_as: "z".into()
                    },
                    "Top"
                ),
            ]
        );

        let variants = |name: &str, count: usize| -> String {
            let variants = (0..count).map(|i| format!("    {name}{i}\n"));
            variants.collect()
        };
        let src = format!(
            "union Half:\n{}union Rest:\n{}union Both:\n    use Half\n    use Rest\n",
            variants("a", 128),
            variants("b", 129)
        );
        assert_eq!(
            errors_at(&src),
            vec![(TooManyVariants("Both".into()), "Rest")]
        );
    }

    #[test]
    fn used_constants_are_not_used_in_their_own_definition() {
        use TypeErrorKind::*;
        let src = "\
struct A:
    x: i32 = B().x
struct B:
    use A
enum(u8) E:
    a = F.b as u8
enum(u8) F:
    use E
    b
";
        assert_eq!(
            errors_at(src),
            vec![
                (RecursiveConstant("A".into()), "A"),
                (RecursiveConstant("E".into()), "E"),
            ]
        );
    }

    #[test]
    fn as_casts_a_value_to_what_it_is() {
        let src = "\
struct Head:
    id: i32
    tag: u8
struct Named:
    use Head
    len: u8
    wide: i64
enum(Named) Names:
    one = Named(id: 1, tag: 2, len: 3, wide: 4)
extern:
    fn make() -> Named
let first = Named(id: 5, tag: 6, len: 7, wide: 8) as Head
fn up(n: Named) -> Head:
    return n as Head
fn made() -> Head:
    return make() as Head
fn name() -> Head:
    return Names.one as Head
fn ptrs(n: &var Named, m: &Named) -> tuple(&var Head, &Head, &Head, uint):
    return (n as &var Head, n as &Head, m as &Head, m as uint)
fn(T: Head) bound(x: T, p: &T) -> i32:
    return (x as Head).id + (p as &Head).id + first.id
fn call(n: Named, p: &Named) -> i32:
    return bound(n, p)
";
        let module = lower(src);
        // A struct is one that it starts as: its first fields.
        assert_eq!(body(&module, "up"), "(return n.id n.tag)");
        assert_eq!(body(&module, "name"), "(return 1 2)");
        // What it leaves out is still evaluated.
        assert_eq!(
            body(&module, "made"),
            "(call make [] -> [tmp0 tmp1 tmp2 tmp3]) (return tmp0 (I32.And tmp1 255))"
        );
        // A pointer to it is one to what it starts as, and writes it if it
        // wrote the whole.
        assert_eq!(body(&module, "ptrs"), "(return n n m m)");
        // A type parameter is what bounds it.
        assert_eq!(
            body(&module, "bound(Named)"),
            "(return (I32.Add (I32.Add x.id (I32.Load offset=0 p)) 5))"
        );
    }

    #[test]
    fn as_unchecked_casts_an_address_to_any_other() {
        use TypeErrorKind::*;
        let decls = "\
struct Head:
    id: i32
struct Named:
    use Head
    len: u8
struct Last:
    len: u8
    use Head
union Narrow:
    a
union Wide:
    use Narrow
    b
enum(u8) Warm:
    red
enum(u8) Color:
    use Warm
    blue
";
        let params = "h: Head, p: &Head, n: &Named, l: &Last, a: uint, g: fn(), s: array(u8), u: &Narrow, w: &Warm";
        let src = format!(
            "{decls}\
fn f({params}):
    let a1 = p as! &Named
    let a2 = n as! &var Head
    let a3 = l as! &Head
    let a4 = a as! &Head
    let a5 = a as! fn()
    let a6 = g as! fn(i32)
    let a7 = s as! varray(u8)
    let a8 = 0 as! &Head
    let a9 = u as! &Wide
    let b1 = w as! &Color
    let b2 = n as! &Head
"
        );
        // The value is as it was: nothing is checked, or done.
        assert_eq!(
            body(&lower(&src), "f"),
            "(set a1 p) (set a2 n) (set a3 l) (set a4 a) (set a5 a) (set a6 g) \
             (set a7.ptr s.ptr) (set a7.len s.len) (set a8 0) (set a9 u) (set b1 w) (set b2 n)"
        );

        let src = format!(
            "{decls}\
fn f({params}):
    let a0 = h as Named
    let a1 = p as &Named
    let a2 = n as &var Head
    let a3 = l as &Head
    let a4 = a as &Head
    let a5 = a as fn()
    let a6 = g as fn(i32)
    let a7 = s as varray(u8)
    let a8 = 0 as &Head
    let a9 = u as &Wide
    let b1 = w as &Color
    let c1 = n as! Head
    let c2 = a as! u8
    let c3 = h as! Named
    let c4 = p as! uint
    let c5 = 1.5 as! &Head
    let c6 = a as u32 as! &Head
    let c7 = s as! array(u16)
"
        );
        let cast = |from: &str, to: &str| InvalidCast {
            from: from.into(),
            to: to.into(),
        };
        let unchecked = |from: &str, to: &str| UncheckedCast {
            from: from.into(),
            to: to.into(),
        };
        let value = |from: &str, to: &str| UncheckedValue {
            from: from.into(),
            to: to.into(),
        };
        assert_eq!(
            errors_at(&src),
            vec![
                // No value is one of a type that has more than it does.
                (cast("Head", "Named"), "h as Named"),
                // Nothing says what is at an address, or that it is written.
                (unchecked("&Head", "&Named"), "p as &Named"),
                (unchecked("&Named", "&var Head"), "n as &var Head"),
                (unchecked("&Last", "&Head"), "l as &Head"),
                (unchecked("uint", "&Head"), "a as &Head"),
                (unchecked("uint", "fn()"), "a as fn()"),
                (unchecked("fn()", "fn(i32)"), "g as fn(i32)"),
                (unchecked("array(u8)", "varray(u8)"), "s as varray(u8)"),
                (unchecked("uint", "&Head"), "0 as &Head"),
                // A wider union or enum is another value, not the same one.
                (unchecked("&Narrow", "&Wide"), "u as &Wide"),
                (unchecked("&Warm", "&Color"), "w as &Color"),
                // Only an address is cast without a check.
                (value("&Named", "Head"), "n as! Head"),
                (value("uint", "u8"), "a as! u8"),
                (value("Head", "Named"), "h as! Named"),
                (value("&Head", "uint"), "p as! uint"),
                (cast("f64", "&Head"), "1.5 as! &Head"),
                (
                    AddressCast {
                        from: "u32".into(),
                        to: "&Head".into()
                    },
                    "a as u32 as! &Head"
                ),
                (cast("array(u8)", "array(u16)"), "s as! array(u16)"),
            ]
        );
        assert_eq!(
            unchecked("uint", "&Head").to_string(),
            "casting `uint` as `&Head` is unchecked: write `as!`"
        );
        assert_eq!(
            value("uint", "u8").to_string(),
            "`as!` casts an address as another, or an integer and a float of one width \
             as each other, and `uint` as `u8` is neither"
        );
    }

    #[test]
    fn as_unchecked_gives_a_number_the_bits_of_another() {
        use TypeErrorKind::*;
        let src = "\
let one = 0x3f800000 as! f32
let nan = 0xfff8000000000000 as! f64
let bits = 1.0 as! u64
fn f(a: i32, b: u32, c: i64, d: u64, x: f32, y: f64) -> tuple(f32, f32, f64, f64):
    return (a as! f32, b as! f32, c as! f64, d as! f64)
fn g(x: f32, y: f64) -> tuple(i32, u32, i64, u64):
    return (x as! i32, x as! u32, y as! i64, y as! u64)
fn consts() -> tuple(f32, u64, f64, i32):
    return (one, bits, 1 as! f64, (2.5 as f32) as! i32)
fn round(x: f32) -> f32:
    return x as! u32 as! f32
";
        let module = lower(src);
        // The bits are as they were, where `as` gives the nearest value.
        assert_eq!(
            body(&module, "f"),
            "(return (I32.Reinterpret a) (I32.Reinterpret b) \
             (I64.Reinterpret c) (I64.Reinterpret d))"
        );
        assert_eq!(
            body(&module, "g"),
            "(return (F32.Reinterpret x) (F32.Reinterpret x) \
             (F64.Reinterpret y) (F64.Reinterpret y))"
        );
        assert_eq!(
            body(&module, "round"),
            "(return (I32.Reinterpret (F32.Reinterpret x)))"
        );
        // A literal is as wide as the float it is cast to, and a constant
        // is cast when it is folded.
        assert_eq!(
            body(&module, "consts"),
            "(return 1f32 4607182418800017408i64 (I64.Reinterpret 1i64) \
             (F32.Reinterpret (F64.Demote 2.5f64)))"
        );

        let src = "\
fn f(a: u8, b: uint, c: i32, x: f32, y: f64, t: bool):
    let a1 = a as! f32
    let a2 = b as! f32
    let a3 = c as! f64
    let a4 = x as! u64
    let a5 = x as! f64
    let a6 = y as! int
    let a7 = t as! f32
    let a8 = 1.5 as! f32
    let a9 = c as! u32
";
        let value = |from: &str, to: &str| UncheckedValue {
            from: from.into(),
            to: to.into(),
        };
        // Only an integer and a float of one width share their bits: any
        // other number is converted, by `as`.
        assert_eq!(
            errors_at(src),
            vec![
                (value("u8", "f32"), "a as! f32"),
                (value("uint", "f32"), "b as! f32"),
                (value("i32", "f64"), "c as! f64"),
                (value("f32", "u64"), "x as! u64"),
                (value("f32", "f64"), "x as! f64"),
                (value("f64", "int"), "y as! int"),
                (value("bool", "f32"), "t as! f32"),
                (value("f64", "f32"), "1.5 as! f32"),
                (value("i32", "u32"), "c as! u32"),
            ]
        );
    }
}

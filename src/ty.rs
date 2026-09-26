//! Name resolution, type checking, and lowering to [`crate::ir`].
//!
//! All three happen in one walk over each function body. Signatures are
//! collected first so items can be used before they are declared.

use std::collections::HashMap;
use std::fmt;
use std::mem;
use std::ops::Range;

use crate::ir::{
    self, BinOp as IrBinOp, Const, Expr, FuncId, GlobalId, LocalId, Stmt, UnOp as IrUnOp, ValType,
};
use crate::lex::Span;
use crate::parse::{self, Arg, BinOp, ExprKind, ItemKind, Mutability, StmtKind, TypeKind, UnaryOp};

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Ty {
    Prim(Prim),
    Struct(StructId),
    /// The type of functions without a return type.
    Unit,
    /// The type of an expression that already failed to check. Compatible
    /// with everything, so one mistake is reported once.
    Error,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeError {
    pub kind: TypeErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeErrorKind {
    UnknownName(String),
    UnknownType(String),
    /// A function or struct used as a value.
    NotAValue(String),
    NotCallable(String),
    DuplicateItem(String),
    DuplicateField(String),
    DuplicateParam(String),
    /// A struct that contains itself by value.
    RecursiveStruct(String),
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
    /// A global initializer that can't be evaluated at compile time.
    NotConstant,
    /// A global initializer that traps, such as dividing by zero.
    ConstTrap,
    Unsupported(&'static str),
}

#[derive(Default)]
struct Checker {
    items: HashMap<String, Item>,
    structs: Vec<StructDef>,
    funcs: Vec<FuncSig>,
    /// `None` until the global's initializer has been checked.
    globals: Vec<Option<GlobalDef>>,
    ir_globals: Vec<ir::Global>,
    errors: Vec<TypeError>,
}

#[derive(Debug, Clone, Copy)]
enum Item {
    Func(FuncId),
    Struct(StructId),
    Global(usize),
}

struct StructDef {
    name: String,
    fields: Vec<FieldDef>,
}

struct FieldDef {
    name: String,
    ty: Ty,
    /// Recorded for when modules can see each other's fields; not enforced.
    #[allow(dead_code)]
    is_pub: bool,
    span: Span,
}

#[derive(Clone)]
struct FuncSig {
    name: String,
    params: Vec<(String, Ty)>,
    ret: Ty,
}

struct GlobalDef {
    ty: Ty,
    mutable: bool,
    /// One wasm global per scalar leaf of `ty`.
    slots: Vec<GlobalId>,
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

/// A variable, or a field of one, that can be assigned.
struct Place {
    name: String,
    ty: Ty,
    mutable: bool,
    slots: Slots,
}

enum Slots {
    Local(Vec<LocalId>),
    Global(Vec<GlobalId>),
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
            Self::RecursiveStruct(name) => write!(f, "struct `{name}` contains itself"),
            Self::Mismatch { expected, found } => {
                write!(f, "expected `{expected}`, found `{found}`")
            }
            Self::InvalidOperand { op, ty } => write!(f, "`{op}` can't be applied to `{ty}`"),
            Self::InvalidCast { from, to } => write!(f, "can't cast `{from}` as `{to}`"),
            Self::IntOutOfRange(ty) => write!(f, "literal out of range for `{ty}`"),
            Self::NoField { ty, field } => write!(f, "`{ty}` has no field `{field}`"),
            Self::NotAssignable => write!(f, "invalid assignment target"),
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
            Self::NotConstant => write!(f, "global initializers must be constant"),
            Self::ConstTrap => write!(f, "constant evaluation traps"),
            Self::Unsupported(what) => write!(f, "{what} are not supported yet"),
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}..{}", self.kind, self.span.start, self.span.end)
    }
}

impl std::error::Error for TypeError {}

/// Resolves names in, type checks, and lowers a parsed module.
///
/// Checking continues past errors, so every error in the module is reported
/// at once.
pub fn check(module: &parse::Module) -> Result<ir::Module, Vec<TypeError>> {
    let mut ck = Checker::default();
    ck.declare(module);
    ck.define_structs(module);
    ck.define_funcs(module);
    ck.define_globals(module);
    let funcs = ck.lower_funcs(module);
    if ck.errors.is_empty() {
        Ok(ir::Module {
            globals: ck.ir_globals,
            funcs,
        })
    } else {
        Err(ck.errors)
    }
}

impl Checker {
    fn error(&mut self, kind: TypeErrorKind, span: Span) {
        self.errors.push(TypeError { kind, span });
    }

    /// Registers every item's name, so bodies can refer to later items.
    fn declare(&mut self, module: &parse::Module) {
        for item in &module.items {
            let (name, entry) = match &item.kind {
                ItemKind::Struct(s) => {
                    let id = StructId(self.structs.len() as u32);
                    self.structs.push(StructDef {
                        name: s.name.name.clone(),
                        fields: Vec::new(),
                    });
                    (&s.name, Item::Struct(id))
                }
                ItemKind::Fn(f) => {
                    let id = FuncId(self.funcs.len() as u32);
                    self.funcs.push(FuncSig {
                        name: f.name.name.clone(),
                        params: Vec::new(),
                        ret: Ty::Unit,
                    });
                    (&f.name, Item::Func(id))
                }
                ItemKind::Binding(b) => {
                    self.globals.push(None);
                    (&b.name, Item::Global(self.globals.len() - 1))
                }
            };
            if self.items.contains_key(&name.name) {
                self.error(TypeErrorKind::DuplicateItem(name.name.clone()), name.span);
            } else {
                self.items.insert(name.name.clone(), entry);
            }
        }
    }

    fn define_structs(&mut self, module: &parse::Module) {
        let decls = module.items.iter().filter_map(|item| match &item.kind {
            ItemKind::Struct(s) => Some(s),
            _ => None,
        });
        for (id, decl) in decls.enumerate() {
            let mut fields: Vec<FieldDef> = Vec::new();
            for field in &decl.fields {
                let ty = self.resolve_ty(&field.ty);
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
            self.structs[id].fields = fields;
        }
        let mut visits = vec![Visit::New; self.structs.len()];
        for id in 0..self.structs.len() {
            self.break_cycles(id, &mut visits);
        }
    }

    /// Reports structs that contain themselves by value, and cuts each cycle
    /// by giving the offending field the error type.
    fn break_cycles(&mut self, id: usize, visits: &mut [Visit]) {
        if visits[id] != Visit::New {
            return;
        }
        visits[id] = Visit::Active;
        for i in 0..self.structs[id].fields.len() {
            let Ty::Struct(StructId(child)) = self.structs[id].fields[i].ty else {
                continue;
            };
            let child = child as usize;
            match visits[child] {
                Visit::Active => {
                    let kind = TypeErrorKind::RecursiveStruct(self.structs[id].name.clone());
                    self.error(kind, self.structs[id].fields[i].span);
                    self.structs[id].fields[i].ty = Ty::Error;
                }
                Visit::New => self.break_cycles(child, visits),
                Visit::Done => {}
            }
        }
        visits[id] = Visit::Done;
    }

    fn define_funcs(&mut self, module: &parse::Module) {
        let decls = module.items.iter().filter_map(|item| match &item.kind {
            ItemKind::Fn(f) => Some(f),
            _ => None,
        });
        for (id, decl) in decls.enumerate() {
            let mut params: Vec<(String, Ty)> = Vec::new();
            for param in &decl.params {
                if params.iter().any(|(name, _)| *name == param.name.name) {
                    let kind = TypeErrorKind::DuplicateParam(param.name.name.clone());
                    self.error(kind, param.name.span);
                }
                params.push((param.name.name.clone(), self.resolve_ty(&param.ty)));
            }
            self.funcs[id].params = params;
            self.funcs[id].ret = decl.ret.as_ref().map_or(Ty::Unit, |ty| self.resolve_ty(ty));
        }
    }

    /// Checks and folds global initializers in declaration order.
    fn define_globals(&mut self, module: &parse::Module) {
        let decls = module.items.iter().filter_map(|item| match &item.kind {
            ItemKind::Binding(b) => Some(b),
            _ => None,
        });
        for (index, decl) in decls.enumerate() {
            let (ty, value) = Body::new(self, Ty::Unit).binding_value(decl);
            let mutable = decl.mutability == Mutability::Var;
            let mut inits = Vec::new();
            if value.pre.is_empty() {
                for (_, scalar) in &value.scalars {
                    match self.fold(scalar) {
                        Ok(c) => inits.push(c),
                        Err(fold) => {
                            let kind = match fold {
                                Fold::NotConstant => TypeErrorKind::NotConstant,
                                Fold::Trap => TypeErrorKind::ConstTrap,
                            };
                            self.error(kind, decl.value.span);
                            break;
                        }
                    }
                }
            } else {
                self.error(TypeErrorKind::NotConstant, decl.value.span);
            }
            let mut slots = Vec::new();
            let leaves = self.leaves(ty, &decl.name.name);
            for (i, (name, vt)) in leaves.into_iter().enumerate() {
                slots.push(GlobalId(self.ir_globals.len() as u32));
                self.ir_globals.push(ir::Global {
                    name,
                    ty: vt,
                    mutable,
                    init: inits.get(i).copied().unwrap_or(zero(vt)),
                });
            }
            self.globals[index] = Some(GlobalDef { ty, mutable, slots });
        }
    }

    fn lower_funcs(&mut self, module: &parse::Module) -> Vec<ir::Func> {
        let decls = module.items.iter().filter_map(|item| match &item.kind {
            ItemKind::Fn(f) => Some((item, f)),
            _ => None,
        });
        let mut funcs = Vec::new();
        for (id, (item, decl)) in decls.enumerate() {
            let sig = self.funcs[id].clone();
            let mut body = Body::new(self, sig.ret);
            for (name, ty) in &sig.params {
                let slots = body.alloc(name, *ty);
                body.bind(name, *ty, false, slots);
            }
            let params = body.locals.iter().map(|local| local.ty).collect();
            let mut stmts = body.block(&decl.body);
            let locals = body.locals;
            let results = self.val_types(sig.ret);
            if !matches!(sig.ret, Ty::Unit | Ty::Error) && !diverges(&decl.body) {
                self.error(TypeErrorKind::MissingReturn(sig.name.clone()), item.span);
            }
            // Wasm validates the end of a function with results as reachable
            // unless it follows a `return`.
            if !results.is_empty() && !matches!(stmts.last(), Some(Stmt::Return(_))) {
                stmts.push(Stmt::Unreachable);
            }
            funcs.push(ir::Func {
                export: item.is_pub.then(|| sig.name.clone()),
                name: sig.name,
                params,
                results,
                locals,
                body: stmts,
            });
        }
        funcs
    }

    fn resolve_ty(&mut self, ty: &parse::Type) -> Ty {
        match &ty.kind {
            TypeKind::Named(name) => {
                if let Some(prim) = Prim::from_name(name) {
                    Ty::Prim(prim)
                } else if let Some(Item::Struct(id)) = self.items.get(name) {
                    Ty::Struct(*id)
                } else {
                    self.error(TypeErrorKind::UnknownType(name.clone()), ty.span);
                    Ty::Error
                }
            }
            TypeKind::Array(_) => {
                self.error(TypeErrorKind::Unsupported("arrays"), ty.span);
                Ty::Error
            }
        }
    }

    fn ty_name(&self, ty: Ty) -> String {
        match ty {
            Ty::Prim(prim) => prim.name().to_string(),
            Ty::Struct(id) => self.structs[id.0 as usize].name.clone(),
            Ty::Unit => "()".to_string(),
            Ty::Error => "{error}".to_string(),
        }
    }

    /// The scalar leaves of `ty` in field order, each named `prefix` followed
    /// by its `.field` path.
    fn leaves(&self, ty: Ty, prefix: &str) -> Vec<(String, ValType)> {
        let mut out = Vec::new();
        self.push_leaves(ty, prefix.to_string(), &mut out);
        out
    }

    fn push_leaves(&self, ty: Ty, name: String, out: &mut Vec<(String, ValType)>) {
        match ty {
            Ty::Prim(prim) => out.push((name, prim.val_type())),
            Ty::Struct(id) => {
                for field in &self.structs[id.0 as usize].fields {
                    self.push_leaves(field.ty, format!("{name}.{}", field.name), out);
                }
            }
            Ty::Unit | Ty::Error => {}
        }
    }

    fn val_types(&self, ty: Ty) -> Vec<ValType> {
        self.leaves(ty, "").into_iter().map(|(_, vt)| vt).collect()
    }

    /// The type of `field` in `ty`, and the range of `ty`'s leaves it covers.
    /// `None` after reporting an error.
    fn field(&mut self, ty: Ty, field: &parse::Ident) -> Option<(Ty, Range<usize>)> {
        if let Ty::Struct(id) = ty {
            let mut start = 0;
            for def in &self.structs[id.0 as usize].fields {
                let len = self.val_types(def.ty).len();
                if def.name == field.name {
                    return Some((def.ty, start..start + len));
                }
                start += len;
            }
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
            Expr::Local(_) | Expr::Call(..) | Expr::Seq(..) => Err(Fold::NotConstant),
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
                let slots = self.alloc(&binding.name.name, ty);
                out.extend(value.pre);
                for (slot, (_, scalar)) in slots.iter().zip(value.scalars) {
                    out.push(Stmt::SetLocal(*slot, scalar));
                }
                let mutable = binding.mutability == Mutability::Var;
                self.bind(&binding.name.name, ty, mutable, slots);
            }
            StmtKind::Assign { target, op, value } => {
                let Some(place) = self.place(target) else {
                    self.expr(value, None);
                    return;
                };
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
                self.assign(&place.slots, value, out);
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
                self.labels.push(Label::Break);
                inner.extend(self.labelled(Label::Continue, body));
                self.labels.pop();
                inner.push(Stmt::Br(0));
                out.push(Stmt::Block(vec![Stmt::Loop(inner)]));
            }
            StmtKind::For { .. } => self.error(TypeErrorKind::Unsupported("for loops"), stmt.span),
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
                        slots: Slots::Local(var.slots.clone()),
                    });
                }
                match self.ck.items.get(name).copied() {
                    Some(Item::Global(index)) => {
                        let global = self.ck.globals[index].as_ref()?;
                        Some(Place {
                            name: name.clone(),
                            ty: global.ty,
                            mutable: global.mutable,
                            slots: Slots::Global(global.slots.clone()),
                        })
                    }
                    Some(Item::Func(_) | Item::Struct(_)) => {
                        self.error(TypeErrorKind::NotAssignable, target.span);
                        None
                    }
                    None => {
                        self.error(TypeErrorKind::UnknownName(name.clone()), target.span);
                        None
                    }
                }
            }
            ExprKind::Field(inner, field) => {
                let place = self.place(inner)?;
                let (ty, range) = self.ck.field(place.ty, field)?;
                let slots = match place.slots {
                    Slots::Local(slots) => Slots::Local(slots[range].to_vec()),
                    Slots::Global(slots) => Slots::Global(slots[range].to_vec()),
                };
                Some(Place { ty, slots, ..place })
            }
            ExprKind::Index(..) => {
                self.error(TypeErrorKind::Unsupported("arrays"), target.span);
                None
            }
            _ => {
                self.error(TypeErrorKind::NotAssignable, target.span);
                None
            }
        }
    }

    fn read_place(&self, place: &Place) -> Value {
        let reads = match &place.slots {
            Slots::Local(slots) => slots.iter().map(|l| Expr::Local(*l)).collect(),
            Slots::Global(slots) => slots.iter().map(|g| Expr::Global(*g)).collect(),
        };
        self.scalars(place.ty, reads)
    }

    fn assign(&mut self, slots: &Slots, mut value: Value, out: &mut Vec<Stmt>) {
        // Every scalar is read before any slot is written, so `p = Point(x:
        // p.y, y: p.x)` swaps.
        if value.scalars.len() > 1 {
            self.spill(&mut value, |e| matches!(e, Expr::Const(_)));
        }
        out.extend(value.pre);
        let scalars = exprs(value.scalars);
        match slots {
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
            ExprKind::Str(_) => self.unsupported("strings", expr.span),
            ExprKind::List(_) | ExprKind::Index(..) => self.unsupported("arrays", expr.span),
            ExprKind::Name(name) => self.name(name, expr.span),
            ExprKind::Unary(op, operand) => self.unary(*op, operand, expected, expr.span),
            ExprKind::Binary(op, lhs, rhs) => self.binary(*op, lhs, rhs, expected, expr.span),
            ExprKind::Call(callee, args) => self.call(callee, args, expr.span),
            ExprKind::Field(inner, field) => {
                let (ty, value) = self.expr(inner, None);
                match self.ck.field(ty, field) {
                    Some((ty, range)) => (ty, self.project(value, range)),
                    None => (Ty::Error, Value::default()),
                }
            }
            ExprKind::Cast(inner, ty) => self.cast(inner, ty, expr.span),
        }
    }

    fn unsupported(&mut self, what: &'static str, span: Span) -> (Ty, Value) {
        self.error(TypeErrorKind::Unsupported(what), span);
        (Ty::Error, Value::default())
    }

    /// An integer literal, typed by `expected` and defaulting to `i32`.
    fn int_literal(&mut self, n: i128, expected: Option<Ty>, span: Span) -> (Ty, Value) {
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
        match self.ck.items.get(name).copied() {
            Some(Item::Global(index)) => match &self.ck.globals[index] {
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
            Some(Item::Func(_) | Item::Struct(_)) => {
                self.error(TypeErrorKind::NotAValue(name.to_string()), span);
                (Ty::Error, Value::default())
            }
            None => {
                self.error(TypeErrorKind::UnknownName(name.to_string()), span);
                (Ty::Error, Value::default())
            }
        }
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
                if let Some(Ty::Prim(prim)) = expected
                    && prim.is_int()
                    && !prim.is_signed()
                {
                    return self.invalid_operand("-", Ty::Prim(prim), span);
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
        let Ty::Prim(prim) = ty else {
            return self.invalid_operand(binop_symbol(op), ty, span);
        };
        let bool = Ty::Prim(Prim::Bool);
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
        let (from, value) = self.expr(operand, None);
        match (from, to) {
            (Ty::Error, _) | (_, Ty::Error) => (Ty::Error, Value::default()),
            (Ty::Prim(from), Ty::Prim(to)) if convertible(from, to) => (
                Ty::Prim(to),
                map1(value, to.val_type(), |e| convert(from, to, e)),
            ),
            _ => {
                let kind = TypeErrorKind::InvalidCast {
                    from: self.ck.ty_name(from),
                    to: self.ck.ty_name(to),
                };
                self.error(kind, span);
                (Ty::Error, Value::default())
            }
        }
    }

    fn call(&mut self, callee: &parse::Expr, args: &[Arg], span: Span) -> (Ty, Value) {
        let item = match &callee.kind {
            ExprKind::Name(name) if self.lookup(name).is_some() => {
                Err(TypeErrorKind::NotCallable(name.clone()))
            }
            ExprKind::Name(name) => match self.ck.items.get(name).copied() {
                Some(Item::Func(id)) => Ok(Item::Func(id)),
                Some(Item::Struct(id)) => Ok(Item::Struct(id)),
                Some(Item::Global(_)) => Err(TypeErrorKind::NotCallable(name.clone())),
                None => Err(TypeErrorKind::UnknownName(name.clone())),
            },
            _ => Err(TypeErrorKind::NotCallable("expression".to_string())),
        };
        match item {
            Ok(Item::Func(id)) => {
                let sig = self.ck.funcs[id.0 as usize].clone();
                let value = self.args(&sig.params, args, false, span);
                let results = self.ck.val_types(sig.ret);
                let mut pre = value.pre;
                let args = exprs(value.scalars);
                let scalars = if let [result] = results[..] {
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
                (sig.ret, Value { pre, scalars })
            }
            Ok(Item::Struct(id)) => {
                let fields = self.ck.structs[id.0 as usize]
                    .fields
                    .iter()
                    .map(|f| (f.name.clone(), f.ty))
                    .collect::<Vec<_>>();
                (Ty::Struct(id), self.args(&fields, args, true, span))
            }
            Ok(Item::Global(_)) | Err(_) => {
                if let Err(kind) = item {
                    self.error(kind, callee.span);
                }
                for arg in args {
                    self.expr(&arg.value, None);
                }
                (Ty::Error, Value::default())
            }
        }
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
        let mut values = Vec::new();
        // Parameter index and scalar count of each value.
        let mut groups = Vec::new();
        for (arg, param) in args.iter().zip(binding) {
            match param {
                Some(i) => {
                    let value = self.check(&arg.value, params[i].1);
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

fn zero(ty: ValType) -> Const {
    match ty {
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

/// Whether `from as to` is allowed: any numeric conversion, and `bool` to an
/// integer.
fn convertible(from: Prim, to: Prim) -> bool {
    from == to || (from.is_numeric() && to.is_numeric()) || (from == Prim::Bool && to.is_int())
}

/// Lowers `expr as to`. Float to integer conversions saturate.
fn convert(from: Prim, to: Prim, expr: Expr) -> Expr {
    let (fvt, tvt) = (from.val_type(), to.val_type());
    let unary = |op, e| Expr::Unary(fvt, op, Box::new(e));
    if from == to {
        return expr;
    }
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
        Expr::Unary(_, _, x) => is_pure(x),
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
/// it may be evaluated later than written. Calls can change globals but not
/// the caller's locals.
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
        Expr::Global(_) | Expr::Call(..) | Expr::Seq(..) => false,
    }
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
    use crate::file::{DummyManager, FileManager};
    use crate::ir::{Const, Expr, Func, Module, Stmt, ValType};
    use crate::lex::tokenize;

    fn check_src(src: &str) -> Result<Module, Vec<TypeError>> {
        let tokens = tokenize(DummyManager::entry_point(), src).unwrap();
        check(&parse::parse(&tokens).unwrap())
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
            Stmt::Drop(v) => format!("(drop {})", e(v)),
            Stmt::Call { func, args, dests } => {
                let dests: Vec<_> = dests.iter().map(|d| local(f, *d)).collect();
                let name = &m.funcs[func.0 as usize].name;
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
            Expr::Binary(ty, op, a, b) => format!("({ty:?}.{op:?} {} {})", ex(a), ex(b)),
            Expr::Call(func, args) => {
                let args: Vec<_> = args.iter().map(ex).collect();
                format!(
                    "(call {} {})",
                    m.funcs[func.0 as usize].name,
                    args.join(" ")
                )
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
        let globals: Vec<_> = module
            .globals
            .iter()
            .map(|g| (g.name.as_str(), g.mutable, g.init))
            .collect();
        assert_eq!(
            globals,
            vec![
                ("global", false, Const::I32(1)),
                ("counter", true, Const::I32(0))
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
    let e = p == p
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
                invalid_operand("==", "P"),
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
                mismatch("i32", "()"),
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
    let l: [i32] = a
";
        assert_eq!(
            errors(src),
            vec![
                ImmutableAssign("a".into()),
                ImmutableAssign("b".into()),
                BreakOutsideLoop,
                ContinueOutsideLoop,
                Unsupported("for loops"),
                Unsupported("strings"),
                Unsupported("arrays"),
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
        assert_eq!(inits, vec!["1f32", "2f32", "1f32"]);
    }
}

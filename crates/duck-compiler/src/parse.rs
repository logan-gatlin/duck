use std::fmt;
use std::mem;

use crate::lex::{Span, Token, TokenKind};

/// A parsed source file, or the items of a whole program once
/// [`crate::load`] has gathered every file it uses.
#[derive(Debug, Clone, PartialEq)]
pub struct Module {
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Item {
    pub is_pub: bool,
    pub kind: ItemKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ItemKind {
    Fn(FnDecl),
    Extern(ExternBlock),
    Struct(StructDecl),
    Enum(EnumDecl),
    Union(UnionDecl),
    Binding(Binding),
    /// Resolved by [`crate::load`], so later stages never see one.
    Use(Use),
}

/// `use a.b` or `use a.{b, c}`, binding what each path names.
#[derive(Debug, Clone, PartialEq)]
pub struct Use {
    /// One for `use a.b`, and one for each name a group ends in.
    pub paths: Vec<UsePath>,
}

/// `a.b.c`, binding the module or item it names to its last name, unless
/// `as alias` renames it.
#[derive(Debug, Clone, PartialEq)]
pub struct UsePath {
    /// The names from the root of the package, the first of which may be a
    /// dependency instead. Those before a group are repeated in each of its
    /// paths.
    pub segments: Vec<Ident>,
    pub alias: Option<Ident>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub sig: FnSig,
    pub body: Block,
    /// The interface of the `pub "interface":` block the function is in,
    /// which exports it, as it is written there: with its quotes. Each
    /// function of a block is an item of its own.
    pub interface: Option<Ident>,
    /// The `= "name"` after the signature, which the function is exported
    /// as in place of its own name, as it is written.
    pub export_name: Option<Ident>,
}

/// `fn(A, B) name(params) -> ret`, shared by definitions and imports. The
/// type parameters are optional.
#[derive(Debug, Clone, PartialEq)]
pub struct FnSig {
    /// The type parameters that a call infers from its arguments.
    pub type_params: Vec<TypeParam>,
    pub name: Ident,
    /// A parameter of type `type` is a type parameter that a call gives a
    /// type.
    pub params: Vec<Param>,
    pub ret: Option<Type>,
}

/// A type parameter in the `(A, B: Bound, C = Default)` after `struct`,
/// `union` or `fn`.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeParam {
    pub name: Ident,
    /// The types its type arguments use, first and in order: one for
    /// `: Bound`, each of a list `: (A, B)`, and none if it isn't bounded.
    pub bound: Vec<Type>,
    /// The type it is where a list of type arguments gives it none.
    pub default: Option<Type>,
}

/// `extern "module":` and the host functions it imports. The module name is
/// optional.
#[derive(Debug, Clone, PartialEq)]
pub struct ExternBlock {
    /// The module as it is written: with its quotes.
    pub module: Option<Ident>,
    pub fns: Vec<ExternFn>,
}

/// A bodyless `fn` in an `extern` block, optionally followed by `= "name"` to
/// import it under a different name, and optionally marked `pub` so other
/// modules can call it.
#[derive(Debug, Clone, PartialEq)]
pub struct ExternFn {
    pub is_pub: bool,
    pub sig: FnSig,
    pub import_name: Option<String>,
    pub span: Span,
}

/// A `name: Type` or `name: Type = default` function parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Type,
    /// The value the parameter has where a call gives it none.
    pub default: Option<Expr>,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDecl {
    pub name: Ident,
    /// `struct(A, B) Name`'s type parameters, if it has any.
    pub params: Vec<TypeParam>,
    pub entries: Vec<Entry<Field>>,
}

/// A line of the body of a struct, a union or an enum.
#[derive(Debug, Clone, PartialEq)]
pub enum Entry<T> {
    /// A field, variant or member of the declaration's own.
    Own(T),
    /// `use Type`: those of another struct, union or enum, in its place.
    /// Every one comes before the declaration's own.
    Use(Type),
}

/// A `name: Type` or `name: Type = default` struct field, optionally marked
/// `pub`.
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub is_pub: bool,
    pub name: Ident,
    pub ty: Type,
    /// The value the field has where a constructor gives it none.
    pub default: Option<Expr>,
    pub span: Span,
}

/// `enum(Type) Name:` and its members, whose values have type `Type`.
#[derive(Debug, Clone, PartialEq)]
pub struct EnumDecl {
    pub name: Ident,
    pub ty: Type,
    pub entries: Vec<Entry<Member>>,
}

/// A `name` or `name = value` member of an enum.
#[derive(Debug, Clone, PartialEq)]
pub struct Member {
    pub name: Ident,
    pub value: Option<Expr>,
    pub span: Span,
}

/// `union Name:` and its variants, one of which a value holds at a time.
#[derive(Debug, Clone, PartialEq)]
pub struct UnionDecl {
    pub name: Ident,
    /// `union(A, B) Name`'s type parameters, if it has any.
    pub params: Vec<TypeParam>,
    pub entries: Vec<Entry<Variant>>,
}

/// A `name` or `name: Type` variant of a union.
#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub name: Ident,
    /// The type of the value it holds, if it holds one.
    pub ty: Option<Type>,
    pub span: Span,
}

/// `let pattern: Type = value` or `var pattern: Type = value`. The type is
/// optional.
#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    pub mutability: Mutability,
    pub pattern: Pattern,
    pub ty: Option<Type>,
    pub value: Expr,
}

/// What a binding assigns its value to, or an arm of a `match` tests its
/// value against.
#[derive(Debug, Clone, PartialEq)]
pub struct Pattern {
    pub kind: PatternKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatternKind {
    Name(String),
    /// `_`, which binds nothing.
    Discard,
    /// `(a, b)`, which takes a tuple apart. `()` is the empty tuple.
    Tuple(Vec<Pattern>),
    /// `.name` or `.name(pattern)`: a variant of a union and what it holds,
    /// or a member of an enum. Only an arm of a `match` has one, or any of
    /// the patterns below, as a value can fail to match them.
    Variant(Ident, Option<Box<Pattern>>),
    /// A number, which may be negative, a string, `true` or `false`.
    Literal(Expr),
    /// `[a, b]`, which takes apart an array of as many elements.
    Array(Vec<Pattern>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    Let,
    Var,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Ident {
    pub name: String,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

/// A type argument, optionally labelled with the type parameter it is given
/// to, as in `Name(A, T: B)`.
#[derive(Debug, Clone, PartialEq)]
pub struct TypeArg {
    pub label: Option<Ident>,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    /// `Name`, or `Name(A, B)` given a list of type arguments, which may be
    /// empty as in `Name()`. `None` is no list at all.
    Named(String, Option<Vec<TypeArg>>),
    /// `&T`, or `&var T`, which can be written through.
    Pointer(Mutability, Box<Type>),
    /// `module.T`, a type in another module, where `T` is a name or itself
    /// qualified.
    Qualified(Ident, Box<Type>),
    /// `fn(A, B) -> R`, a pointer to a function. `None` is no result written.
    Fn(Vec<Type>, Option<Box<Type>>),
    /// `todo`, in place of a type yet to be written. Nothing but a `todo` is
    /// of it.
    Todo,
}

pub type Block = Vec<Stmt>;

#[derive(Debug, Clone, PartialEq)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
    Binding(Binding),
    Expr(Expr),
    /// `else if` is represented as an `else` block holding a single `If`.
    If {
        cond: Expr,
        then_body: Block,
        else_body: Option<Block>,
    },
    While {
        cond: Expr,
        body: Block,
    },
    For {
        var: Ident,
        iter: Expr,
        body: Block,
    },
    /// `match value:`, which runs the first of `arms` whose pattern the
    /// value matches.
    Match {
        value: Expr,
        arms: Vec<Arm>,
    },
    Pass,
    /// `defer expr`, whose block is that one expression, or `defer:` and a
    /// block. It runs when the block that the `defer` is in is left.
    Defer(Block),
}

/// `pattern:` and the block a `match` runs for a value that matches it.
/// `else:` is an arm whose pattern is `_`.
#[derive(Debug, Clone, PartialEq)]
pub struct Arm {
    pub pattern: Pattern,
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Int(u64),
    Float(f64),
    Str(String),
    Bool(bool),
    /// `()`
    Unit,
    Name(String),
    /// `module.name`, a property of the module being compiled.
    Module(Ident),
    /// `(a, b)`, with at least two elements.
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    /// `[value; len]`, an array of `len` copies of `value`.
    Repeat(Box<Expr>, Box<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Arg>),
    Index(Box<Expr>, Box<Expr>),
    Field(Box<Expr>, Ident),
    /// `pointer.*`
    Deref(Box<Expr>),
    /// `&place`, or `&var place`, which can be written through.
    AddrOf(Mutability, Box<Expr>),
    /// `value as Type`, or `value as! Type` if unchecked.
    Cast(Box<Expr>, Type, bool),
    /// `fn(A) -> R`, a function type written where a value belongs.
    FnType(Type),
    /// `value |> body`, which evaluates `value` once and then `body`, where
    /// each [`ExprKind::Placeholder`] stands for it.
    Pipe(Box<Expr>, Box<Expr>),
    /// `_`, the value piped into the nearest pipe whose body it's in.
    Placeholder,
    /// `.name`, a variant of the union or member of the enum expected of it.
    Dot(Ident),
    /// `target = value`, or `target op= value` when `op` is set. Its value is
    /// the one assigned.
    Assign {
        target: Box<Expr>,
        op: Option<BinOp>,
        value: Box<Expr>,
    },
    /// `return`, or `return value`, whose value is all that follows it. It
    /// has no value of its own, as the function is left where it is.
    Return(Option<Box<Expr>>),
    /// `break`, which has no value either: the loop is left where it is.
    Break,
    /// `continue`, which has none, as the loop goes on to its next
    /// iteration from where it is.
    Continue,
    /// `todo`, which has none, as it traps where it is: what is yet to be
    /// written is in its place.
    Todo,
}

/// A call argument, optionally labelled as in `f(name: value)`.
#[derive(Debug, Clone, PartialEq)]
pub struct Arg {
    pub label: Option<Ident>,
    pub value: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    BitNot,
    Not,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Or,
    And,
    Eq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    BitOr,
    BitXor,
    BitAnd,
    Shl,
    Shr,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Debug, Clone, PartialEq)]
pub struct ParseError {
    pub kind: ParseErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParseErrorKind {
    Expected {
        expected: String,
        found: TokenKind,
    },
    UnexpectedIndent,
    ChainedComparison,
    InvalidAssignTarget,
    /// A `fn` with no body outside an `extern` block.
    MissingFnBody,
    /// A `fn` with a body inside an `extern` block.
    ExternFnBody,
    /// `pub` on an `extern` block.
    PubExtern,
    /// A `use` after an item that isn't one.
    UseAfterItem,
    /// A `use` after a field, variant or member of the declaration's own.
    UseAfterEntry,
    /// A function in an `extern` block with type parameters.
    GenericExtern,
    /// A function in a `pub "interface":` block with type parameters.
    GenericExport,
    /// A pipe whose body has no `_` of its own.
    PipeWithoutPlaceholder,
    /// A `|>` after a `return` in the body of a pipe, outside any brackets
    /// in it: it would be in the value returned.
    PipeAfterReturn,
    /// `_` as an expression that isn't in the body of a pipe.
    PlaceholderOutsidePipe,
    /// A line starting with `|>` that isn't indented deeper than the
    /// statement above it, so it continues nothing.
    LeadingPipe,
    /// An arm of a `match` after its `else`.
    ArmAfterElse,
    /// A pattern that names a variant or member through its type, as in
    /// `Shape.circle`.
    QualifiedPattern,
}

type PResult<T> = Result<T, ParseError>;

struct Parser<'a> {
    /// Always ends with `Eof`.
    tokens: &'a [Token],
    pos: usize,
    /// End of the last consumed token, ignoring layout tokens so that spans
    /// don't stretch over trailing newlines and dedents.
    last_end: usize,
    errors: Vec<ParseError>,
    /// How many errors are in the line being parsed that skipping a line
    /// within it didn't leave out. A line with any is left out itself.
    flaws: usize,
    /// Whether each pipe body being parsed has had a placeholder yet,
    /// innermost last.
    placeholder_used: Vec<bool>,
    /// Whether what is being parsed is the body of a pipe, and in no
    /// brackets within it: a `return` there ends the chain of pipes.
    pipe_body: bool,
}

/// What a parenthesized list turned out to be.
enum Parens<T> {
    /// `()`
    Empty,
    /// `(x)`
    Group(T),
    /// `(x, y)`, or `(x,)`: a comma makes a tuple of even one.
    Tuple(Vec<T>),
}

/// Precedence of `not`, which sits between `and` and the comparisons.
const NOT_PREC: u8 = 3;
const CMP_PREC: u8 = 4;

impl<T> Entry<T> {
    /// The field, variant or member it is, unless it's a `use`.
    pub fn own(&self) -> Option<&T> {
        match self {
            Self::Own(own) => Some(own),
            Self::Use(_) => None,
        }
    }
}

impl FnSig {
    /// Whether it has a type parameter: one a call infers, or a parameter of
    /// type `type`.
    pub fn is_generic(&self) -> bool {
        !self.type_params.is_empty() || self.params.iter().any(|param| param.ty.is_type())
    }

    /// The names of its type parameters: those a call infers, then its
    /// parameters of type `type`.
    pub fn type_param_names(&self) -> Vec<Ident> {
        let inferred = self.type_params.iter().map(|param| &param.name);
        let given = self.params.iter().filter(|param| param.ty.is_type());
        inferred
            .chain(given.map(|param| &param.name))
            .cloned()
            .collect()
    }
}

impl Binding {
    /// Whether it is typed `type`, as one that names a type is: its value
    /// is that type, written as an expression.
    pub fn binds_type(&self) -> bool {
        self.ty.as_ref().is_some_and(Type::is_type)
    }
}

impl Type {
    /// Whether it is `type`, which makes a parameter a type parameter.
    pub fn is_type(&self) -> bool {
        matches!(&self.kind, TypeKind::Named(name, None) if name == "type")
    }
}

/// Displays the type argument as it is written.
impl fmt::Display for TypeArg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.label {
            Some(label) => write!(f, "{}: {}", label.name, self.ty),
            None => write!(f, "{}", self.ty),
        }
    }
}

/// Displays the type as it is written.
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn list<T: fmt::Display>(f: &mut fmt::Formatter<'_>, items: &[T]) -> fmt::Result {
            write!(f, "(")?;
            for (i, item) in items.iter().enumerate() {
                let comma = if i == 0 { "" } else { ", " };
                write!(f, "{comma}{item}")?;
            }
            write!(f, ")")
        }
        match &self.kind {
            TypeKind::Named(name, None) => write!(f, "{name}"),
            TypeKind::Named(name, Some(args)) => {
                write!(f, "{name}")?;
                list(f, args)
            }
            TypeKind::Pointer(Mutability::Let, pointee) => write!(f, "&{pointee}"),
            TypeKind::Pointer(Mutability::Var, pointee) => write!(f, "&var {pointee}"),
            TypeKind::Qualified(module, ty) => write!(f, "{}.{ty}", module.name),
            TypeKind::Fn(params, ret) => {
                write!(f, "fn")?;
                list(f, params)?;
                match ret {
                    Some(ret) => write!(f, " -> {ret}"),
                    None => Ok(()),
                }
            }
            TypeKind::Todo => write!(f, "todo"),
        }
    }
}

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expected { expected, found } => write!(f, "expected {expected}, found {found}"),
            Self::UnexpectedIndent => write!(f, "unexpected indentation"),
            Self::ChainedComparison => write!(f, "comparison operators cannot be chained"),
            Self::InvalidAssignTarget => write!(f, "invalid assignment target"),
            Self::MissingFnBody => write!(f, "functions outside `extern` blocks need a body"),
            Self::ExternFnBody => write!(f, "functions in `extern` blocks cannot have a body"),
            Self::PubExtern => write!(f, "`extern` blocks cannot be `pub`"),
            Self::UseAfterItem => write!(f, "`use` must come before other items"),
            Self::UseAfterEntry => write!(
                f,
                "`use` must come before the fields, variants or members of the declaration's own"
            ),
            Self::GenericExtern => {
                write!(
                    f,
                    "functions in `extern` blocks cannot have type parameters"
                )
            }
            Self::GenericExport => write!(
                f,
                "functions that an interface exports cannot have type parameters"
            ),
            Self::PipeWithoutPlaceholder => {
                write!(f, "the right side of `|>` must use `_`, e.g. `x |> f(_)`")
            }
            Self::PipeAfterReturn => write!(
                f,
                "a `return` on the right side of `|>` ends the chain: bracket its value to pipe \
                 within it, e.g. `x |> return (_ |> f(_))`"
            ),
            Self::PlaceholderOutsidePipe => {
                write!(f, "`_` can only be used on the right side of `|>`")
            }
            Self::LeadingPipe => write!(
                f,
                "a line starting with `|>` must be indented deeper than the statement it continues"
            ),
            Self::ArmAfterElse => write!(f, "`else` must be the last arm of a `match`"),
            Self::QualifiedPattern => write!(
                f,
                "a pattern names a variant or member without its type, as in `.name`"
            ),
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}..{}", self.kind, self.span.start, self.span.end)
    }
}

impl std::error::Error for ParseError {}

/// Parses the output of [`crate::lex::tokenize`] into a syntax tree.
///
/// Parsing continues past errors: a malformed line (and any block nested
/// under it) is skipped, so every error in the file is reported at once.
pub fn parse(tokens: &[Token]) -> Result<Module, Vec<ParseError>> {
    match parse_partial(tokens) {
        (module, errors) if errors.is_empty() => Ok(module),
        (_, errors) => Err(errors),
    }
}

/// Parses as [`parse`] does, and gives what parsed of a source with errors
/// along with them: every line but those an error is in, and the blocks
/// nested under those.
pub fn parse_partial(tokens: &[Token]) -> (Module, Vec<ParseError>) {
    let mut parser = Parser {
        tokens,
        pos: 0,
        last_end: 0,
        errors: Vec::new(),
        flaws: 0,
        placeholder_used: Vec::new(),
        pipe_body: false,
    };
    let module = parser.module();
    (module, parser.errors)
}

impl<'a> Parser<'a> {
    fn module(&mut self) -> Module {
        let mut items = Vec::new();
        let mut past_uses = false;
        while !self.at(TokenKind::Eof) {
            let flaws = self.flaws;
            if self.at(TokenKind::Pub) && matches!(self.peek_second().kind, TokenKind::Str(_)) {
                past_uses = true;
                match self.export_block() {
                    Ok(exported) if self.flaws == flaws => items.extend(exported),
                    Ok(_) => {}
                    Err(e) => self.recover(e),
                }
                self.flaws = flaws;
                continue;
            }
            match self.item() {
                Ok(item) => {
                    let is_use = matches!(item.kind, ItemKind::Use(_));
                    if past_uses && is_use {
                        self.error(ParseErrorKind::UseAfterItem, item.span);
                    }
                    past_uses |= !is_use;
                    if self.flaws == flaws {
                        items.push(item);
                    }
                }
                Err(e) => self.recover(e),
            }
            self.flaws = flaws;
        }
        Module { items }
    }

    /// `pub "interface":` and the functions it exports, each an item that
    /// says which interface it is of.
    fn export_block(&mut self) -> PResult<Vec<Item>> {
        self.expect(TokenKind::Pub)?;
        let interface = self.string_ident()?;
        let fns = self.indented(|p| {
            if p.eat(TokenKind::Pass) {
                p.expect(TokenKind::Newline)?;
                return Ok(None);
            }
            let start = p.peek().span;
            let is_pub = p.eat(TokenKind::Pub);
            let mut decl = p.fn_decl()?;
            let sig = &decl.sig;
            if let (Some(first), Some(last)) = (sig.type_params.first(), sig.type_params.last()) {
                let span = Span {
                    end: last.name.span.end,
                    ..first.name.span
                };
                p.error(ParseErrorKind::GenericExport, span);
            }
            for param in sig.params.iter().filter(|param| param.ty.is_type()) {
                p.error(ParseErrorKind::GenericExport, param.span);
            }
            decl.interface = Some(interface.clone());
            Ok(Some(Item {
                is_pub,
                kind: ItemKind::Fn(decl),
                span: p.span_from(start),
            }))
        })?;
        Ok(fns.into_iter().flatten().collect())
    }

    fn item(&mut self) -> PResult<Item> {
        let start = self.peek().span;
        let is_pub = self.eat(TokenKind::Pub);
        let kind = match self.peek().kind {
            TokenKind::Fn => ItemKind::Fn(self.fn_decl()?),
            TokenKind::Extern => {
                if is_pub {
                    self.error(ParseErrorKind::PubExtern, start);
                }
                ItemKind::Extern(self.extern_block()?)
            }
            TokenKind::Struct => ItemKind::Struct(self.struct_decl()?),
            TokenKind::Enum => ItemKind::Enum(self.enum_decl()?),
            TokenKind::Union => ItemKind::Union(self.union_decl()?),
            TokenKind::Let | TokenKind::Var => ItemKind::Binding(self.binding()?),
            TokenKind::Use => ItemKind::Use(self.use_decl()?),
            _ => return Err(self.unexpected("item")),
        };
        Ok(Item {
            is_pub,
            kind,
            span: self.span_from(start),
        })
    }

    fn use_decl(&mut self) -> PResult<Use> {
        self.expect(TokenKind::Use)?;
        let mut paths = Vec::new();
        self.use_tree(Vec::new(), &mut paths)?;
        self.expect(TokenKind::Newline)?;
        Ok(Use { paths })
    }

    /// The paths of `a.b`, `a.b as c` or `a.{b, c.d}`, each after `prefix`.
    fn use_tree(&mut self, prefix: Vec<Ident>, paths: &mut Vec<UsePath>) -> PResult<()> {
        let mut segments = prefix;
        segments.push(self.ident()?);
        while self.eat(TokenKind::Dot) {
            if self.eat(TokenKind::LBrace) {
                self.comma_list(TokenKind::RBrace, |parser| {
                    parser.use_tree(segments.clone(), paths)
                })?;
                return Ok(());
            }
            segments.push(self.ident()?);
        }
        let alias = match self.eat(TokenKind::As) {
            true => Some(self.ident()?),
            false => None,
        };
        paths.push(UsePath { segments, alias });
        Ok(())
    }

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        let start = self.peek().span;
        let sig = self.fn_sig()?;
        let export_name = match self.eat(TokenKind::Eq) {
            true => Some(self.string_ident()?),
            false => None,
        };
        if self.at(TokenKind::Newline) {
            return Err(self.error_from(ParseErrorKind::MissingFnBody, start));
        }
        let body = self.block()?;
        Ok(FnDecl {
            sig,
            body,
            interface: None,
            export_name,
        })
    }

    fn fn_sig(&mut self) -> PResult<FnSig> {
        self.expect(TokenKind::Fn)?;
        let type_params = self.type_params()?;
        let name = self.ident()?;
        self.expect(TokenKind::LParen)?;
        let params = self.comma_list(TokenKind::RParen, Self::param)?;
        let ret = if self.eat(TokenKind::Arrow) {
            Some(self.ty()?)
        } else {
            None
        };
        Ok(FnSig {
            type_params,
            name,
            params,
            ret,
        })
    }

    fn extern_block(&mut self) -> PResult<ExternBlock> {
        self.expect(TokenKind::Extern)?;
        let module = if matches!(self.peek().kind, TokenKind::Str(_)) {
            Some(self.string_ident()?)
        } else {
            None
        };
        let fns = self.indented(|p| {
            if p.eat(TokenKind::Pass) {
                p.expect(TokenKind::Newline)?;
                return Ok(None);
            }
            p.extern_fn().map(Some)
        })?;
        Ok(ExternBlock {
            module,
            fns: fns.into_iter().flatten().collect(),
        })
    }

    fn extern_fn(&mut self) -> PResult<ExternFn> {
        let start = self.peek().span;
        let is_pub = self.eat(TokenKind::Pub);
        let sig = self.fn_sig()?;
        if let (Some(first), Some(last)) = (sig.type_params.first(), sig.type_params.last()) {
            let span = Span {
                end: last.name.span.end,
                ..first.name.span
            };
            self.error(ParseErrorKind::GenericExtern, span);
        }
        for param in sig.params.iter().filter(|param| param.ty.is_type()) {
            self.error(ParseErrorKind::GenericExtern, param.span);
        }
        let import_name = if self.eat(TokenKind::Eq) {
            Some(self.string()?)
        } else {
            None
        };
        if self.at(TokenKind::Colon) {
            return Err(self.error_from(ParseErrorKind::ExternFnBody, start));
        }
        let span = self.span_from(start);
        self.expect(TokenKind::Newline)?;
        Ok(ExternFn {
            is_pub,
            sig,
            import_name,
            span,
        })
    }

    fn struct_decl(&mut self) -> PResult<StructDecl> {
        self.expect(TokenKind::Struct)?;
        let params = self.type_params()?;
        let name = self.ident()?;
        let mut past_uses = false;
        let entries = self.indented(|p| {
            if p.eat(TokenKind::Pass) {
                past_uses = true;
                p.expect(TokenKind::Newline)?;
                return Ok(None);
            }
            p.entry(&mut past_uses, Self::field).map(Some)
        })?;
        Ok(StructDecl {
            name,
            params,
            entries: entries.into_iter().flatten().collect(),
        })
    }

    /// A line of a struct's, a union's or an enum's body: `use Type`, or
    /// what `own` parses. `past_uses` is whether a line before it was the
    /// declaration's own, which a `use` is reported for coming after.
    fn entry<T>(
        &mut self,
        past_uses: &mut bool,
        own: impl FnOnce(&mut Self) -> PResult<T>,
    ) -> PResult<Entry<T>> {
        let start = self.peek().span;
        let entry = match self.eat(TokenKind::Use) {
            true => Entry::Use(self.ty()?),
            false => Entry::Own(own(self)?),
        };
        match entry {
            Entry::Use(_) if *past_uses => {
                let span = self.span_from(start);
                self.error(ParseErrorKind::UseAfterEntry, span);
            }
            Entry::Use(_) => {}
            Entry::Own(_) => *past_uses = true,
        }
        self.expect(TokenKind::Newline)?;
        Ok(entry)
    }

    /// The `(A, B: Bound, C = Default)` after `struct`, `union` or `fn` that
    /// makes a declaration generic, if there is one. A bound is a type, or
    /// a list of them in brackets, and a default is a type.
    fn type_params(&mut self) -> PResult<Vec<TypeParam>> {
        if !self.eat(TokenKind::LParen) {
            return Ok(Vec::new());
        }
        if self.at(TokenKind::RParen) {
            return Err(self.unexpected("type parameter"));
        }
        self.comma_list(TokenKind::RParen, |p| {
            let name = p.ident()?;
            let bound = match p.eat(TokenKind::Colon) {
                true if p.eat(TokenKind::LParen) => p.comma_list(TokenKind::RParen, Self::ty)?,
                true => vec![p.ty()?],
                false => Vec::new(),
            };
            let default = match p.eat(TokenKind::Eq) {
                true => Some(p.ty()?),
                false => None,
            };
            Ok(TypeParam {
                name,
                bound,
                default,
            })
        })
    }

    /// A type argument: a type, or `Param: Type`, which gives it to the
    /// type parameter so named.
    fn type_arg(&mut self) -> PResult<TypeArg> {
        let labelled = matches!(self.peek().kind, TokenKind::Ident(_))
            && self.peek_second().kind == TokenKind::Colon;
        let label = match labelled {
            true => {
                let label = self.ident()?;
                self.bump();
                Some(label)
            }
            false => None,
        };
        Ok(TypeArg {
            label,
            ty: self.ty()?,
        })
    }

    fn enum_decl(&mut self) -> PResult<EnumDecl> {
        self.expect(TokenKind::Enum)?;
        self.expect(TokenKind::LParen)?;
        let ty = self.ty()?;
        self.expect(TokenKind::RParen)?;
        let name = self.ident()?;
        let mut past_uses = false;
        let entries = self.indented(|p| p.entry(&mut past_uses, Self::member))?;
        Ok(EnumDecl { name, ty, entries })
    }

    fn member(&mut self) -> PResult<Member> {
        let start = self.peek().span;
        let name = self.ident()?;
        let value = match self.eat(TokenKind::Eq) {
            true => Some(self.expr()?),
            false => None,
        };
        let span = self.span_from(start);
        Ok(Member { name, value, span })
    }

    fn union_decl(&mut self) -> PResult<UnionDecl> {
        self.expect(TokenKind::Union)?;
        let params = self.type_params()?;
        let name = self.ident()?;
        let mut past_uses = false;
        let entries = self.indented(|p| p.entry(&mut past_uses, Self::variant))?;
        Ok(UnionDecl {
            name,
            params,
            entries,
        })
    }

    fn variant(&mut self) -> PResult<Variant> {
        let start = self.peek().span;
        let name = self.ident()?;
        let ty = match self.eat(TokenKind::Colon) {
            true => Some(self.ty()?),
            false => None,
        };
        let span = self.span_from(start);
        Ok(Variant { name, ty, span })
    }

    fn param(&mut self) -> PResult<Param> {
        let start = self.peek().span;
        let (name, ty) = self.typed_name()?;
        let default = self.default()?;
        Ok(Param {
            name,
            ty,
            default,
            span: self.span_from(start),
        })
    }

    fn field(&mut self) -> PResult<Field> {
        let start = self.peek().span;
        let is_pub = self.eat(TokenKind::Pub);
        let (name, ty) = self.typed_name()?;
        let default = self.default()?;
        Ok(Field {
            is_pub,
            name,
            ty,
            default,
            span: self.span_from(start),
        })
    }

    /// The `= default` after a parameter or field, if there is one.
    fn default(&mut self) -> PResult<Option<Expr>> {
        match self.eat(TokenKind::Eq) {
            true => self.expr().map(Some),
            false => Ok(None),
        }
    }

    /// `name: Type`
    fn typed_name(&mut self) -> PResult<(Ident, Type)> {
        let name = self.ident()?;
        self.expect(TokenKind::Colon)?;
        let ty = self.ty()?;
        Ok((name, ty))
    }

    fn binding(&mut self) -> PResult<Binding> {
        let kind = if self.eat(TokenKind::Let) {
            Mutability::Let
        } else {
            self.expect(TokenKind::Var)?;
            Mutability::Var
        };
        let pattern = self.pattern()?;
        let ty = if self.eat(TokenKind::Colon) {
            Some(self.ty()?)
        } else {
            None
        };
        self.expect(TokenKind::Eq)?;
        let value = self.expr()?;
        self.expect(TokenKind::Newline)?;
        Ok(Binding {
            mutability: kind,
            pattern,
            ty,
            value,
        })
    }

    fn pattern(&mut self) -> PResult<Pattern> {
        let token = self.peek();
        let kind = match &token.kind {
            TokenKind::Ident(name) => {
                self.bump();
                match name.as_str() {
                    "_" => PatternKind::Discard,
                    _ => PatternKind::Name(name.clone()),
                }
            }
            TokenKind::LParen => {
                self.bump();
                match self.parens(Self::pattern)? {
                    Parens::Empty => PatternKind::Tuple(Vec::new()),
                    Parens::Group(inner) => inner.kind,
                    Parens::Tuple(items) => PatternKind::Tuple(items),
                }
            }
            _ => return Err(self.unexpected("pattern")),
        };
        Ok(Pattern {
            kind,
            span: self.span_from(token.span),
        })
    }

    fn ty(&mut self) -> PResult<Type> {
        let token = self.peek();
        let kind = match &token.kind {
            TokenKind::Ident(_) if self.peek_second().kind == TokenKind::Dot => {
                let module = self.ident()?;
                self.bump();
                if !matches!(self.peek().kind, TokenKind::Ident(_)) {
                    return Err(self.unexpected("type name"));
                }
                TypeKind::Qualified(module, Box::new(self.ty()?))
            }
            TokenKind::Ident(name) => {
                self.bump();
                let args = match self.eat(TokenKind::LParen) {
                    true => Some(self.comma_list(TokenKind::RParen, Self::type_arg)?),
                    false => None,
                };
                TypeKind::Named(name.clone(), args)
            }
            TokenKind::Amp => {
                self.bump();
                let mutability = self.pointer_mutability();
                TypeKind::Pointer(mutability, Box::new(self.ty()?))
            }
            TokenKind::Fn => {
                self.bump();
                self.expect(TokenKind::LParen)?;
                let params = self.comma_list(TokenKind::RParen, Self::ty)?;
                let ret = match self.eat(TokenKind::Arrow) {
                    true => Some(Box::new(self.ty()?)),
                    false => None,
                };
                TypeKind::Fn(params, ret)
            }
            TokenKind::Todo => {
                self.bump();
                TypeKind::Todo
            }
            _ => return Err(self.unexpected("type")),
        };
        Ok(Type {
            kind,
            span: self.span_from(token.span),
        })
    }

    fn block(&mut self) -> PResult<Block> {
        self.indented(Self::stmt)
    }

    /// Parses `: NEWLINE INDENT line+ DEDENT`. Errors inside a line are
    /// recorded and the line is skipped.
    fn indented<T>(&mut self, mut line: impl FnMut(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        self.expect(TokenKind::Colon)?;
        self.expect(TokenKind::Newline)?;
        if !self.eat(TokenKind::Indent) {
            // Leave the next line alone; it likely belongs to the outer block.
            let error = self.unexpected("indented block");
            self.error(error.kind, error.span);
            return Ok(Vec::new());
        }
        let mut lines = Vec::new();
        while !self.eat(TokenKind::Dedent) && !self.at(TokenKind::Eof) {
            let flaws = self.flaws;
            match line(self) {
                Ok(l) if self.flaws == flaws => lines.push(l),
                Ok(_) => {}
                Err(e) => self.recover(e),
            }
            self.flaws = flaws;
        }
        Ok(lines)
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let start = self.peek().span;
        let kind = match self.peek().kind {
            TokenKind::Let | TokenKind::Var => StmtKind::Binding(self.binding()?),
            TokenKind::If => return self.if_stmt(),
            TokenKind::While => {
                self.bump();
                let cond = self.expr()?;
                let body = self.block()?;
                StmtKind::While { cond, body }
            }
            TokenKind::For => {
                self.bump();
                let var = self.ident()?;
                self.expect(TokenKind::In)?;
                let iter = self.expr()?;
                let body = self.block()?;
                StmtKind::For { var, iter, body }
            }
            TokenKind::Match => {
                self.bump();
                let value = self.expr()?;
                let arms = self.arms()?;
                StmtKind::Match { value, arms }
            }
            TokenKind::Pass => self.keyword_stmt(StmtKind::Pass)?,
            TokenKind::Defer => {
                self.bump();
                if self.at(TokenKind::Colon) {
                    StmtKind::Defer(self.block()?)
                } else {
                    let line = self.peek().span;
                    let expr = self.expr()?;
                    self.expect(TokenKind::Newline)?;
                    let span = self.span_from(line);
                    let kind = StmtKind::Expr(expr);
                    StmtKind::Defer(vec![Stmt { kind, span }])
                }
            }
            _ => {
                let expr = self.expr()?;
                self.expect(TokenKind::Newline)?;
                StmtKind::Expr(expr)
            }
        };
        Ok(Stmt {
            kind,
            span: self.span_from(start),
        })
    }

    fn if_stmt(&mut self) -> PResult<Stmt> {
        let start = self.expect(TokenKind::If)?.span;
        let cond = self.expr()?;
        let then_body = self.block()?;
        let else_body = if !self.eat(TokenKind::Else) {
            None
        } else if self.at(TokenKind::If) {
            Some(vec![self.if_stmt()?])
        } else {
            Some(self.block()?)
        };
        Ok(Stmt {
            kind: StmtKind::If {
                cond,
                then_body,
                else_body,
            },
            span: self.span_from(start),
        })
    }

    /// The arms of a `match`, after its value. Its `else`, if it has one,
    /// is the last.
    fn arms(&mut self) -> PResult<Vec<Arm>> {
        let mut else_seen = false;
        self.indented(|p| {
            let start = p.peek().span;
            let is_else = p.eat(TokenKind::Else);
            let pattern = match is_else {
                true => Pattern {
                    kind: PatternKind::Discard,
                    span: start,
                },
                false => p.arm_pattern()?,
            };
            if else_seen {
                return Err(p.error_from(ParseErrorKind::ArmAfterElse, start));
            }
            else_seen = is_else;
            let body = p.block()?;
            Ok(Arm { pattern, body })
        })
    }

    /// The pattern of an arm of a `match`, which can fail to match, as that
    /// of a binding can't.
    fn arm_pattern(&mut self) -> PResult<Pattern> {
        let token = self.peek();
        let kind = match &token.kind {
            TokenKind::Dot => {
                self.bump();
                let name = self.ident()?;
                let holds = match self.eat(TokenKind::LParen) {
                    true => {
                        let holds = self.arm_pattern()?;
                        self.expect(TokenKind::RParen)?;
                        Some(Box::new(holds))
                    }
                    false => None,
                };
                PatternKind::Variant(name, holds)
            }
            // `Shape.circle`, or `Option(i32).some`.
            TokenKind::Ident(_)
                if matches!(self.peek_second().kind, TokenKind::Dot | TokenKind::LParen) =>
            {
                self.bump();
                return Err(self.error_from(ParseErrorKind::QualifiedPattern, token.span));
            }
            TokenKind::Ident(_) => return self.pattern(),
            TokenKind::LParen => {
                self.bump();
                match self.parens(Self::arm_pattern)? {
                    Parens::Empty => PatternKind::Tuple(Vec::new()),
                    Parens::Group(inner) => inner.kind,
                    Parens::Tuple(items) => PatternKind::Tuple(items),
                }
            }
            TokenKind::LBracket => {
                self.bump();
                PatternKind::Array(self.comma_list(TokenKind::RBracket, Self::arm_pattern)?)
            }
            TokenKind::Minus
            | TokenKind::Int(_)
            | TokenKind::Float(_)
            | TokenKind::Str(_)
            | TokenKind::True
            | TokenKind::False => PatternKind::Literal(self.literal_pattern()?),
            _ => return Err(self.unexpected("pattern")),
        };
        Ok(Pattern {
            kind,
            span: self.span_from(token.span),
        })
    }

    /// A literal that a pattern is: a number, which may follow a `-`, a
    /// string, `true` or `false`.
    fn literal_pattern(&mut self) -> PResult<Expr> {
        let start = self.peek().span;
        let negative = self.eat(TokenKind::Minus);
        let token = self.peek();
        let kind = match &token.kind {
            TokenKind::Int(n) => ExprKind::Int(*n),
            TokenKind::Float(x) => ExprKind::Float(*x),
            _ if negative => return Err(self.unexpected("number")),
            TokenKind::Str(s) => ExprKind::Str(s.clone()),
            TokenKind::True => ExprKind::Bool(true),
            TokenKind::False => ExprKind::Bool(false),
            _ => return Err(self.unexpected("pattern")),
        };
        self.bump();
        let literal = Expr {
            kind,
            span: token.span,
        };
        Ok(match negative {
            true => Expr {
                kind: ExprKind::Unary(UnaryOp::Neg, Box::new(literal)),
                span: self.span_from(start),
            },
            false => literal,
        })
    }

    fn keyword_stmt(&mut self, kind: StmtKind) -> PResult<StmtKind> {
        self.bump();
        self.expect(TokenKind::Newline)?;
        Ok(kind)
    }

    /// An expression, which is an assignment if an assignment operator
    /// follows its first chain of pipes. Assignments bind looser than every
    /// other operator and group to the right.
    fn expr(&mut self) -> PResult<Expr> {
        let target = self.pipe()?;
        let op = match self.peek().kind {
            TokenKind::Eq => None,
            TokenKind::PlusEq => Some(BinOp::Add),
            TokenKind::MinusEq => Some(BinOp::Sub),
            TokenKind::StarEq => Some(BinOp::Mul),
            TokenKind::SlashEq => Some(BinOp::Div),
            TokenKind::PercentEq => Some(BinOp::Rem),
            _ => return Ok(target),
        };
        self.bump();
        if !matches!(
            target.kind,
            ExprKind::Name(_) | ExprKind::Field(..) | ExprKind::Index(..) | ExprKind::Deref(_)
        ) {
            self.error(ParseErrorKind::InvalidAssignTarget, target.span);
        }
        let value = self.expr()?;
        let span = self.span_from(target.span);
        Ok(Expr {
            kind: ExprKind::Assign {
                target: Box::new(target),
                op,
                value: Box::new(value),
            },
            span,
        })
    }

    /// A chain of pipes, which bind looser than every operator but
    /// assignment and group to the left.
    fn pipe(&mut self) -> PResult<Expr> {
        let mut expr = self.binary(0)?;
        while self.eat(TokenKind::PipeArrow) {
            self.placeholder_used.push(false);
            let outer = mem::replace(&mut self.pipe_body, true);
            let body = self.binary(0);
            self.pipe_body = outer;
            let used = self.placeholder_used.pop();
            let body = body?;
            if used == Some(false) {
                self.error(ParseErrorKind::PipeWithoutPlaceholder, body.span);
            }
            let span = self.span_from(expr.span);
            expr = Expr {
                kind: ExprKind::Pipe(Box::new(expr), Box::new(body)),
                span,
            };
        }
        Ok(expr)
    }

    /// Precedence climbing over the binary operators and `not`, parsing only
    /// operators that bind at least as tightly as `min_prec`.
    fn binary(&mut self, min_prec: u8) -> PResult<Expr> {
        let mut lhs = if min_prec <= NOT_PREC && self.at(TokenKind::Not) {
            let start = self.bump().span;
            let operand = self.binary(NOT_PREC)?;
            Expr {
                kind: ExprKind::Unary(UnaryOp::Not, Box::new(operand)),
                span: self.span_from(start),
            }
        } else {
            self.cast()?
        };
        while let Some((op, prec)) = binary_op(&self.peek().kind) {
            if prec < min_prec {
                break;
            }
            self.bump();
            let rhs = self.binary(prec + 1)?;
            let span = self.span_from(lhs.span);
            lhs = Expr {
                kind: ExprKind::Binary(op, Box::new(lhs), Box::new(rhs)),
                span,
            };
            if prec == CMP_PREC && binary_op(&self.peek().kind).is_some_and(|(_, p)| p == CMP_PREC)
            {
                self.error(ParseErrorKind::ChainedComparison, self.peek().span);
            }
        }
        Ok(lhs)
    }

    /// A unary expression followed by any `as Type` and `as! Type` casts,
    /// which bind tighter than binary operators but looser than unary ones.
    fn cast(&mut self) -> PResult<Expr> {
        let mut expr = self.unary()?;
        loop {
            let unchecked = self.eat(TokenKind::AsUnchecked);
            if !unchecked && !self.eat(TokenKind::As) {
                return Ok(expr);
            }
            let ty = self.ty()?;
            let span = self.span_from(expr.span);
            expr = Expr {
                kind: ExprKind::Cast(Box::new(expr), ty, unchecked),
                span,
            };
        }
    }

    fn unary(&mut self) -> PResult<Expr> {
        let op = match self.peek().kind {
            TokenKind::Minus => Some(UnaryOp::Neg),
            TokenKind::Tilde => Some(UnaryOp::BitNot),
            TokenKind::Amp => None,
            _ => return self.postfix(),
        };
        let start = self.bump().span;
        let kind = match op {
            Some(op) => ExprKind::Unary(op, Box::new(self.unary()?)),
            None => {
                let mutability = self.pointer_mutability();
                ExprKind::AddrOf(mutability, Box::new(self.unary()?))
            }
        };
        Ok(Expr {
            kind,
            span: self.span_from(start),
        })
    }

    /// The `var` of `&var`, if it's there, after the `&`.
    fn pointer_mutability(&mut self) -> Mutability {
        match self.eat(TokenKind::Var) {
            true => Mutability::Var,
            false => Mutability::Let,
        }
    }

    /// A primary expression followed by any calls, indexing, field access, or
    /// dereferences.
    fn postfix(&mut self) -> PResult<Expr> {
        let mut expr = self.primary()?;
        loop {
            let start = expr.span;
            let kind = match self.peek().kind {
                TokenKind::LParen => {
                    self.bump();
                    let args = self.bracketed(|p| p.comma_list(TokenKind::RParen, Self::arg))?;
                    ExprKind::Call(Box::new(expr), args)
                }
                TokenKind::LBracket => {
                    self.bump();
                    let index = self.bracketed(Self::expr)?;
                    self.expect(TokenKind::RBracket)?;
                    ExprKind::Index(Box::new(expr), Box::new(index))
                }
                TokenKind::Dot => {
                    self.bump();
                    let field = self.field_name()?;
                    ExprKind::Field(Box::new(expr), field)
                }
                TokenKind::DotStar => {
                    self.bump();
                    ExprKind::Deref(Box::new(expr))
                }
                _ => return Ok(expr),
            };
            expr = Expr {
                kind,
                span: self.span_from(start),
            };
        }
    }

    /// `value` or `label: value`
    fn arg(&mut self) -> PResult<Arg> {
        let labelled = matches!(self.peek().kind, TokenKind::Ident(_))
            && self.peek_second().kind == TokenKind::Colon;
        let label = if labelled {
            let label = self.ident()?;
            self.expect(TokenKind::Colon)?;
            Some(label)
        } else {
            None
        };
        let value = self.expr()?;
        Ok(Arg { label, value })
    }

    fn primary(&mut self) -> PResult<Expr> {
        let token = self.peek();
        let kind = match &token.kind {
            TokenKind::Int(n) => ExprKind::Int(*n),
            TokenKind::Float(x) => ExprKind::Float(*x),
            TokenKind::Str(s) => ExprKind::Str(s.clone()),
            TokenKind::True => ExprKind::Bool(true),
            TokenKind::False => ExprKind::Bool(false),
            TokenKind::Ident(name) if name == "_" => {
                match self.placeholder_used.last_mut() {
                    Some(used) => *used = true,
                    None => self.error(ParseErrorKind::PlaceholderOutsidePipe, token.span),
                }
                ExprKind::Placeholder
            }
            TokenKind::Ident(name) => ExprKind::Name(name.clone()),
            TokenKind::Break => ExprKind::Break,
            TokenKind::Continue => ExprKind::Continue,
            TokenKind::Todo => ExprKind::Todo,
            TokenKind::LParen => {
                self.bump();
                let kind = match self.bracketed(|p| p.parens(Self::expr))? {
                    Parens::Empty => ExprKind::Unit,
                    Parens::Group(inner) => inner.kind,
                    Parens::Tuple(items) => ExprKind::Tuple(items),
                };
                return Ok(Expr {
                    kind,
                    span: self.span_from(token.span),
                });
            }
            TokenKind::Module => {
                self.bump();
                self.expect(TokenKind::Dot)?;
                let name = self.ident()?;
                return Ok(Expr {
                    kind: ExprKind::Module(name),
                    span: self.span_from(token.span),
                });
            }
            TokenKind::Fn => {
                let ty = self.ty()?;
                return Ok(Expr {
                    span: ty.span,
                    kind: ExprKind::FnType(ty),
                });
            }
            TokenKind::LBracket => {
                self.bump();
                let kind = self.bracketed(Self::brackets)?;
                return Ok(Expr {
                    kind,
                    span: self.span_from(token.span),
                });
            }
            TokenKind::Dot => {
                self.bump();
                let name = self.ident()?;
                return Ok(Expr {
                    kind: ExprKind::Dot(name),
                    span: self.span_from(token.span),
                });
            }
            TokenKind::Return => {
                self.bump();
                // In the body of a pipe, a `|>` after its value would
                // read as the next of the chain, so it is no part of it.
                let value = match starts_expr(&self.peek().kind) {
                    true if self.pipe_body => Some(Box::new(self.binary(0)?)),
                    true => Some(Box::new(self.expr()?)),
                    false => None,
                };
                if self.pipe_body && self.at(TokenKind::PipeArrow) {
                    self.error(ParseErrorKind::PipeAfterReturn, self.peek().span);
                }
                return Ok(Expr {
                    kind: ExprKind::Return(value),
                    span: self.span_from(token.span),
                });
            }
            _ => return Err(self.unexpected("expression")),
        };
        self.bump();
        Ok(Expr {
            kind,
            span: token.span,
        })
    }

    /// Parses what brackets hold with `inner`: a pipe body that they are in
    /// is not what it is in.
    fn bracketed<T>(&mut self, inner: impl FnOnce(&mut Self) -> PResult<T>) -> PResult<T> {
        let outer = mem::take(&mut self.pipe_body);
        let result = inner(self);
        self.pipe_body = outer;
        result
    }

    /// Parses the rest of a parenthesized list after its `(`. A comma makes
    /// a tuple, of one item too.
    fn parens<T>(&mut self, mut item: impl FnMut(&mut Self) -> PResult<T>) -> PResult<Parens<T>> {
        if self.eat(TokenKind::RParen) {
            return Ok(Parens::Empty);
        }
        let first = item(self)?;
        if !self.eat(TokenKind::Comma) {
            self.expect(TokenKind::RParen)?;
            return Ok(Parens::Group(first));
        }
        let mut items = vec![first];
        items.extend(self.comma_list(TokenKind::RParen, &mut item)?);
        Ok(Parens::Tuple(items))
    }

    /// Parses the rest of an array literal after its `[`: a list of elements,
    /// or `value; len`.
    fn brackets(&mut self) -> PResult<ExprKind> {
        if self.eat(TokenKind::RBracket) {
            return Ok(ExprKind::List(Vec::new()));
        }
        let first = self.expr()?;
        if self.eat(TokenKind::Semi) {
            let len = self.expr()?;
            self.expect(TokenKind::RBracket)?;
            return Ok(ExprKind::Repeat(Box::new(first), Box::new(len)));
        }
        let mut items = vec![first];
        if self.eat(TokenKind::Comma) {
            items.extend(self.comma_list(TokenKind::RBracket, Self::expr)?);
        } else {
            self.expect(TokenKind::RBracket)?;
        }
        Ok(ExprKind::List(items))
    }

    /// Parses `item, item, ... close` after the opening bracket. A trailing
    /// comma is allowed.
    fn comma_list<T>(
        &mut self,
        close: TokenKind,
        mut item: impl FnMut(&mut Self) -> PResult<T>,
    ) -> PResult<Vec<T>> {
        let mut items = Vec::new();
        while !self.eat(close.clone()) {
            items.push(item(self)?);
            if !self.eat(TokenKind::Comma) {
                self.expect(close)?;
                break;
            }
        }
        Ok(items)
    }

    fn string(&mut self) -> PResult<String> {
        match &self.peek().kind {
            TokenKind::Str(value) => {
                self.bump();
                Ok(value.clone())
            }
            _ => Err(self.unexpected("string")),
        }
    }

    /// A string and where it is written, quotes and all.
    fn string_ident(&mut self) -> PResult<Ident> {
        let span = self.peek().span;
        let name = self.string()?;
        Ok(Ident { name, span })
    }

    fn ident(&mut self) -> PResult<Ident> {
        let token = self.peek();
        match &token.kind {
            TokenKind::Ident(name) => {
                self.bump();
                Ok(Ident {
                    name: name.clone(),
                    span: token.span,
                })
            }
            _ => Err(self.unexpected("identifier")),
        }
    }

    /// The name after a `.`: a struct field, or the index of a tuple element.
    fn field_name(&mut self) -> PResult<Ident> {
        let token = self.peek();
        match &token.kind {
            TokenKind::Int(index) => {
                self.bump();
                Ok(Ident {
                    name: index.to_string(),
                    span: token.span,
                })
            }
            _ => self.ident(),
        }
    }

    /// Records `error`, then skips the rest of the current line, any block
    /// nested under it, and any `else` clauses that follow.
    fn recover(&mut self, error: ParseError) {
        self.errors.push(error);
        loop {
            if !self.at(TokenKind::Indent) {
                while !self.at(TokenKind::Eof) {
                    if self.bump().kind == TokenKind::Newline {
                        break;
                    }
                }
            }
            if self.at(TokenKind::Indent) {
                self.skip_block();
            }
            if !self.at(TokenKind::Else) {
                break;
            }
        }
    }

    /// Skips from an `Indent` through its matching `Dedent`.
    fn skip_block(&mut self) {
        let mut depth = 0usize;
        loop {
            match self.bump().kind {
                TokenKind::Indent => depth += 1,
                TokenKind::Dedent => {
                    depth -= 1;
                    if depth == 0 {
                        return;
                    }
                }
                TokenKind::Eof => return,
                _ => {}
            }
        }
    }

    fn peek(&self) -> &'a Token {
        &self.tokens[self.pos]
    }

    /// The token after [`Self::peek`], or `Eof` at the end.
    fn peek_second(&self) -> &'a Token {
        &self.tokens[(self.pos + 1).min(self.tokens.len() - 1)]
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.peek().kind == kind
    }

    /// Whether [`Self::peek`] is the first token of its line.
    fn at_line_start(&self) -> bool {
        self.pos.checked_sub(1).is_none_or(|prev| {
            matches!(
                self.tokens[prev].kind,
                TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent
            )
        })
    }

    fn bump(&mut self) -> &'a Token {
        let token = self.peek();
        if token.kind != TokenKind::Eof {
            self.pos += 1;
        }
        if !matches!(
            token.kind,
            TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent | TokenKind::Eof
        ) {
            self.last_end = token.span.end;
        }
        token
    }

    fn eat(&mut self, kind: TokenKind) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: TokenKind) -> PResult<&'a Token> {
        if self.at(kind.clone()) {
            Ok(self.bump())
        } else {
            Err(self.unexpected(kind.to_string()))
        }
    }

    fn unexpected(&self, expected: impl Into<String>) -> ParseError {
        let token = self.peek();
        let kind = match token.kind {
            TokenKind::Indent => ParseErrorKind::UnexpectedIndent,
            TokenKind::PipeArrow if self.at_line_start() => ParseErrorKind::LeadingPipe,
            _ => ParseErrorKind::Expected {
                expected: expected.into(),
                found: token.kind.clone(),
            },
        };
        ParseError {
            kind,
            span: token.span,
        }
    }

    /// Records an error that doesn't stop the current line from parsing,
    /// though the line is left out of what [`parse_partial`] gives.
    fn error(&mut self, kind: ParseErrorKind, span: Span) {
        self.errors.push(ParseError { kind, span });
        self.flaws += 1;
    }

    /// An error spanning from `start` to the end of the last consumed token.
    fn error_from(&self, kind: ParseErrorKind, start: Span) -> ParseError {
        ParseError {
            kind,
            span: self.span_from(start),
        }
    }

    /// Span from the start of `start` to the end of the last consumed token.
    fn span_from(&self, start: Span) -> Span {
        Span {
            file: start.file,
            start: start.start,
            end: self.last_end,
        }
    }
}

/// Whether an expression can start with a token of `kind`: one that
/// [`Parser::primary`], [`Parser::unary`] or `not` takes.
fn starts_expr(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Int(_)
            | TokenKind::Float(_)
            | TokenKind::Str(_)
            | TokenKind::Ident(_)
            | TokenKind::True
            | TokenKind::False
            | TokenKind::LParen
            | TokenKind::LBracket
            | TokenKind::Dot
            | TokenKind::Module
            | TokenKind::Fn
            | TokenKind::Minus
            | TokenKind::Tilde
            | TokenKind::Amp
            | TokenKind::Not
            | TokenKind::Return
            | TokenKind::Break
            | TokenKind::Continue
            | TokenKind::Todo
    )
}

/// Binary operators and their precedence; higher binds tighter.
fn binary_op(kind: &TokenKind) -> Option<(BinOp, u8)> {
    let op = match kind {
        TokenKind::Or => (BinOp::Or, 1),
        TokenKind::And => (BinOp::And, 2),
        TokenKind::EqEq => (BinOp::Eq, CMP_PREC),
        TokenKind::NotEq => (BinOp::NotEq, CMP_PREC),
        TokenKind::Lt => (BinOp::Lt, CMP_PREC),
        TokenKind::Le => (BinOp::Le, CMP_PREC),
        TokenKind::Gt => (BinOp::Gt, CMP_PREC),
        TokenKind::Ge => (BinOp::Ge, CMP_PREC),
        TokenKind::Pipe => (BinOp::BitOr, 5),
        TokenKind::Caret => (BinOp::BitXor, 6),
        TokenKind::Amp => (BinOp::BitAnd, 7),
        TokenKind::Shl => (BinOp::Shl, 8),
        TokenKind::Shr => (BinOp::Shr, 8),
        TokenKind::Plus => (BinOp::Add, 9),
        TokenKind::Minus => (BinOp::Sub, 9),
        TokenKind::Star => (BinOp::Mul, 10),
        TokenKind::Slash => (BinOp::Div, 10),
        TokenKind::Percent => (BinOp::Rem, 10),
        _ => return None,
    };
    Some(op)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::{DummyManager, FileManager};
    use crate::lex::tokenize;

    fn parse_src(src: &str) -> Result<Module, Vec<ParseError>> {
        let tokens = tokenize(DummyManager::new().entry_point(), src).unwrap();
        parse(&tokens)
    }

    fn errors(src: &str) -> Vec<ParseErrorKind> {
        parse_src(src)
            .unwrap_err()
            .into_iter()
            .map(|e| e.kind)
            .collect()
    }

    fn expected(expected: &str, found: TokenKind) -> ParseErrorKind {
        ParseErrorKind::Expected {
            expected: expected.to_string(),
            found,
        }
    }

    /// Parses `src` as an expression and renders it as an s-expression.
    fn expr(src: &str) -> String {
        let module = parse_src(&format!("let _ = {src}")).unwrap();
        let ItemKind::Binding(binding) = &module.items[0].kind else {
            unreachable!()
        };
        sexpr(&binding.value)
    }

    fn sexpr(expr: &Expr) -> String {
        let list = |exprs: &[Expr]| exprs.iter().map(sexpr).collect::<Vec<_>>().join(" ");
        match &expr.kind {
            ExprKind::Int(n) => n.to_string(),
            ExprKind::Float(x) => x.to_string(),
            ExprKind::Str(s) => format!("{s:?}"),
            ExprKind::Bool(b) => b.to_string(),
            ExprKind::Unit => "()".to_string(),
            ExprKind::Name(name) => name.clone(),
            ExprKind::Module(name) => format!("module.{}", name.name),
            ExprKind::Tuple(items) => format!("(tuple {})", list(items)),
            ExprKind::List(items) => format!("[{}]", list(items)),
            ExprKind::Repeat(value, len) => format!("[{}; {}]", sexpr(value), sexpr(len)),
            ExprKind::Unary(op, e) => format!("({op:?} {})", sexpr(e)),
            ExprKind::Binary(op, l, r) => format!("({op:?} {} {})", sexpr(l), sexpr(r)),
            ExprKind::Call(f, args) => {
                let args = args
                    .iter()
                    .map(|arg| match &arg.label {
                        Some(label) => format!("{}:{}", label.name, sexpr(&arg.value)),
                        None => sexpr(&arg.value),
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("(call {} {args})", sexpr(f))
            }
            ExprKind::Index(e, i) => format!("(index {} {})", sexpr(e), sexpr(i)),
            ExprKind::Field(e, field) => format!("(. {} {})", sexpr(e), field.name),
            ExprKind::Deref(e) => format!("(.* {})", sexpr(e)),
            ExprKind::AddrOf(Mutability::Let, e) => format!("(& {})", sexpr(e)),
            ExprKind::AddrOf(Mutability::Var, e) => format!("(&var {})", sexpr(e)),
            ExprKind::Cast(e, ty, false) => format!("(as {} {})", sexpr(e), render_ty(ty)),
            ExprKind::Cast(e, ty, true) => format!("(as! {} {})", sexpr(e), render_ty(ty)),
            ExprKind::FnType(ty) => render_ty(ty),
            ExprKind::Pipe(value, body) => format!("(|> {} {})", sexpr(value), sexpr(body)),
            ExprKind::Placeholder => "_".to_string(),
            ExprKind::Dot(name) => format!(".{}", name.name),
            ExprKind::Assign { target, op, value } => {
                let op = op.map(|op| format!("{op:?}")).unwrap_or_default();
                format!("({op}= {} {})", sexpr(target), sexpr(value))
            }
            ExprKind::Break => "break".to_string(),
            ExprKind::Continue => "continue".to_string(),
            ExprKind::Todo => "todo".to_string(),
            ExprKind::Return(None) => "(return)".to_string(),
            ExprKind::Return(Some(value)) => format!("(return {})", sexpr(value)),
        }
    }

    fn render_ty(ty: &Type) -> String {
        match &ty.kind {
            TypeKind::Named(name, None) => name.clone(),
            TypeKind::Named(name, Some(args)) => {
                let arg = |arg: &TypeArg| match &arg.label {
                    Some(label) => format!("{}: {}", label.name, render_ty(&arg.ty)),
                    None => render_ty(&arg.ty),
                };
                let args: Vec<_> = args.iter().map(arg).collect();
                format!("{name}({})", args.join(", "))
            }
            TypeKind::Pointer(Mutability::Let, pointee) => format!("&{}", render_ty(pointee)),
            TypeKind::Pointer(Mutability::Var, pointee) => {
                format!("&var {}", render_ty(pointee))
            }
            TypeKind::Qualified(module, ty) => format!("{}.{}", module.name, render_ty(ty)),
            TypeKind::Fn(params, ret) => {
                let params: Vec<_> = params.iter().map(render_ty).collect();
                let ret = ret.as_ref().map(|ret| format!(" -> {}", render_ty(ret)));
                format!("fn({}){}", params.join(", "), ret.unwrap_or_default())
            }
            TypeKind::Todo => "todo".to_string(),
        }
    }

    fn stmt_kinds(body: &Block) -> Vec<&'static str> {
        body.iter()
            .map(|s| match &s.kind {
                StmtKind::Binding(_) => "binding",
                StmtKind::Expr(expr) => match expr.kind {
                    ExprKind::Assign { .. } => "assign",
                    ExprKind::Return(_) => "return",
                    ExprKind::Break => "break",
                    ExprKind::Continue => "continue",
                    _ => "expr",
                },
                StmtKind::If { .. } => "if",
                StmtKind::While { .. } => "while",
                StmtKind::For { .. } => "for",
                StmtKind::Match { .. } => "match",
                StmtKind::Pass => "pass",
                StmtKind::Defer(_) => "defer",
            })
            .collect()
    }

    /// The value that `stmt` returns, if it's a `return` of one.
    fn returned(stmt: &Stmt) -> Option<&Expr> {
        match &stmt.kind {
            StmtKind::Expr(Expr {
                kind: ExprKind::Return(value),
                ..
            }) => value.as_deref(),
            _ => None,
        }
    }

    fn named(name: &str) -> TypeKind {
        TypeKind::Named(name.to_string(), None)
    }

    fn render_pattern(pattern: &Pattern) -> String {
        match &pattern.kind {
            PatternKind::Name(name) => name.clone(),
            PatternKind::Discard => "_".to_string(),
            PatternKind::Tuple(elems) => {
                let elems: Vec<_> = elems.iter().map(render_pattern).collect();
                format!("({})", elems.join(" "))
            }
            PatternKind::Variant(name, None) => format!(".{}", name.name),
            PatternKind::Variant(name, Some(holds)) => {
                format!(".{}({})", name.name, render_pattern(holds))
            }
            PatternKind::Literal(literal) => sexpr(literal),
            PatternKind::Array(elems) => {
                let elems: Vec<_> = elems.iter().map(render_pattern).collect();
                format!("[{}]", elems.join(" "))
            }
        }
    }

    /// The arms of the `match` that is the only statement of `f` in `src`.
    fn arms(src: &str) -> Vec<Arm> {
        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        let StmtKind::Match { arms, .. } = &f.body[0].kind else {
            panic!()
        };
        arms.clone()
    }

    #[test]
    fn example_program() {
        let module = parse_src(include_str!("../example.duck")).unwrap();
        let [host, global, counter, greeting, primes, point, add, main] = &module.items[..] else {
            panic!("expected 8 items, got {:#?}", module.items);
        };
        assert!(!host.is_pub);
        assert!(module.items[1..].iter().all(|item| item.is_pub));

        let ItemKind::Extern(host) = &host.kind else {
            panic!()
        };
        assert_eq!(host.module, None);
        let fns: Vec<_> = host
            .fns
            .iter()
            .map(|f| (f.sig.name.name.as_str(), f.import_name.as_deref()))
            .collect();
        assert_eq!(
            fns,
            vec![
                ("logi", None),
                ("logf", Some("log_f32")),
                ("logs", Some("log_str"))
            ]
        );
        assert_eq!(host.fns[0].sig.params[0].ty.kind, named("i32"));
        assert_eq!(render_ty(&host.fns[2].sig.params[0].ty), "array(u8)");

        let ItemKind::Binding(global) = &global.kind else {
            panic!()
        };
        assert_eq!(global.mutability, Mutability::Let);
        assert_eq!(global.pattern.kind, PatternKind::Name("global".to_string()));
        assert_eq!(global.value.kind, ExprKind::Bool(true));

        let ItemKind::Binding(counter) = &counter.kind else {
            panic!()
        };
        assert_eq!(counter.mutability, Mutability::Var);
        assert_eq!(counter.value.kind, ExprKind::Int(0));

        let ItemKind::Binding(greeting) = &greeting.kind else {
            panic!()
        };
        assert_eq!(sexpr(&greeting.value), r#""Hello, duck!""#);
        let ItemKind::Binding(primes) = &primes.kind else {
            panic!()
        };
        assert_eq!(sexpr(&primes.value), "[2 3 5 7]");

        let ItemKind::Struct(point) = &point.kind else {
            panic!()
        };
        assert_eq!(point.name.name, "Point");
        let fields: Vec<_> = point
            .entries
            .iter()
            .filter_map(Entry::own)
            .map(|f| (f.name.name.as_str(), f.ty.kind.clone()))
            .collect();
        assert_eq!(fields, vec![("x", named("f32")), ("y", named("f32"))]);

        let ItemKind::Fn(add) = &add.kind else {
            panic!()
        };
        assert_eq!(add.sig.name.name, "add");
        assert_eq!(add.sig.params.len(), 2);
        assert_eq!(add.sig.ret.as_ref().unwrap().kind, named("i32"));
        let Some(sum) = returned(&add.body[0]) else {
            panic!()
        };
        assert_eq!(sexpr(sum), "(Add a b)");

        let ItemKind::Fn(main) = &main.kind else {
            panic!()
        };
        assert_eq!(main.sig.ret, None);
        assert_eq!(
            stmt_kinds(&main.body),
            vec![
                "binding", "binding", "binding", "expr", "expr", "expr", "for", "binding", "while",
                "while"
            ]
        );
        let StmtKind::While { cond, body } = &main.body[8].kind else {
            panic!()
        };
        assert_eq!(sexpr(cond), "(Lt i 3)");
        assert_eq!(stmt_kinds(body), vec!["assign", "continue"]);
    }

    #[test]
    fn precedence() {
        assert_eq!(
            expr("a or b and not c == d | e ^ f & g << h + i * -j"),
            "(Or a (And b (Not (Eq c (BitOr d (BitXor e (BitAnd f (Shl g (Add h (Mul i (Neg j)))))))))))"
        );
        assert_eq!(
            expr("a * b + c << d & e ^ f | g == h and i or j"),
            "(Or (And (Eq (BitOr (BitXor (BitAnd (Shl (Add (Mul a b) c) d) e) f) g) h) i) j)"
        );
        assert_eq!(expr("not a and b"), "(And (Not a) b)");
        assert_eq!(expr("not not a"), "(Not (Not a))");
        assert_eq!(expr("a & 1 == 0"), "(Eq (BitAnd a 1) 0)");
        assert_eq!(expr("(a + b) * c"), "(Mul (Add a b) c)");
    }

    #[test]
    fn left_associative() {
        assert_eq!(expr("a - b - c"), "(Sub (Sub a b) c)");
        assert_eq!(expr("a / b * c"), "(Mul (Div a b) c)");
        assert_eq!(expr("a or b or c"), "(Or (Or a b) c)");
    }

    #[test]
    fn assignment_is_an_expression() {
        assert_eq!(expr("a = b = c"), "(= a (= b c))");
        assert_eq!(expr("a += b.x *= c"), "(Add= a (Mul= (. b x) c))");
        assert_eq!(expr("a = b or c |> f(_)"), "(= a (|> (Or b c) (call f _)))");
        assert_eq!(expr("(a = b) + c"), "(Add (= a b) c)");
        assert_eq!(
            expr("f(a = 1, x: p.* = 2)"),
            "(call f (= a 1) x:(= (.* p) 2))"
        );
        assert_eq!(expr("a[i = 0]"), "(index a (= i 0))");
        assert_eq!(expr("x |> (y = _)"), "(|> x (= y _))");
        let src = "fn f():\n    while (n = next(p)) != 0:\n        a = b = n\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        let StmtKind::While { cond, body } = &f.body[0].kind else {
            panic!()
        };
        assert_eq!(sexpr(cond), "(NotEq (= n (call next p)) 0)");
        assert_eq!(stmt_kinds(body), vec!["assign"]);
        // Only the first of a chain is a target the parser has yet to see.
        assert_eq!(
            errors("fn f():\n    a = b + 1 = c\n    a = 1 = b\n"),
            vec![
                ParseErrorKind::InvalidAssignTarget,
                ParseErrorKind::InvalidAssignTarget
            ]
        );
    }

    #[test]
    fn postfix_and_unary() {
        assert_eq!(expr("-f(x, 1).y[0]"), "(Neg (index (. (call f x 1) y) 0))");
        assert_eq!(expr("~-a"), "(BitNot (Neg a))");
        assert_eq!(expr("f()()"), "(call (call f ) )");
    }

    #[test]
    fn casts() {
        assert_eq!(expr("-x as i64"), "(as (Neg x) i64)");
        assert_eq!(expr("a + b as i64"), "(Add a (as b i64))");
        assert_eq!(expr("a * b as i64"), "(Mul a (as b i64))");
        assert_eq!(expr("x as i64 as f32"), "(as (as x i64) f32)");
        assert_eq!(expr("-x as! &u8 as uint"), "(as (as! (Neg x) &u8) uint)");
        assert_eq!(expr("a + b as! fn(i32)"), "(Add a (as! b fn(i32)))");
        assert_eq!(expr("not x as bool"), "(Not (as x bool))");
        assert_eq!(expr("f(x).y as u8"), "(as (. (call f x) y) u8)");
    }

    #[test]
    fn pointers() {
        assert_eq!(expr("p.*"), "(.* p)");
        assert_eq!(expr("p.*.x.*"), "(.* (. (.* p) x))");
        assert_eq!(expr("&p.x"), "(& (. p x))");
        assert_eq!(expr("-&p.* as u32"), "(as (Neg (& (.* p))) u32)");
        assert_eq!(expr("0 as &&u32"), "(as 0 &&u32)");
        assert_eq!(expr("&var p.x"), "(&var (. p x))");
        assert_eq!(expr("&var&p.*"), "(&var (& (.* p)))");
        assert_eq!(expr("a & var_b"), "(BitAnd a var_b)");
        assert_eq!(expr("0 as &var &u32"), "(as 0 &var &u32)");
        assert_eq!(expr("(&var P).size"), "(. (&var P) size)");
        let src = "fn f(p: &var P) -> &array(i32):\n    p.* = 1\n    p.*.x += 1\n    p.*= 2\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(render_ty(&f.sig.params[0].ty), "&var P");
        assert_eq!(render_ty(f.sig.ret.as_ref().unwrap()), "&array(i32)");
        assert_eq!(stmt_kinds(&f.body), vec!["assign", "assign", "assign"]);
        assert_eq!(
            errors("fn f():\n    &p = 1\n"),
            vec![ParseErrorKind::InvalidAssignTarget]
        );
    }

    #[test]
    fn labelled_args() {
        assert_eq!(expr("Point(x: 1, y: 2)"), "(call Point x:1 y:2)");
        assert_eq!(expr("f(1, b: c)"), "(call f 1 b:c)");
        assert_eq!(expr("f(a == b)"), "(call f (Eq a b))");
    }

    #[test]
    fn literals() {
        assert_eq!(expr("()"), "()");
        assert_eq!(expr("f((), ( ))"), "(call f () ())");
        assert_eq!(expr("[]"), "[]");
        assert_eq!(expr("[1, 2,]"), "[1 2]");
        assert_eq!(
            expr(r#"[1.5, "hi", true, false]"#),
            r#"[1.5 "hi" true false]"#
        );
        assert_eq!(expr("[0; 4]"), "[0; 4]");
        assert_eq!(expr("[[a, b]; n + 1]"), "[[a b]; (Add n 1)]");
        assert_eq!(
            errors("let a = [1; 2, 3]\n"),
            vec![expected("`]`", TokenKind::Comma)]
        );
        assert_eq!(
            errors("let a = [1, 2; 3]\n"),
            vec![expected("`]`", TokenKind::Semi)]
        );
        assert_eq!(
            errors("let a = [; 3]\n"),
            vec![expected("expression", TokenKind::Semi)]
        );
    }

    #[test]
    fn module_properties() {
        assert_eq!(expr("module.static"), "module.static");
        assert_eq!(expr("module.static.len"), "(. module.static len)");
        assert_eq!(expr("module.static[0]"), "(index module.static 0)");
        for src in ["let x = module\n", "let x = module.0\n", "let module = 1\n"] {
            assert!(parse_src(src).is_err(), "{src:?}");
        }
    }

    #[test]
    fn tuples() {
        assert_eq!(expr("(1, 2)"), "(tuple 1 2)");
        assert_eq!(expr("(a, (b, c),)"), "(tuple a (tuple b c))");
        assert_eq!(expr("(a)"), "a");
        assert_eq!(expr("t.0.1"), "(. (. t 0) 1)");
        assert_eq!(expr("f(x).10"), "(. (call f x) 10)");
        assert_eq!(expr("p.*.0"), "(. (.* p) 0)");
        let src = "fn f(t: tuple(i32, tuple(f32, &u8))) -> tuple(i32, tuple()):\n    t.1.0 = 1.0\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(
            render_ty(&f.sig.params[0].ty),
            "tuple(i32, tuple(f32, &u8))"
        );
        assert_eq!(
            render_ty(f.sig.ret.as_ref().unwrap()),
            "tuple(i32, tuple())"
        );
        assert_eq!(stmt_kinds(&f.body), vec!["assign"]);
        // A comma after one element makes a tuple of it, as only brackets
        // around it don't.
        let value = |src: &str| {
            let module = parse_src(src).unwrap();
            let ItemKind::Binding(binding) = &module.items[0].kind else {
                panic!()
            };
            sexpr(&binding.value)
        };
        assert_eq!(value("let _ = (1,)\n"), "(tuple 1)");
        assert_eq!(value("let _ = (1)\n"), "1");
        assert_eq!(value("let _ = ((1,),)\n"), "(tuple (tuple 1))");
        assert_eq!(
            errors("fn f():\n    (a, b) = (b, a)\n"),
            vec![ParseErrorKind::InvalidAssignTarget]
        );
    }

    #[test]
    fn patterns() {
        let pattern = |src: &str| {
            let module = parse_src(src).unwrap();
            let ItemKind::Binding(binding) = &module.items[0].kind else {
                panic!()
            };
            binding.pattern.clone()
        };
        let render = render_pattern;
        assert_eq!(render(&pattern("let x = 1\n")), "x");
        assert_eq!(render(&pattern("let _ = 1\n")), "_");
        assert_eq!(render(&pattern("var (a, _) = t\n")), "(a _)");
        assert_eq!(render(&pattern("let ((a, b), (c)) = t\n")), "((a b) c)");
        assert_eq!(render(&pattern("let () = t\n")), "()");
        assert_eq!(render(&pattern("let (a, b): tuple(u8, u8) = t\n")), "(a b)");
        assert_eq!(render(&pattern("let (a,) = t\n")), "(a)");
        assert_eq!(render(&pattern("let ((a,), b) = t\n")), "((a) b)");
        assert_eq!(
            errors("let 1 = t\n"),
            vec![expected("pattern", TokenKind::Int(1))]
        );
    }

    #[test]
    fn pipes() {
        assert_eq!(expr("x |> f(_, 1)"), "(|> x (call f _ 1))");
        assert_eq!(
            expr("x |> _ + 1 |> f(_, _)"),
            "(|> (|> x (Add _ 1)) (call f _ _))"
        );
        assert_eq!(expr("a or b |> not _"), "(|> (Or a b) (Not _))");
        assert_eq!(expr("a | b |> _ | c"), "(|> (BitOr a b) (BitOr _ c))");
        assert_eq!(expr("f(x |> _.a, 2)"), "(call f (|> x (. _ a)) 2)");
        assert_eq!(
            expr("h |> _(1)[_ as u8]"),
            "(|> h (index (call _ 1) (as _ u8)))"
        );
        // The value of a nested pipe is still in the body of the outer one.
        assert_eq!(expr("x |> (_ |> g(_))"), "(|> x (|> _ (call g _)))");
        assert_eq!(
            expr("x |> f(_, y |> g(_))"),
            "(|> x (call f _ (|> y (call g _))))"
        );
    }

    #[test]
    fn return_is_an_expression() {
        // Its value is all that follows it.
        assert_eq!(expr("a or return b or c"), "(Or a (return (Or b c)))");
        assert_eq!(
            expr("return a = n |> f(_)"),
            "(return (= a (|> n (call f _))))"
        );
        assert_eq!(expr("-return x.y + 1"), "(Neg (return (Add (. x y) 1)))");
        // It has none before a token that starts no expression.
        assert_eq!(
            expr("f(return, [return], (return) + 1)"),
            "(call f (return) [(return)] (Add (return) 1))"
        );
        assert_eq!(expr("a and return or b"), "(Or (And a (return)) b)");
        assert_eq!(expr("return -1"), "(return (Neg 1))");
        assert_eq!(expr("return .none"), "(return .none)");
        assert_eq!(expr("return (a, b).0"), "(return (. (tuple a b) 0))");
        assert_eq!(expr("return not a"), "(return (Not a))");
        assert_eq!(expr("return return"), "(return (return))");
        // It ends a chain of pipes.
        assert_eq!(
            expr("x |> g(_) |> return _"),
            "(|> (|> x (call g _)) (return _))"
        );
        assert_eq!(
            expr("x |> ok(_) or return _ + 1"),
            "(|> x (Or (call ok _) (return (Add _ 1))))"
        );
    }

    #[test]
    fn break_and_continue_are_expressions() {
        assert_eq!(expr("a or break"), "(Or a break)");
        assert_eq!(
            expr("f(continue, x) and break or c"),
            "(Or (And (call f continue x) break) c)"
        );
        // Each is an expression, so one after a `return` is its value.
        assert_eq!(expr("return break"), "(return break)");
        assert_eq!(expr("(break, continue).0"), "(. (tuple break continue) 0)");
        // Nor is either a value to pipe on from.
        assert_eq!(
            errors("let _ = x |> break\n"),
            vec![ParseErrorKind::PipeWithoutPlaceholder]
        );
        assert_eq!(
            expr("x |> g(_) or break |> f(_)"),
            "(|> (|> x (Or (call g _) break)) (call f _))"
        );
    }

    #[test]
    fn todo_is_an_expression() {
        assert_eq!(expr("a or todo"), "(Or a todo)");
        assert_eq!(expr("f(todo, x) + todo"), "(Add (call f todo x) todo)");
        assert_eq!(expr("return todo"), "(return todo)");
        // It is a keyword, so nothing is named it.
        assert!(!errors("let todo = 1\n").is_empty());
    }

    #[test]
    fn todo_is_a_type() {
        assert_eq!(expr("x as todo"), "(as x todo)");
        assert_eq!(
            expr("x as &var Box(todo, fn(todo) -> todo)"),
            "(as x &var Box(todo, fn(todo) -> todo))"
        );
        let module = parse_src("fn f(a: todo) -> todo:\n    let x: todo = todo\n").unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(f.sig.params[0].ty.kind, TypeKind::Todo);
        assert_eq!(f.sig.ret.as_ref().unwrap().to_string(), "todo");
        // It is no name, so it takes no arguments and is in no module.
        assert!(!errors("let x: todo(i32) = 1\n").is_empty());
        assert!(!errors("let x: m.todo = 1\n").is_empty());
    }

    #[test]
    fn a_return_ends_its_chain_of_pipes() {
        // Its value would be the rest of the chain, which reads as if it
        // came after.
        for src in [
            "x |> return _ |> f(_)",
            "x |> ok(_) or return _ |> f(_)",
            "x |> g(_) or return |> f(_)",
            "x |> return _ + 1 |> f(_) |> g(_)",
        ] {
            let src = format!("let _ = {src}");
            assert_eq!(errors(&src), vec![ParseErrorKind::PipeAfterReturn], "{src}");
        }
        let src = "let a = x |> return _ |> f(_)\n";
        let span = parse_src(src).unwrap_err()[0].span;
        assert_eq!(&src[span.start..span.end], "|>");
        // Brackets end its value, or hold a chain of its own.
        assert_eq!(
            expr("x |> (return _) + 1 |> f(_)"),
            "(|> (|> x (Add (return _) 1)) (call f _))"
        );
        assert_eq!(
            expr("x |> return (_ |> f(_))"),
            "(|> x (return (|> _ (call f _))))"
        );
        assert_eq!(
            expr("x |> g(return _ |> f(_)) |> h(_)"),
            "(|> (|> x (call g (return (|> _ (call f _))))) (call h _))"
        );
        assert_eq!(
            expr("x |> _[return _ |> f(_)] |> [return _ |> f(_)]"),
            "(|> (|> x (index _ (return (|> _ (call f _))))) [(return (|> _ (call f _)))])"
        );
        // One that no pipe holds has a chain as its value.
        assert_eq!(expr("return x |> f(_)"), "(return (|> x (call f _)))");
        // One with no value is the body of no pipe.
        assert_eq!(
            errors("let _ = x |> return\n"),
            vec![ParseErrorKind::PipeWithoutPlaceholder]
        );
    }

    #[test]
    fn pipe_body_must_use_placeholder() {
        for src in ["x |> f", "x |> f()", "x |> f(y |> g(_))", "x |> f(_) |> g"] {
            let src = format!("let _ = {src}");
            assert_eq!(
                errors(&src),
                vec![ParseErrorKind::PipeWithoutPlaceholder],
                "{src}"
            );
        }
        let src = "let a = x |> f(1)\n";
        let span = parse_src(src).unwrap_err()[0].span;
        assert_eq!(&src[span.start..span.end], "f(1)");
    }

    #[test]
    fn placeholder_outside_pipe() {
        for src in [
            "let a = _",
            "let a = f(_)",
            "let a = _ |> f(_)",
            "let a = f(_) + (x |> _)",
        ] {
            assert_eq!(
                errors(src),
                vec![ParseErrorKind::PlaceholderOutsidePipe],
                "{src}"
            );
        }
        // Patterns, labels and other names are not expressions.
        parse_src("fn f(_: i32):\n    for _ in xs:\n        let _ = g(_: 1)\n").unwrap();
    }

    #[test]
    fn pipe_lines() {
        let module = parse_src("fn f():\n    let a = 1\n        |> g(_)\n    return a\n").unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        let StmtKind::Binding(binding) = &f.body[0].kind else {
            panic!()
        };
        assert_eq!(sexpr(&binding.value), "(|> 1 (call g _))");
        assert_eq!(f.body.len(), 2);

        // In the head of a block, the body of the block is indented as usual.
        parse_src("fn f():\n    if x\n        |> g(_):\n        pass\n    pass\n").unwrap();

        for src in [
            "let a = 1\n|> g(_)\nlet b = 2\n",
            "fn f():\n    let a = 1\n    |> g(_)\n    return a\n",
            "fn f():\n    pass\n|> g(_)\n",
            "|> g(_)\n",
        ] {
            assert_eq!(errors(src), vec![ParseErrorKind::LeadingPipe], "{src}");
        }
        // Only at the start of a line.
        assert_eq!(
            errors("let a = 1 + |> g(_)\n"),
            vec![expected("expression", TokenKind::PipeArrow)]
        );
        assert_eq!(
            errors("let a = 1 |>\n    g(_)\n"),
            vec![expected("expression", TokenKind::Newline)]
        );
    }

    #[test]
    fn comparisons_do_not_chain() {
        assert_eq!(
            errors("let _ = a < b < c"),
            vec![ParseErrorKind::ChainedComparison]
        );
        assert_eq!(expr("(a < b) == c"), "(Eq (Lt a b) c)");
    }

    #[test]
    fn not_is_not_an_operand_of_comparison() {
        assert_eq!(
            errors("let _ = a == not b"),
            vec![expected("expression", TokenKind::Not)]
        );
    }

    #[test]
    fn types() {
        let module =
            parse_src("fn f(xs: array(array(i32)), n: u8,) -> array(f32):\n\tpass").unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(render_ty(&f.sig.params[0].ty), "array(array(i32))");
        assert_eq!(render_ty(&f.sig.params[1].ty), "u8");
        assert_eq!(render_ty(f.sig.ret.as_ref().unwrap()), "array(f32)");

        let module = parse_src("fn f(a: tuple(), b: &tuple()) -> tuple():\n\tpass").unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(
            f.sig.params[0].ty.kind,
            TypeKind::Named("tuple".to_string(), Some(Vec::new()))
        );
        assert_eq!(render_ty(&f.sig.params[1].ty), "&tuple()");
        assert_eq!(render_ty(f.sig.ret.as_ref().unwrap()), "tuple()");

        let module = parse_src("let x: i32() = 1").unwrap();
        let ItemKind::Binding(x) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(render_ty(x.ty.as_ref().unwrap()), "i32()");

        let module = parse_src("let x: i32 = 1").unwrap();
        let ItemKind::Binding(x) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(x.ty.as_ref().unwrap().kind, named("i32"));
    }

    #[test]
    fn generic_types() {
        let module = parse_src("let x: Map(&K, tuple(V, W), Box(T),) = 1").unwrap();
        let ItemKind::Binding(x) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(
            render_ty(x.ty.as_ref().unwrap()),
            "Map(&K, tuple(V, W), Box(T))"
        );
        assert_eq!(expr("x as Box(i32)"), "(as x Box(i32))");
        assert_eq!(
            expr("Box(&i32)(value: 1)"),
            "(call (call Box (& i32)) value:1)"
        );
    }

    #[test]
    fn function_types() {
        let ty = |src: &str| {
            let module = parse_src(&format!("let x: {src} = 1")).unwrap();
            let ItemKind::Binding(x) = &module.items[0].kind else {
                panic!()
            };
            render_ty(x.ty.as_ref().unwrap())
        };
        assert_eq!(ty("fn()"), "fn()");
        assert_eq!(ty("fn(i32, &u8,) -> bool"), "fn(i32, &u8) -> bool");
        // The result takes everything it can.
        assert_eq!(ty("fn(A) -> fn(B) -> C"), "fn(A) -> fn(B) -> C");
        assert_eq!(ty("&fn(A) -> &B"), "&fn(A) -> &B");
        assert_eq!(ty("array(fn(A))"), "array(fn(A))");

        assert_eq!(expr("fn(i32) -> i32"), "fn(i32) -> i32");
        assert_eq!(expr("malloc(fn(i32))"), "(call malloc fn(i32))");
        assert_eq!(
            expr("array(fn(i32) -> u8)(len: 1, ptr: p)"),
            "(call (call array fn(i32) -> u8) len:1 ptr:p)"
        );
        assert_eq!(expr("x as fn(i32) -> u8"), "(as x fn(i32) -> u8)");
        assert_eq!(expr("(fn(i32)).size"), "(. fn(i32) size)");
        assert_eq!(
            errors("let x: fn = 1\nlet y = fn\nlet z: fn(a: i32) = 1\n"),
            vec![
                expected("`(`", TokenKind::Eq),
                expected("`(`", TokenKind::Newline),
                expected("`)`", TokenKind::Colon),
            ]
        );
    }

    #[test]
    fn types_are_not_bracketed_starred_or_parenthesized() {
        assert_eq!(
            errors("let x: [u8] = 1"),
            vec![expected("type", TokenKind::LBracket)]
        );
        assert_eq!(
            errors("let x: *u8 = 1"),
            vec![expected("type", TokenKind::Star)]
        );
        assert_eq!(
            errors("let x: (i32, u8) = 1\nlet y: (i32) = 1\nlet z: () = 1\n"),
            vec![expected("type", TokenKind::LParen); 3]
        );
    }

    #[test]
    fn statements() {
        let src = "\
fn f():
    x = 1
    x.y += 2
    x[0] %= 3
    g(x)
    return
    if a:
        pass
    else if b:
        pass
    else:
        pass
";
        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(
            stmt_kinds(&f.body),
            vec!["assign", "assign", "assign", "expr", "return", "if"]
        );
        let ops: Vec<_> = f.body[..3]
            .iter()
            .map(|s| match &s.kind {
                StmtKind::Expr(Expr {
                    kind: ExprKind::Assign { op, .. },
                    ..
                }) => *op,
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(ops, vec![None, Some(BinOp::Add), Some(BinOp::Rem)]);
        assert_eq!(returned(&f.body[4]), None);

        let StmtKind::If {
            else_body: Some(else_body),
            ..
        } = &f.body[5].kind
        else {
            panic!()
        };
        let [nested] = &else_body[..] else { panic!() };
        let StmtKind::If {
            cond,
            else_body: Some(last),
            ..
        } = &nested.kind
        else {
            panic!()
        };
        assert_eq!(sexpr(cond), "b");
        assert_eq!(stmt_kinds(last), vec!["pass"]);
    }

    #[test]
    fn defers() {
        let src = "\
fn f():
    defer close(h)
    defer heap = mark
    defer:
        x = 1
        return
    pass
";
        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(stmt_kinds(&f.body), vec!["defer", "defer", "defer", "pass"]);
        let bodies: Vec<_> = f.body[..3]
            .iter()
            .map(|s| match &s.kind {
                StmtKind::Defer(body) => stmt_kinds(body),
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(
            bodies,
            vec![vec!["expr"], vec!["assign"], vec!["assign", "return"]]
        );
        // The line of a `defer` is one expression, and no other statement.
        assert_eq!(
            errors("fn f():\n    defer pass\n    defer\n"),
            vec![
                expected("expression", TokenKind::Pass),
                expected("expression", TokenKind::Newline),
            ]
        );
    }

    #[test]
    fn matches() {
        let src = "\
fn f():
    match g(s):
        .circle(r):
            pass
        .rect((w, _)):
            return
        .empty:
            pass
        other:
            pass
        else:
            x = 1
            return
";
        let arms = arms(src);
        let patterns: Vec<_> = arms
            .iter()
            .map(|arm| render_pattern(&arm.pattern))
            .collect();
        assert_eq!(
            patterns,
            [".circle(r)", ".rect((w _))", ".empty", "other", "_"]
        );
        let bodies: Vec<_> = arms.iter().map(|arm| stmt_kinds(&arm.body)).collect();
        assert_eq!(bodies[1], ["return"]);
        assert_eq!(bodies[4], ["assign", "return"]);
        let span = arms[1].pattern.span;
        assert_eq!(&src[span.start..span.end], ".rect((w, _))");
        let span = arms[4].pattern.span;
        assert_eq!(&src[span.start..span.end], "else");

        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        let StmtKind::Match { value, .. } = &f.body[0].kind else {
            panic!()
        };
        assert_eq!(sexpr(value), "(call g s)");
    }

    #[test]
    fn match_patterns_nest_and_test_literals() {
        let src = "\
fn f():
    match s:
        .some((0, _)):
            pass
        (.none, -1, -1.5):
            pass
        [a, _, 3,]:
            pass
        []:
            pass
        \"zero\":
            pass
        true:
            pass
        .rect((.a, [x, false])):
            pass
        (((x))):
            pass
";
        let arms = arms(src);
        let patterns: Vec<_> = arms
            .iter()
            .map(|arm| render_pattern(&arm.pattern))
            .collect();
        assert_eq!(
            patterns,
            [
                ".some((0 _))",
                "(.none (Neg 1) (Neg 1.5))",
                "[a _ 3]",
                "[]",
                "\"zero\"",
                "true",
                ".rect((.a [x false]))",
                "x",
            ]
        );
        let span = arms[1].pattern.span;
        assert_eq!(&src[span.start..span.end], "(.none, -1, -1.5)");
    }

    #[test]
    fn match_errors() {
        let arm = |arm: &str| format!("fn f():\n    match s:\n        {arm}:\n            pass\n");
        assert_eq!(
            errors(&arm("Shape.circle(r)")),
            vec![ParseErrorKind::QualifiedPattern]
        );
        assert_eq!(
            errors(&arm("Option(f32).some(x)")),
            vec![ParseErrorKind::QualifiedPattern]
        );
        assert_eq!(
            errors(&arm(".circle(a, b)")),
            vec![expected("`)`", TokenKind::Comma)]
        );
        assert_eq!(
            errors(&arm(".circle()")),
            vec![expected("pattern", TokenKind::RParen)]
        );
        assert_eq!(
            errors(&arm("x + 1")),
            vec![expected("`:`", TokenKind::Plus)]
        );
        assert_eq!(
            errors(
                "fn f():\n    match s:\n        else:\n            pass\n        .a:\n            pass\n"
            ),
            vec![ParseErrorKind::ArmAfterElse]
        );
        assert_eq!(
            errors("fn f():\n    match s:\n    pass\n"),
            vec![expected("indented block", TokenKind::Pass)]
        );
        assert_eq!(
            errors("fn f():\n    match s:\n        .a: pass\n"),
            vec![expected("newline", TokenKind::Pass)]
        );
        let x = || TokenKind::Ident("x".into());
        assert_eq!(errors(&arm("-x")), vec![expected("number", x())]);
        assert_eq!(
            errors(&arm("-true")),
            vec![expected("number", TokenKind::True)]
        );
        assert_eq!(
            errors(&arm("[a; 2]")),
            vec![expected("`]`", TokenKind::Semi)]
        );
        assert!(parse_src(&arm("(.a,)")).is_ok());
        assert_eq!(
            errors(&arm("(a, T.b)")),
            vec![ParseErrorKind::QualifiedPattern]
        );
        assert_eq!(
            errors("let .a = s\n"),
            vec![expected("pattern", TokenKind::Dot)]
        );
        assert_eq!(
            errors("let [a] = s\n"),
            vec![expected("pattern", TokenKind::LBracket)]
        );
        assert_eq!(
            errors("let (a, 1) = s\n"),
            vec![expected("pattern", TokenKind::Int(1))]
        );
        assert_eq!(
            errors("let match = 1\n"),
            vec![expected("pattern", TokenKind::Match)]
        );
    }

    #[test]
    fn field_visibility() {
        let src = "struct P:\n    pub x: f32\n    y: f32\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Struct(p) = &module.items[0].kind else {
            panic!()
        };
        let fields: Vec<_> = p.entries.iter().filter_map(Entry::own).collect();
        let names: Vec<_> = fields
            .iter()
            .map(|f| (f.is_pub, f.name.name.as_str()))
            .collect();
        assert_eq!(names, vec![(true, "x"), (false, "y")]);
        let span = fields[0].span;
        assert_eq!(&src[span.start..span.end], "pub x: f32");

        assert_eq!(
            errors("fn f(pub x: i32):\n    pass\n"),
            vec![expected("identifier", TokenKind::Pub)]
        );
    }

    #[test]
    fn field_defaults() {
        let src = "struct P:\n    pub x: f32 = 1.5 * 2.0\n    y: &P = 0\n    z: i32\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Struct(p) = &module.items[0].kind else {
            panic!()
        };
        let fields: Vec<_> = p.entries.iter().filter_map(Entry::own).collect();
        let defaults: Vec<_> = fields
            .iter()
            .map(|f| f.default.as_ref().map(sexpr))
            .collect();
        let want = [Some("(Mul 1.5 2)"), Some("0"), None].map(|d| d.map(str::to_string));
        assert_eq!(defaults, want);
        let span = fields[0].span;
        assert_eq!(&src[span.start..span.end], "pub x: f32 = 1.5 * 2.0");

        assert_eq!(
            errors("struct P:\n    x: i32 =\n"),
            vec![expected("expression", TokenKind::Newline)]
        );
        assert_eq!(
            errors("struct P:\n    x = 1\n"),
            vec![expected("`:`", TokenKind::Eq)]
        );
    }

    #[test]
    fn param_defaults() {
        let src = "fn f(a: i32, b: f32 = 1.5 * 2.0, c: &P = 0) -> i32:\n    return a\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        let params = &f.sig.params;
        let defaults: Vec<_> = params
            .iter()
            .map(|p| p.default.as_ref().map(sexpr))
            .collect();
        let want = [None, Some("(Mul 1.5 2)"), Some("0")].map(|d| d.map(str::to_string));
        assert_eq!(defaults, want);
        let span = params[1].span;
        assert_eq!(&src[span.start..span.end], "b: f32 = 1.5 * 2.0");

        // A default is before the host's name for an `extern` function.
        let src = "extern:\n    fn log(n: i32, base: i32 = 10) = \"log_int\"\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Extern(host) = &module.items[0].kind else {
            panic!()
        };
        let log = &host.fns[0];
        assert_eq!(log.sig.params[1].default.as_ref().map(sexpr).unwrap(), "10");
        assert_eq!(log.import_name.as_deref(), Some("log_int"));

        assert_eq!(
            errors("fn f(a: i32 =):\n    pass\n"),
            vec![expected("expression", TokenKind::RParen)]
        );
        assert_eq!(
            errors("fn f(a = 1):\n    pass\n"),
            vec![expected("`:`", TokenKind::Eq)]
        );
    }

    #[test]
    fn empty_struct() {
        let module = parse_src("struct Unit:\n    pass\n").unwrap();
        let ItemKind::Struct(unit) = &module.items[0].kind else {
            panic!()
        };
        assert!(unit.entries.is_empty());
    }

    #[test]
    fn uses_in_bodies() {
        let src = "\
struct Named:
    use Head
    use geo.Box(&T)
    pub name: array(u8)
union Wide:
    use option(i32)
    other
enum(u8) Color:
    use Warm
    red
";
        let module = parse_src(src).unwrap();
        let entries = |item: &Item| -> Vec<String> {
            fn render<T>(entry: &Entry<T>, own: impl Fn(&T) -> &Ident) -> String {
                match entry {
                    Entry::Own(entry) => own(entry).name.clone(),
                    Entry::Use(ty) => format!("use {}", render_ty(ty)),
                }
            }
            match &item.kind {
                ItemKind::Struct(s) => s.entries.iter().map(|e| render(e, |f| &f.name)).collect(),
                ItemKind::Union(u) => u.entries.iter().map(|e| render(e, |v| &v.name)).collect(),
                ItemKind::Enum(e) => e.entries.iter().map(|e| render(e, |m| &m.name)).collect(),
                _ => panic!(),
            }
        };
        assert_eq!(
            entries(&module.items[0]),
            ["use Head", "use geo.Box(&T)", "name"]
        );
        assert_eq!(entries(&module.items[1]), ["use option(i32)", "other"]);
        assert_eq!(entries(&module.items[2]), ["use Warm", "red"]);
        let ItemKind::Struct(named) = &module.items[0].kind else {
            panic!()
        };
        let Entry::Use(ty) = &named.entries[1] else {
            panic!()
        };
        assert_eq!(&src[ty.span.start..ty.span.end], "geo.Box(&T)");

        // `pub` is each field's own, and a `use` names one type.
        assert_eq!(
            errors("struct S:\n    pub use Head\n"),
            vec![expected("identifier", TokenKind::Use)]
        );
        assert_eq!(
            errors("struct S:\n    use A, B\n"),
            vec![expected("newline", TokenKind::Comma)]
        );
        assert_eq!(
            errors("union U:\n    use\n"),
            vec![expected("type", TokenKind::Newline)]
        );
    }

    #[test]
    fn uses_come_before_the_rest_of_a_body() {
        let src = "struct S:\n    use A\n    x: i32\n    use B\n    use C\n";
        assert_eq!(
            errors(src),
            [ParseErrorKind::UseAfterEntry, ParseErrorKind::UseAfterEntry]
        );
        let span = parse_src(src).unwrap_err()[0].span;
        assert_eq!(&src[span.start..span.end], "use B");
        let after = [ParseErrorKind::UseAfterEntry];
        assert_eq!(errors("union U:\n    a\n    use V\n"), after);
        assert_eq!(errors("enum(u8) E:\n    a = 1\n    use F\n"), after);
        // A `pass` stands for the lines of its own that a struct lacks.
        assert_eq!(errors("struct S:\n    pass\n    use A\n"), after);
    }

    #[test]
    fn bounds_list_the_types_a_type_argument_uses() {
        let bounds = |src: &str| -> Vec<Vec<String>> {
            let module = parse_src(src).unwrap();
            let ItemKind::Fn(f) = &module.items[0].kind else {
                panic!()
            };
            let params = f.sig.type_params.iter();
            params
                .map(|p| p.bound.iter().map(render_ty).collect())
                .collect()
        };
        let src = "fn(A, B: Head, C: (Head, mod.Meta(A)), D: (), E: (Head), F: (Head, Tail,)) f():
    pass
";
        assert_eq!(
            bounds(src),
            [
                vec![],
                vec!["Head"],
                vec!["Head", "mod.Meta(A)"],
                vec![],
                vec!["Head"],
                vec!["Head", "Tail"],
            ]
        );
        // A list is no type: it holds none, and nothing else is one.
        assert_eq!(
            errors("fn(T: ((A, B), C)) f():\n    pass\n"),
            vec![expected("type", TokenKind::LParen)]
        );
        assert_eq!(
            errors("fn f(x: (A, B)):\n    pass\n"),
            vec![expected("type", TokenKind::LParen)]
        );
    }

    #[test]
    fn a_type_parameter_has_a_default_and_a_type_argument_a_label() {
        let src = "struct(T, R: Make = lib.bump, N = tuple(T, u8)) Vec:
    next: &Vec(T, N: i32)
    all: Vec(R: fn(uint), T: u8,)
";
        let module = parse_src(src).unwrap();
        let ItemKind::Struct(vec) = &module.items[0].kind else {
            panic!()
        };
        let defaults: Vec<_> = (vec.params.iter())
            .map(|p| p.default.as_ref().map(render_ty))
            .collect();
        let want = [None, Some("lib.bump"), Some("tuple(T, u8)")];
        assert_eq!(defaults, want.map(|d| d.map(str::to_string)));
        let fields: Vec<_> = (vec.entries.iter().filter_map(Entry::own))
            .map(|field| render_ty(&field.ty))
            .collect();
        assert_eq!(fields, ["&Vec(T, N: i32)", "Vec(R: fn(uint), T: u8)"]);
        // A type is displayed as it is written.
        let ItemKind::Struct(vec) = &module.items[0].kind else {
            panic!()
        };
        let shown: Vec<_> = (vec.entries.iter().filter_map(Entry::own))
            .map(|field| field.ty.to_string())
            .collect();
        assert_eq!(shown, fields);
        // A label is a name, and is followed by a type.
        assert_eq!(
            errors("fn f(x: Vec(u8, R:)):\n    pass\n"),
            vec![expected("type", TokenKind::RParen)]
        );
        assert_eq!(
            errors("struct(T =) S:\n    pass\n"),
            vec![expected("type", TokenKind::RParen)]
        );
    }

    #[test]
    fn type_params() {
        let module =
            parse_src("struct(A, B,) Pair:\n    a: A\n    b: B\nstruct P:\n    pass\n").unwrap();
        let ItemKind::Struct(pair) = &module.items[0].kind else {
            panic!()
        };
        let params: Vec<_> = pair.params.iter().map(|p| p.name.name.as_str()).collect();
        assert_eq!(params, vec!["A", "B"]);
        let ItemKind::Struct(p) = &module.items[1].kind else {
            panic!()
        };
        assert!(p.params.is_empty());

        assert_eq!(
            errors("struct() Box:\n    pass\n"),
            vec![expected("type parameter", TokenKind::RParen)]
        );

        let module = parse_src(
            "struct(A: mod.Head(u8), B) Pair:\n    pass\nfn(T: Head) f(T: type, x: &T):\n    pass\n",
        )
        .unwrap();
        let ItemKind::Struct(pair) = &module.items[0].kind else {
            panic!()
        };
        let bounds = pair.params.iter();
        let bounds: Vec<Vec<_>> = bounds
            .map(|p| p.bound.iter().map(render_ty).collect())
            .collect();
        assert_eq!(bounds, vec![vec!["mod.Head(u8)".to_string()], vec![]]);
        let ItemKind::Fn(f) = &module.items[1].kind else {
            panic!()
        };
        assert!(f.sig.is_generic());
        let names: Vec<_> = f
            .sig
            .type_param_names()
            .into_iter()
            .map(|p| p.name)
            .collect();
        assert_eq!(names, vec!["T", "T"]);
        let bound: Vec<_> = f.sig.type_params[0].bound.iter().map(render_ty).collect();
        assert_eq!(bound, ["Head"]);
    }

    #[test]
    fn generic_fns() {
        let module = parse_src(
            "fn(T, U) pair(a: T, b: U) -> tuple(T, U):\n    return (a, b)\nfn f():\n    pass\n",
        )
        .unwrap();
        let ItemKind::Fn(pair) = &module.items[0].kind else {
            panic!()
        };
        let params: Vec<_> = pair
            .sig
            .type_params
            .iter()
            .map(|p| p.name.name.as_str())
            .collect();
        assert_eq!(params, vec!["T", "U"]);
        assert_eq!(pair.sig.name.name, "pair");
        assert_eq!(render_ty(&pair.sig.params[1].ty), "U");
        let ItemKind::Fn(f) = &module.items[1].kind else {
            panic!()
        };
        assert!(f.sig.type_params.is_empty());

        assert_eq!(
            errors("fn() f():\n    pass\n"),
            vec![expected("type parameter", TokenKind::RParen)]
        );
        assert_eq!(
            errors("extern:\n    fn(T) f(x: T)\n"),
            vec![ParseErrorKind::GenericExtern]
        );
        assert_eq!(
            errors("extern:\n    fn f(T: type, x: &type)\n"),
            vec![ParseErrorKind::GenericExtern]
        );
    }

    #[test]
    fn export_blocks_hold_the_functions_of_an_interface() {
        let src = "pub \"my:pkg/math@0.1.0\":\n    fn add(a: i32, b: i32) -> i32:\n        \
                   return a + b\n    pub fn double_it(n: i32) -> i32 = \"double\":\n        \
                   return n * 2\n\npub fn tick() = \"tick-now\":\n    pass\n\nfn idle():\n    pass\n";
        let module = parse_src(src).unwrap();
        // Each function of a block is an item of the file, as any is.
        let fns = module.items.iter().map(|item| {
            let ItemKind::Fn(f) = &item.kind else {
                panic!()
            };
            let text =
                |ident: &Option<Ident>| ident.as_ref().map(|i| &src[i.span.start..i.span.end]);
            let named = f.export_name.as_ref().map(|name| name.name.as_str());
            (
                (item.is_pub, f.sig.name.name.as_str()),
                (
                    f.interface.as_ref().map(|i| i.name.as_str()),
                    text(&f.interface),
                ),
                (named, text(&f.export_name)),
            )
        });
        let interface = (Some("my:pkg/math@0.1.0"), Some("\"my:pkg/math@0.1.0\""));
        assert_eq!(
            fns.collect::<Vec<_>>(),
            [
                ((false, "add"), interface, (None, None)),
                (
                    (true, "double_it"),
                    interface,
                    (Some("double"), Some("\"double\""))
                ),
                (
                    (true, "tick"),
                    (None, None),
                    (Some("tick-now"), Some("\"tick-now\""))
                ),
                ((false, "idle"), (None, None), (None, None)),
            ]
        );
        let span = module.items[1].span;
        assert!(src[span.start..span.end].starts_with("pub fn double_it"));
        assert!(src[span.start..span.end].ends_with("return n * 2"));

        // A block may hold nothing, as an `extern` block may.
        let empty = parse_src("pub \"a:b/c\":\n    pass\n").unwrap();
        assert!(empty.items.is_empty());

        assert_eq!(
            errors("pub \"a:b/c\":\n    fn(T) f(x: T):\n        pass\n"),
            vec![ParseErrorKind::GenericExport]
        );
        assert_eq!(
            errors("pub \"a:b/c\":\n    fn f(T: type):\n        pass\n"),
            vec![ParseErrorKind::GenericExport]
        );
        assert_eq!(
            errors("pub \"a:b/c\":\n    let x = 1\n"),
            vec![expected("`fn`", TokenKind::Let)]
        );
        // Only an `extern` function has no body.
        assert_eq!(
            errors("pub \"a:b/c\":\n    fn f()\n"),
            vec![ParseErrorKind::MissingFnBody]
        );
        assert_eq!(
            errors("fn f() = \"g\"\n"),
            vec![ParseErrorKind::MissingFnBody]
        );
        assert_eq!(
            errors("use a\nfn f():\n    pass\npub \"a:b/c\":\n    pass\nuse b\n"),
            vec![ParseErrorKind::UseAfterItem]
        );
    }

    #[test]
    fn enums() {
        let src = "\
pub enum(i8) ReturnCode:
    ok
    error = 5 + 1
enum(tuple(u8, u8)) Pair:
    a = (1, 2)
";
        let module = parse_src(src).unwrap();
        assert!(module.items[0].is_pub);
        let decls: Vec<_> = module
            .items
            .iter()
            .map(|item| match &item.kind {
                ItemKind::Enum(e) => e,
                _ => panic!(),
            })
            .collect();
        assert_eq!(decls[0].name.name, "ReturnCode");
        assert_eq!(render_ty(&decls[0].ty), "i8");
        let members: Vec<_> = decls[0].entries.iter().filter_map(Entry::own).collect();
        let values: Vec<_> = members
            .iter()
            .map(|m| (m.name.name.as_str(), m.value.as_ref().map(sexpr)))
            .collect();
        assert_eq!(
            values,
            [("ok", None), ("error", Some("(Add 5 1)".to_string()))]
        );
        let error = members[1];
        assert_eq!(&src[error.span.start..error.span.end], "error = 5 + 1");
        assert_eq!(render_ty(&decls[1].ty), "tuple(u8, u8)");

        assert_eq!(
            errors("enum E:\n    a\n"),
            vec![expected("`(`", TokenKind::Ident("E".into()))]
        );
        assert_eq!(
            errors("enum(i8) E:\n    pub a\n    pass\n"),
            vec![
                expected("identifier", TokenKind::Pub),
                expected("identifier", TokenKind::Pass),
            ]
        );
    }

    #[test]
    fn unions() {
        let src = "\
pub union Shape:
    circle: f32
    rect: tuple(f32, f32)
    empty
union(T, E,) Result:
    ok: T
    err: E
";
        let module = parse_src(src).unwrap();
        assert!(module.items[0].is_pub);
        let decls: Vec<_> = module
            .items
            .iter()
            .map(|item| match &item.kind {
                ItemKind::Union(u) => u,
                _ => panic!(),
            })
            .collect();
        let variants = |decl: &UnionDecl| -> Vec<_> {
            let variants = decl.entries.iter().filter_map(Entry::own);
            variants
                .map(|v| (v.name.name.clone(), v.ty.as_ref().map(render_ty)))
                .collect()
        };
        assert_eq!(decls[0].name.name, "Shape");
        assert!(decls[0].params.is_empty());
        assert_eq!(
            variants(decls[0]),
            [
                ("circle".to_string(), Some("f32".to_string())),
                ("rect".to_string(), Some("tuple(f32, f32)".to_string())),
                ("empty".to_string(), None),
            ]
        );
        let Entry::Own(rect) = &decls[0].entries[1] else {
            panic!()
        };
        assert_eq!(
            &src[rect.span.start..rect.span.end],
            "rect: tuple(f32, f32)"
        );
        let params: Vec<_> = decls[1]
            .params
            .iter()
            .map(|p| p.name.name.as_str())
            .collect();
        assert_eq!(params, vec!["T", "E"]);
        assert_eq!(
            variants(decls[1]),
            [
                ("ok".to_string(), Some("T".to_string())),
                ("err".to_string(), Some("E".to_string())),
            ]
        );

        assert_eq!(
            errors("union U:\n    pub a\n    pass\n    b = 1\n"),
            vec![
                expected("identifier", TokenKind::Pub),
                expected("identifier", TokenKind::Pass),
                expected("newline", TokenKind::Eq),
            ]
        );
        assert_eq!(
            errors("union() U:\n    a\n"),
            vec![expected("type parameter", TokenKind::RParen)]
        );
    }

    #[test]
    fn dot_names() {
        assert_eq!(expr(".red"), ".red");
        assert_eq!(expr(".some(1)"), "(call .some 1)");
        assert_eq!(expr("a == .none"), "(Eq a .none)");
        assert_eq!(expr("f(.a, x: .b(.c))"), "(call f .a x:(call .b .c))");
        assert_eq!(expr(".a.b"), "(. .a b)");
        assert_eq!(
            errors("let _ = .1\n"),
            vec![expected("identifier", TokenKind::Int(1))]
        );
    }

    #[test]
    fn extern_blocks() {
        let src = "\
extern \"js\":
    fn now() -> f64
    fn log(p: &u8, len: i32) = \"console.log\"
extern:
    pass
extern \"\":
    fn f() = \"\"
";
        let module = parse_src(src).unwrap();
        let blocks: Vec<_> = module
            .items
            .iter()
            .map(|item| match &item.kind {
                ItemKind::Extern(block) => block,
                _ => panic!(),
            })
            .collect();
        let module = |block: &ExternBlock| block.module.as_ref().map(|m| m.name.clone());
        assert_eq!(module(blocks[0]).as_deref(), Some("js"));
        let [now, log] = &blocks[0].fns[..] else {
            panic!()
        };
        assert_eq!(now.sig.name.name, "now");
        assert_eq!(render_ty(now.sig.ret.as_ref().unwrap()), "f64");
        assert_eq!(now.import_name, None);
        assert_eq!(&src[now.span.start..now.span.end], "fn now() -> f64");
        assert_eq!(log.sig.params.len(), 2);
        assert_eq!(log.import_name.as_deref(), Some("console.log"));
        assert_eq!(
            &src[log.span.start..log.span.end],
            "fn log(p: &u8, len: i32) = \"console.log\""
        );
        assert_eq!(module(blocks[1]), None);
        assert!(blocks[1].fns.is_empty());
        assert_eq!(module(blocks[2]).as_deref(), Some(""));
        assert_eq!(blocks[2].fns[0].import_name.as_deref(), Some(""));
    }

    #[test]
    fn extern_errors() {
        let src = "\
extern:
    fn a():
        pass
    let c = 1
    fn d() = e
pub extern:
    fn f()
fn g()
fn g2() = \"x\"
fn h() -> i32:
    return 1
";
        assert_eq!(
            errors(src),
            vec![
                ParseErrorKind::ExternFnBody,
                expected("`fn`", TokenKind::Let),
                expected("string", TokenKind::Ident("e".into())),
                ParseErrorKind::PubExtern,
                ParseErrorKind::MissingFnBody,
                ParseErrorKind::MissingFnBody,
            ]
        );
        let spans: Vec<_> = parse_src(src)
            .unwrap_err()
            .iter()
            .map(|e| &src[e.span.start..e.span.end])
            .collect();
        // A name after `=` is what a function with a body is exported as.
        let named = "fn g2() = \"x\"";
        assert_eq!(spans, ["fn a()", "let", "e", "pub", "fn g()", named]);
    }

    #[test]
    fn invalid_assign_target() {
        assert_eq!(
            errors("fn f():\n    g() = 1\n    a + b += 1\n"),
            vec![
                ParseErrorKind::InvalidAssignTarget,
                ParseErrorKind::InvalidAssignTarget
            ]
        );
        // The piped value is not a place.
        assert_eq!(
            errors("fn f():\n    x |> _ = 1\n    x |> _.a += 1\n"),
            vec![
                ParseErrorKind::InvalidAssignTarget,
                ParseErrorKind::InvalidAssignTarget
            ]
        );
    }

    #[test]
    fn recovers_and_reports_every_error() {
        let src = "\
fn a():
    let = 1
    return 2 3
    if x x:
        y +
    else:
        z +
    ok()
fn b(: i32):
    pass
struct C:
    x i32
    y: f32
let d = 1
";
        assert_eq!(
            errors(src),
            vec![
                expected("pattern", TokenKind::Eq),
                expected("newline", TokenKind::Int(3)),
                expected("`:`", TokenKind::Ident("x".into())),
                expected("identifier", TokenKind::Colon),
                expected("`:`", TokenKind::Ident("i32".into())),
            ]
        );
    }

    #[test]
    fn what_parses_of_a_source_with_errors_is_every_line_without_one() {
        let src = "\
fn a():
    let = 1
    b = 1 = 2
    if c:
    d |> e()
    while f:
        g +
        h()
    i()
fn j(: i32):
    pass
struct K:
    l i32
    m: f32
let n = 1
";
        let tokens = tokenize(DummyManager::new().entry_point(), src).unwrap();
        let (module, errors) = parse_partial(&tokens);
        assert_eq!(errors.len(), 7, "{errors:?}");
        let [a, k, n] = &module.items[..] else {
            panic!("{:?}", module.items)
        };
        let ItemKind::Fn(a) = &a.kind else { panic!() };
        // A line with an error is left out with the block under it, and
        // the block it is in is kept.
        assert_eq!(stmt_kinds(&a.body), vec!["while", "expr"]);
        let StmtKind::While { body, .. } = &a.body[0].kind else {
            panic!()
        };
        assert_eq!(stmt_kinds(body), vec!["expr"]);
        let ItemKind::Struct(k) = &k.kind else {
            panic!()
        };
        assert_eq!(k.entries.len(), 1);
        assert!(matches!(n.kind, ItemKind::Binding(_)));
        assert_eq!(parse(&tokens).unwrap_err(), errors);
    }

    #[test]
    fn missing_block() {
        assert_eq!(
            errors("fn f():\nlet x = 1\n"),
            vec![expected("indented block", TokenKind::Let)]
        );
    }

    /// Each path of every `use` in `src`, with `pub` and `as` as written.
    fn uses(src: &str) -> Vec<String> {
        let module = parse_src(src).unwrap();
        let mut uses = Vec::new();
        for item in &module.items {
            let ItemKind::Use(decl) = &item.kind else {
                panic!("{item:?}")
            };
            for path in &decl.paths {
                let names: Vec<_> = path.segments.iter().map(|s| s.name.as_str()).collect();
                let mut text = names.join(".");
                if item.is_pub {
                    text.insert_str(0, "pub ");
                }
                if let Some(alias) = &path.alias {
                    text.push_str(&format!(" as {}", alias.name));
                }
                uses.push(text);
            }
        }
        uses
    }

    #[test]
    fn use_paths() {
        let src = "use util.strings\npub use a.b.c as d\nuse json\nuse json as j\n";
        assert_eq!(
            uses(src),
            ["util.strings", "pub a.b.c as d", "json", "json as j"]
        );
    }

    #[test]
    fn use_groups_are_a_path_for_each_name() {
        let src = "use geo.{Point, len as length}\npub use a.{\n    b.{c, d},\n    e,\n}\n";
        assert_eq!(
            uses(src),
            [
                "geo.Point",
                "geo.len as length",
                "pub a.b.c",
                "pub a.b.d",
                "pub a.e"
            ]
        );
    }

    #[test]
    fn use_errors() {
        assert_eq!(
            errors("use \"a.duck\"\nuse a.\nuse a.{b} as c\nuse {a, b}\n"),
            [
                expected("identifier", TokenKind::Str("a.duck".into())),
                expected("identifier", TokenKind::Newline),
                expected("newline", TokenKind::As),
                expected("identifier", TokenKind::LBrace),
            ]
        );
    }

    #[test]
    fn uses_come_before_other_items() {
        let src = "use a\nlet x = 1\nuse b\nfn f():\n    pass\n";
        assert_eq!(errors(src), [ParseErrorKind::UseAfterItem]);
        let span = parse_src(src).unwrap_err()[0].span;
        assert_eq!(&src[span.start..span.end], "use b");
    }

    #[test]
    fn qualified_types() {
        let module =
            parse_src("fn f(a: json.Value, b: &a.b.List(geo.Point)) -> m.T:\n\tpass").unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(render_ty(&f.sig.params[0].ty), "json.Value");
        assert_eq!(render_ty(&f.sig.params[1].ty), "&a.b.List(geo.Point)");
        assert_eq!(render_ty(f.sig.ret.as_ref().unwrap()), "m.T");
    }

    #[test]
    fn pub_extern_fns() {
        let module = parse_src("extern:\n    pub fn a()\n    fn b()\n").unwrap();
        let ItemKind::Extern(block) = &module.items[0].kind else {
            panic!()
        };
        let fns: Vec<_> = block
            .fns
            .iter()
            .map(|f| (f.is_pub, f.sig.name.name.as_str()))
            .collect();
        assert_eq!(fns, [(true, "a"), (false, "b")]);
    }

    #[test]
    fn unexpected_indent() {
        assert_eq!(
            errors("let a = 1\n    let b = 2\nlet c = 3\n"),
            vec![ParseErrorKind::UnexpectedIndent]
        );
        assert_eq!(
            errors("fn f():\n    a()\n        b()\n    c()\n"),
            vec![ParseErrorKind::UnexpectedIndent]
        );
    }

    #[test]
    fn spans() {
        let src = "fn f():\n    return a + b\n\nlet x = 1\n";
        let module = parse_src(src).unwrap();
        let text = |span: Span| &src[span.start..span.end];
        assert_eq!(text(module.items[0].span), "fn f():\n    return a + b");
        assert_eq!(text(module.items[1].span), "let x = 1");
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        let Some(sum) = returned(&f.body[0]) else {
            panic!()
        };
        assert_eq!(text(sum.span), "a + b");
        assert_eq!(text(f.body[0].span), "return a + b");
    }
}

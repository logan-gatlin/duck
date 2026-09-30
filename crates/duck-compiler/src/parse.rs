use std::fmt;

use crate::lex::{Span, Token, TokenKind};

/// A parsed source file, or a whole program once [`crate::load`] has spliced
/// in the items of every imported file.
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
    Binding(Binding),
    /// `import "path"`, which evaluates the items of another file in its
    /// place. Resolved by [`crate::load`], so later stages never see one.
    Import(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub sig: FnSig,
    pub body: Block,
}

/// `fn name(params) -> ret`, shared by definitions and imports.
#[derive(Debug, Clone, PartialEq)]
pub struct FnSig {
    pub name: Ident,
    pub params: Vec<Param>,
    pub ret: Option<Type>,
}

/// `extern "module":` and the host functions it imports. The module name is
/// optional.
#[derive(Debug, Clone, PartialEq)]
pub struct ExternBlock {
    pub module: Option<String>,
    pub fns: Vec<ExternFn>,
}

/// A bodyless `fn` in an `extern` block, optionally followed by `= "name"` to
/// import it under a different name.
#[derive(Debug, Clone, PartialEq)]
pub struct ExternFn {
    pub sig: FnSig,
    pub import_name: Option<String>,
    pub span: Span,
}

/// A `name: Type` function parameter.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: Ident,
    pub ty: Type,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub struct StructDecl {
    pub name: Ident,
    /// The names of `struct Name(A, B)`'s type parameters, if it has any.
    pub params: Vec<Ident>,
    pub fields: Vec<Field>,
}

/// A `name: Type` struct field, optionally marked `pub`.
#[derive(Debug, Clone, PartialEq)]
pub struct Field {
    pub is_pub: bool,
    pub name: Ident,
    pub ty: Type,
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

/// What a binding assigns its value to.
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

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    /// `Name`, or `Name(A, B)` given a list of type arguments, which may be
    /// empty as in `Name()`. `None` is no list at all.
    Named(String, Option<Vec<Type>>),
    /// `&T`
    Pointer(Box<Type>),
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
    /// `target = value`, or `target op= value` when `op` is set.
    Assign {
        target: Expr,
        op: Option<BinOp>,
        value: Expr,
    },
    Expr(Expr),
    Return(Option<Expr>),
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
    Break,
    Continue,
    Pass,
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
    /// `(a, b)`, with at least two elements.
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Arg>),
    Index(Box<Expr>, Box<Expr>),
    Field(Box<Expr>, Ident),
    /// `pointer.*`
    Deref(Box<Expr>),
    /// `&place`
    AddrOf(Box<Expr>),
    /// `value as Type`
    Cast(Box<Expr>, Type),
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
    /// `pub` on an `extern` block or on a function in one.
    PubExtern,
    /// `pub` on an `import`, which has no names of its own to export.
    PubImport,
    /// `(x,)`, which would be a tuple of one element.
    OneElementTuple,
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
}

/// What a parenthesized list turned out to be.
enum Parens<T> {
    /// `()`
    Empty,
    /// `(x)`
    Group(T),
    /// `(x, y)`
    Tuple(Vec<T>),
}

/// Precedence of `not`, which sits between `and` and the comparisons.
const NOT_PREC: u8 = 3;
const CMP_PREC: u8 = 4;

impl fmt::Display for ParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expected { expected, found } => write!(f, "expected {expected}, found {found}"),
            Self::UnexpectedIndent => write!(f, "unexpected indentation"),
            Self::ChainedComparison => write!(f, "comparison operators cannot be chained"),
            Self::InvalidAssignTarget => write!(f, "invalid assignment target"),
            Self::MissingFnBody => write!(f, "functions outside `extern` blocks need a body"),
            Self::ExternFnBody => write!(f, "functions in `extern` blocks cannot have a body"),
            Self::PubExtern => write!(f, "`extern` blocks and their functions cannot be `pub`"),
            Self::PubImport => write!(f, "`import` cannot be `pub`"),
            Self::OneElementTuple => write!(f, "tuples must have at least two elements"),
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
    let mut parser = Parser {
        tokens,
        pos: 0,
        last_end: 0,
        errors: Vec::new(),
    };
    let module = parser.module();
    if parser.errors.is_empty() {
        Ok(module)
    } else {
        Err(parser.errors)
    }
}

impl<'a> Parser<'a> {
    fn module(&mut self) -> Module {
        let mut items = Vec::new();
        while !self.at(TokenKind::Eof) {
            match self.item() {
                Ok(item) => items.push(item),
                Err(e) => self.recover(e),
            }
        }
        Module { items }
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
            TokenKind::Let | TokenKind::Var => ItemKind::Binding(self.binding()?),
            TokenKind::Import => {
                if is_pub {
                    self.error(ParseErrorKind::PubImport, start);
                }
                self.bump();
                let path = self.string()?;
                self.expect(TokenKind::Newline)?;
                ItemKind::Import(path)
            }
            _ => return Err(self.unexpected("item")),
        };
        Ok(Item {
            is_pub,
            kind,
            span: self.span_from(start),
        })
    }

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        let start = self.peek().span;
        let sig = self.fn_sig()?;
        // `=` would name an import, which only `extern` blocks have.
        if self.at(TokenKind::Newline) || self.at(TokenKind::Eq) {
            return Err(self.error_from(ParseErrorKind::MissingFnBody, start));
        }
        let body = self.block()?;
        Ok(FnDecl { sig, body })
    }

    fn fn_sig(&mut self) -> PResult<FnSig> {
        self.expect(TokenKind::Fn)?;
        let name = self.ident()?;
        self.expect(TokenKind::LParen)?;
        let params = self.comma_list(TokenKind::RParen, Self::param)?;
        let ret = if self.eat(TokenKind::Arrow) {
            Some(self.ty()?)
        } else {
            None
        };
        Ok(FnSig { name, params, ret })
    }

    fn extern_block(&mut self) -> PResult<ExternBlock> {
        self.expect(TokenKind::Extern)?;
        let module = if matches!(self.peek().kind, TokenKind::Str(_)) {
            Some(self.string()?)
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
        if self.eat(TokenKind::Pub) {
            self.error(ParseErrorKind::PubExtern, start);
        }
        let sig = self.fn_sig()?;
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
            sig,
            import_name,
            span,
        })
    }

    fn struct_decl(&mut self) -> PResult<StructDecl> {
        self.expect(TokenKind::Struct)?;
        let name = self.ident()?;
        let mut params = Vec::new();
        if self.eat(TokenKind::LParen) {
            if self.at(TokenKind::RParen) {
                return Err(self.unexpected("type parameter"));
            }
            params = self.comma_list(TokenKind::RParen, Self::ident)?;
        }
        let fields = self.indented(|p| {
            if p.eat(TokenKind::Pass) {
                p.expect(TokenKind::Newline)?;
                return Ok(None);
            }
            let field = p.field()?;
            p.expect(TokenKind::Newline)?;
            Ok(Some(field))
        })?;
        Ok(StructDecl {
            name,
            params,
            fields: fields.into_iter().flatten().collect(),
        })
    }

    fn param(&mut self) -> PResult<Param> {
        let start = self.peek().span;
        let (name, ty) = self.typed_name()?;
        Ok(Param {
            name,
            ty,
            span: self.span_from(start),
        })
    }

    fn field(&mut self) -> PResult<Field> {
        let start = self.peek().span;
        let is_pub = self.eat(TokenKind::Pub);
        let (name, ty) = self.typed_name()?;
        Ok(Field {
            is_pub,
            name,
            ty,
            span: self.span_from(start),
        })
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
                match self.parens(token.span, Self::pattern)? {
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
            TokenKind::Ident(name) => {
                self.bump();
                let args = match self.eat(TokenKind::LParen) {
                    true => Some(self.comma_list(TokenKind::RParen, Self::ty)?),
                    false => None,
                };
                TypeKind::Named(name.clone(), args)
            }
            TokenKind::Amp => {
                self.bump();
                TypeKind::Pointer(Box::new(self.ty()?))
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
            self.errors.push(error);
            return Ok(Vec::new());
        }
        let mut lines = Vec::new();
        while !self.eat(TokenKind::Dedent) && !self.at(TokenKind::Eof) {
            match line(self) {
                Ok(l) => lines.push(l),
                Err(e) => self.recover(e),
            }
        }
        Ok(lines)
    }

    fn stmt(&mut self) -> PResult<Stmt> {
        let start = self.peek().span;
        let kind = match self.peek().kind {
            TokenKind::Let | TokenKind::Var => StmtKind::Binding(self.binding()?),
            TokenKind::If => return self.if_stmt(),
            TokenKind::Return => {
                self.bump();
                let value = if self.at(TokenKind::Newline) {
                    None
                } else {
                    Some(self.expr()?)
                };
                self.expect(TokenKind::Newline)?;
                StmtKind::Return(value)
            }
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
            TokenKind::Break => self.keyword_stmt(StmtKind::Break)?,
            TokenKind::Continue => self.keyword_stmt(StmtKind::Continue)?,
            TokenKind::Pass => self.keyword_stmt(StmtKind::Pass)?,
            _ => self.expr_stmt()?,
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

    fn keyword_stmt(&mut self, kind: StmtKind) -> PResult<StmtKind> {
        self.bump();
        self.expect(TokenKind::Newline)?;
        Ok(kind)
    }

    /// An expression statement or assignment.
    fn expr_stmt(&mut self) -> PResult<StmtKind> {
        let target = self.expr()?;
        let op = match self.peek().kind {
            TokenKind::Eq => None,
            TokenKind::PlusEq => Some(BinOp::Add),
            TokenKind::MinusEq => Some(BinOp::Sub),
            TokenKind::StarEq => Some(BinOp::Mul),
            TokenKind::SlashEq => Some(BinOp::Div),
            TokenKind::PercentEq => Some(BinOp::Rem),
            _ => {
                self.expect(TokenKind::Newline)?;
                return Ok(StmtKind::Expr(target));
            }
        };
        self.bump();
        if !matches!(
            target.kind,
            ExprKind::Name(_) | ExprKind::Field(..) | ExprKind::Index(..) | ExprKind::Deref(_)
        ) {
            self.error(ParseErrorKind::InvalidAssignTarget, target.span);
        }
        let value = self.expr()?;
        self.expect(TokenKind::Newline)?;
        Ok(StmtKind::Assign { target, op, value })
    }

    fn expr(&mut self) -> PResult<Expr> {
        self.binary(0)
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

    /// A unary expression followed by any `as Type` casts, which bind tighter
    /// than binary operators but looser than unary ones.
    fn cast(&mut self) -> PResult<Expr> {
        let mut expr = self.unary()?;
        while self.eat(TokenKind::As) {
            let ty = self.ty()?;
            let span = self.span_from(expr.span);
            expr = Expr {
                kind: ExprKind::Cast(Box::new(expr), ty),
                span,
            };
        }
        Ok(expr)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let wrap: fn(Box<Expr>) -> ExprKind = match self.peek().kind {
            TokenKind::Minus => |e| ExprKind::Unary(UnaryOp::Neg, e),
            TokenKind::Tilde => |e| ExprKind::Unary(UnaryOp::BitNot, e),
            TokenKind::Amp => ExprKind::AddrOf,
            _ => return self.postfix(),
        };
        let start = self.bump().span;
        let operand = self.unary()?;
        Ok(Expr {
            kind: wrap(Box::new(operand)),
            span: self.span_from(start),
        })
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
                    let args = self.comma_list(TokenKind::RParen, Self::arg)?;
                    ExprKind::Call(Box::new(expr), args)
                }
                TokenKind::LBracket => {
                    self.bump();
                    let index = self.expr()?;
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
            TokenKind::Ident(name) => ExprKind::Name(name.clone()),
            TokenKind::LParen => {
                self.bump();
                let kind = match self.parens(token.span, Self::expr)? {
                    Parens::Empty => ExprKind::Unit,
                    Parens::Group(inner) => inner.kind,
                    Parens::Tuple(items) => ExprKind::Tuple(items),
                };
                return Ok(Expr {
                    kind,
                    span: self.span_from(token.span),
                });
            }
            TokenKind::LBracket => {
                self.bump();
                let items = self.comma_list(TokenKind::RBracket, Self::expr)?;
                return Ok(Expr {
                    kind: ExprKind::List(items),
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

    /// Parses the rest of a parenthesized list after the `(` at `start`. A
    /// trailing comma makes a tuple, except after a single item.
    fn parens<T>(
        &mut self,
        start: Span,
        mut item: impl FnMut(&mut Self) -> PResult<T>,
    ) -> PResult<Parens<T>> {
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
        if items.len() == 1 {
            self.error(ParseErrorKind::OneElementTuple, self.span_from(start));
            return Ok(Parens::Group(items.pop().unwrap()));
        }
        Ok(Parens::Tuple(items))
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

    /// Records an error that doesn't stop the current line from parsing.
    fn error(&mut self, kind: ParseErrorKind, span: Span) {
        self.errors.push(ParseError { kind, span });
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
            ExprKind::Tuple(items) => format!("(tuple {})", list(items)),
            ExprKind::List(items) => format!("[{}]", list(items)),
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
            ExprKind::AddrOf(e) => format!("(& {})", sexpr(e)),
            ExprKind::Cast(e, ty) => format!("(as {} {})", sexpr(e), render_ty(ty)),
        }
    }

    fn render_ty(ty: &Type) -> String {
        match &ty.kind {
            TypeKind::Named(name, None) => name.clone(),
            TypeKind::Named(name, Some(args)) => {
                let args: Vec<_> = args.iter().map(render_ty).collect();
                format!("{name}({})", args.join(", "))
            }
            TypeKind::Pointer(pointee) => format!("&{}", render_ty(pointee)),
        }
    }

    fn stmt_kinds(body: &Block) -> Vec<&'static str> {
        body.iter()
            .map(|s| match s.kind {
                StmtKind::Binding(_) => "binding",
                StmtKind::Assign { .. } => "assign",
                StmtKind::Expr(_) => "expr",
                StmtKind::Return(_) => "return",
                StmtKind::If { .. } => "if",
                StmtKind::While { .. } => "while",
                StmtKind::For { .. } => "for",
                StmtKind::Break => "break",
                StmtKind::Continue => "continue",
                StmtKind::Pass => "pass",
            })
            .collect()
    }

    fn named(name: &str) -> TypeKind {
        TypeKind::Named(name.to_string(), None)
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
            .fields
            .iter()
            .map(|f| (f.name.name.as_str(), f.ty.kind.clone()))
            .collect();
        assert_eq!(fields, vec![("x", named("f32")), ("y", named("f32"))]);

        let ItemKind::Fn(add) = &add.kind else {
            panic!()
        };
        assert_eq!(add.sig.name.name, "add");
        assert_eq!(add.sig.params.len(), 2);
        assert_eq!(add.sig.ret.as_ref().unwrap().kind, named("i32"));
        let StmtKind::Return(Some(sum)) = &add.body[0].kind else {
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
        let src = "fn f(p: &P) -> &array(i32):\n    p.* = 1\n    p.*.x += 1\n    p.*= 2\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(render_ty(&f.sig.params[0].ty), "&P");
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
        assert_eq!(
            errors("let _ = (1,)\n"),
            vec![ParseErrorKind::OneElementTuple]
        );
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
        let render = |p: &Pattern| -> String {
            fn go(p: &Pattern) -> String {
                match &p.kind {
                    PatternKind::Name(name) => name.clone(),
                    PatternKind::Discard => "_".to_string(),
                    PatternKind::Tuple(elems) => {
                        let elems: Vec<_> = elems.iter().map(go).collect();
                        format!("({})", elems.join(" "))
                    }
                }
            }
            go(p)
        };
        assert_eq!(render(&pattern("let x = 1\n")), "x");
        assert_eq!(render(&pattern("let _ = 1\n")), "_");
        assert_eq!(render(&pattern("var (a, _) = t\n")), "(a _)");
        assert_eq!(render(&pattern("let ((a, b), (c)) = t\n")), "((a b) c)");
        assert_eq!(render(&pattern("let () = t\n")), "()");
        assert_eq!(render(&pattern("let (a, b): tuple(u8, u8) = t\n")), "(a b)");
        assert_eq!(
            errors("let (a,) = t\n"),
            vec![ParseErrorKind::OneElementTuple]
        );
        assert_eq!(
            errors("let 1 = t\n"),
            vec![expected("pattern", TokenKind::Int(1))]
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
                StmtKind::Assign { op, .. } => *op,
                _ => unreachable!(),
            })
            .collect();
        assert_eq!(ops, vec![None, Some(BinOp::Add), Some(BinOp::Rem)]);
        assert_eq!(f.body[4].kind, StmtKind::Return(None));

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
    fn field_visibility() {
        let src = "struct P:\n    pub x: f32\n    y: f32\n";
        let module = parse_src(src).unwrap();
        let ItemKind::Struct(p) = &module.items[0].kind else {
            panic!()
        };
        let fields: Vec<_> = p
            .fields
            .iter()
            .map(|f| (f.is_pub, f.name.name.as_str()))
            .collect();
        assert_eq!(fields, vec![(true, "x"), (false, "y")]);
        let span = p.fields[0].span;
        assert_eq!(&src[span.start..span.end], "pub x: f32");

        assert_eq!(
            errors("fn f(pub x: i32):\n    pass\n"),
            vec![expected("identifier", TokenKind::Pub)]
        );
    }

    #[test]
    fn empty_struct() {
        let module = parse_src("struct Unit:\n    pass\n").unwrap();
        let ItemKind::Struct(unit) = &module.items[0].kind else {
            panic!()
        };
        assert!(unit.fields.is_empty());
    }

    #[test]
    fn type_params() {
        let module =
            parse_src("struct Pair(A, B,):\n    a: A\n    b: B\nstruct P:\n    pass\n").unwrap();
        let ItemKind::Struct(pair) = &module.items[0].kind else {
            panic!()
        };
        let params: Vec<_> = pair.params.iter().map(|p| p.name.as_str()).collect();
        assert_eq!(params, vec!["A", "B"]);
        let ItemKind::Struct(p) = &module.items[1].kind else {
            panic!()
        };
        assert!(p.params.is_empty());

        assert_eq!(
            errors("struct Box():\n    pass\n"),
            vec![expected("type parameter", TokenKind::RParen)]
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
        assert_eq!(blocks[0].module.as_deref(), Some("js"));
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
        assert_eq!(blocks[1].module, None);
        assert!(blocks[1].fns.is_empty());
        assert_eq!(blocks[2].module.as_deref(), Some(""));
        assert_eq!(blocks[2].fns[0].import_name.as_deref(), Some(""));
    }

    #[test]
    fn extern_errors() {
        let src = "\
extern:
    fn a():
        pass
    pub fn b()
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
                ParseErrorKind::PubExtern,
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
        assert_eq!(
            spans,
            ["fn a()", "pub", "let", "e", "pub", "fn g()", "fn g2()"]
        );
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
    fn missing_block() {
        assert_eq!(
            errors("fn f():\nlet x = 1\n"),
            vec![expected("indented block", TokenKind::Let)]
        );
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
        let StmtKind::Return(Some(sum)) = &f.body[0].kind else {
            panic!()
        };
        assert_eq!(text(sum.span), "a + b");
        assert_eq!(text(f.body[0].span), "return a + b");
    }
}

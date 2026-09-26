use std::fmt;

use crate::lex::{Span, Token, TokenKind};

/// A parsed source file.
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
    Struct(StructDecl),
    Binding(Binding),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub name: Ident,
    pub params: Vec<Param>,
    pub ret: Option<Type>,
    pub body: Block,
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

/// `let name: Type = value` or `var name: Type = value`. The type is optional.
#[derive(Debug, Clone, PartialEq)]
pub struct Binding {
    pub mutability: Mutability,
    pub name: Ident,
    pub ty: Option<Type>,
    pub value: Expr,
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
    Named(String),
    /// `[T]`
    Array(Box<Type>),
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
    Name(String),
    List(Vec<Expr>),
    Unary(UnaryOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Call(Box<Expr>, Vec<Arg>),
    Index(Box<Expr>, Box<Expr>),
    Field(Box<Expr>, Ident),
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
    Expected { expected: String, found: TokenKind },
    UnexpectedIndent,
    ChainedComparison,
    InvalidAssignTarget,
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
            TokenKind::Struct => ItemKind::Struct(self.struct_decl()?),
            TokenKind::Let | TokenKind::Var => ItemKind::Binding(self.binding()?),
            _ => return Err(self.unexpected("item")),
        };
        Ok(Item {
            is_pub,
            kind,
            span: self.span_from(start),
        })
    }

    fn fn_decl(&mut self) -> PResult<FnDecl> {
        self.expect(TokenKind::Fn)?;
        let name = self.ident()?;
        self.expect(TokenKind::LParen)?;
        let params = self.comma_list(TokenKind::RParen, Self::param)?;
        let ret = if self.eat(TokenKind::Arrow) {
            Some(self.ty()?)
        } else {
            None
        };
        let body = self.block()?;
        Ok(FnDecl {
            name,
            params,
            ret,
            body,
        })
    }

    fn struct_decl(&mut self) -> PResult<StructDecl> {
        self.expect(TokenKind::Struct)?;
        let name = self.ident()?;
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
        let name = self.ident()?;
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
            name,
            ty,
            value,
        })
    }

    fn ty(&mut self) -> PResult<Type> {
        let token = self.peek();
        let kind = match &token.kind {
            TokenKind::Ident(name) => {
                self.bump();
                TypeKind::Named(name.clone())
            }
            TokenKind::LBracket => {
                self.bump();
                let elem = self.ty()?;
                self.expect(TokenKind::RBracket)?;
                TypeKind::Array(Box::new(elem))
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
            ExprKind::Name(_) | ExprKind::Field(..) | ExprKind::Index(..)
        ) {
            self.errors.push(ParseError {
                kind: ParseErrorKind::InvalidAssignTarget,
                span: target.span,
            });
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
                self.errors.push(ParseError {
                    kind: ParseErrorKind::ChainedComparison,
                    span: self.peek().span,
                });
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
        let op = match self.peek().kind {
            TokenKind::Minus => UnaryOp::Neg,
            TokenKind::Tilde => UnaryOp::BitNot,
            _ => return self.postfix(),
        };
        let start = self.bump().span;
        let operand = self.unary()?;
        Ok(Expr {
            kind: ExprKind::Unary(op, Box::new(operand)),
            span: self.span_from(start),
        })
    }

    /// A primary expression followed by any calls, indexing, or field access.
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
                    let field = self.ident()?;
                    ExprKind::Field(Box::new(expr), field)
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
                let inner = self.expr()?;
                self.expect(TokenKind::RParen)?;
                return Ok(Expr {
                    kind: inner.kind,
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
        let tokens = tokenize(DummyManager::entry_point(), src).unwrap();
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
            ExprKind::Name(name) => name.clone(),
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
            ExprKind::Cast(e, ty) => format!("(as {} {})", sexpr(e), render_ty(ty)),
        }
    }

    fn render_ty(ty: &Type) -> String {
        match &ty.kind {
            TypeKind::Named(name) => name.clone(),
            TypeKind::Array(elem) => format!("[{}]", render_ty(elem)),
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
        TypeKind::Named(name.to_string())
    }

    #[test]
    fn example_program() {
        let module = parse_src(include_str!("../example.duck")).unwrap();
        let [global, counter, point, add, main] = &module.items[..] else {
            panic!("expected 5 items, got {:#?}", module.items);
        };
        assert!(module.items.iter().all(|item| item.is_pub));

        let ItemKind::Binding(global) = &global.kind else {
            panic!()
        };
        assert_eq!(global.mutability, Mutability::Let);
        assert_eq!(global.name.name, "global");
        assert_eq!(global.value.kind, ExprKind::Bool(true));

        let ItemKind::Binding(counter) = &counter.kind else {
            panic!()
        };
        assert_eq!(counter.mutability, Mutability::Var);
        assert_eq!(counter.value.kind, ExprKind::Int(0));

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
        assert_eq!(add.name.name, "add");
        assert_eq!(add.params.len(), 2);
        assert_eq!(add.ret.as_ref().unwrap().kind, named("i32"));
        let StmtKind::Return(Some(sum)) = &add.body[0].kind else {
            panic!()
        };
        assert_eq!(sexpr(sum), "(Add a b)");

        let ItemKind::Fn(main) = &main.kind else {
            panic!()
        };
        assert_eq!(main.ret, None);
        assert_eq!(
            stmt_kinds(&main.body),
            vec!["binding", "binding", "binding", "binding", "while", "while"]
        );
        let StmtKind::While { cond, body } = &main.body[4].kind else {
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
    fn labelled_args() {
        assert_eq!(expr("Point(x: 1, y: 2)"), "(call Point x:1 y:2)");
        assert_eq!(expr("f(1, b: c)"), "(call f 1 b:c)");
        assert_eq!(expr("f(a == b)"), "(call f (Eq a b))");
    }

    #[test]
    fn literals() {
        assert_eq!(expr("[]"), "[]");
        assert_eq!(expr("[1, 2,]"), "[1 2]");
        assert_eq!(
            expr(r#"[1.5, "hi", true, false]"#),
            r#"[1.5 "hi" true false]"#
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
        let module = parse_src("fn f(xs: [[i32]], n: u8,) -> [f32]:\n\tpass").unwrap();
        let ItemKind::Fn(f) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(render_ty(&f.params[0].ty), "[[i32]]");
        assert_eq!(render_ty(&f.params[1].ty), "u8");
        assert_eq!(render_ty(f.ret.as_ref().unwrap()), "[f32]");

        let module = parse_src("let x: i32 = 1").unwrap();
        let ItemKind::Binding(x) = &module.items[0].kind else {
            panic!()
        };
        assert_eq!(x.ty.as_ref().unwrap().kind, named("i32"));
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
                expected("identifier", TokenKind::Eq),
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

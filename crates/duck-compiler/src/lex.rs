use std::fmt;

use crate::file::FileId;

/// Byte range `start..end` into the contents of `file`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // Literals
    Ident(String),
    Int(u64),
    Float(f64),
    Str(String),

    // Keywords
    Pub,
    Fn,
    Let,
    Var,
    Return,
    If,
    Else,
    While,
    For,
    In,
    Break,
    Continue,
    Pass,
    Match,
    Struct,
    Enum,
    Union,
    Extern,
    Use,
    Module,
    And,
    Or,
    Not,
    True,
    False,
    As,
    /// `as!`
    AsUnchecked,

    // Delimiters
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Semi,
    Dot,
    /// `.*`, lexed as one token so that `p.*= 1` isn't `p.` then `*=`.
    DotStar,
    Arrow,

    // Operators
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Amp,
    Pipe,
    /// `|>`
    PipeArrow,
    Caret,
    Tilde,
    Shl,
    Shr,
    Eq,
    EqEq,
    NotEq,
    Lt,
    Le,
    Gt,
    Ge,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,

    // Layout
    Newline,
    Indent,
    Dedent,
    Eof,
}

#[derive(Debug, Clone, PartialEq)]
pub struct LexError {
    pub kind: LexErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum LexErrorKind {
    UnexpectedChar(char),
    UnterminatedString,
    InvalidEscape,
    InvalidNumber,
    IntTooLarge,
    InconsistentIndent,
    UnmatchedClose(char),
    MismatchedClose { expected: char, found: char },
    Unclosed(char),
}

struct Lexer<'a> {
    file: FileId,
    src: &'a str,
    pos: usize,
    tokens: Vec<Token>,
    /// Indentation strings of each open block; the bottom is always `""`.
    indents: Vec<&'a str>,
    /// Open brackets. Newlines and indentation are ignored while non-empty.
    brackets: Vec<(char, Span)>,
    at_line_start: bool,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let symbol = match self {
            Self::Ident(name) => return write!(f, "`{name}`"),
            Self::Int(n) => return write!(f, "`{n}`"),
            Self::Float(x) => return write!(f, "`{x}`"),
            Self::Str(s) => return write!(f, "{s:?}"),
            Self::Newline => return write!(f, "newline"),
            Self::Indent => return write!(f, "indent"),
            Self::Dedent => return write!(f, "dedent"),
            Self::Eof => return write!(f, "end of file"),
            Self::Pub => "pub",
            Self::Fn => "fn",
            Self::Let => "let",
            Self::Var => "var",
            Self::Return => "return",
            Self::If => "if",
            Self::Else => "else",
            Self::While => "while",
            Self::For => "for",
            Self::In => "in",
            Self::Break => "break",
            Self::Continue => "continue",
            Self::Pass => "pass",
            Self::Match => "match",
            Self::Struct => "struct",
            Self::Enum => "enum",
            Self::Union => "union",
            Self::Extern => "extern",
            Self::Use => "use",
            Self::Module => "module",
            Self::And => "and",
            Self::Or => "or",
            Self::Not => "not",
            Self::True => "true",
            Self::False => "false",
            Self::As => "as",
            Self::AsUnchecked => "as!",
            Self::LParen => "(",
            Self::RParen => ")",
            Self::LBracket => "[",
            Self::RBracket => "]",
            Self::LBrace => "{",
            Self::RBrace => "}",
            Self::Comma => ",",
            Self::Colon => ":",
            Self::Semi => ";",
            Self::Dot => ".",
            Self::DotStar => ".*",
            Self::Arrow => "->",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::Percent => "%",
            Self::Amp => "&",
            Self::Pipe => "|",
            Self::PipeArrow => "|>",
            Self::Caret => "^",
            Self::Tilde => "~",
            Self::Shl => "<<",
            Self::Shr => ">>",
            Self::Eq => "=",
            Self::EqEq => "==",
            Self::NotEq => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::PlusEq => "+=",
            Self::MinusEq => "-=",
            Self::StarEq => "*=",
            Self::SlashEq => "/=",
            Self::PercentEq => "%=",
        };
        write!(f, "`{symbol}`")
    }
}

impl fmt::Display for LexErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedChar(c) => write!(f, "unexpected character {c:?}"),
            Self::UnterminatedString => write!(f, "unterminated string literal"),
            Self::InvalidEscape => write!(f, "invalid escape sequence"),
            Self::InvalidNumber => write!(f, "invalid number literal"),
            Self::IntTooLarge => write!(f, "integer literal is too large"),
            Self::InconsistentIndent => {
                write!(f, "indentation does not match any enclosing block")
            }
            Self::UnmatchedClose(c) => write!(f, "unmatched closing {c:?}"),
            Self::MismatchedClose { expected, found } => {
                write!(f, "expected {expected:?}, found {found:?}")
            }
            Self::Unclosed(c) => write!(f, "unclosed {c:?}"),
        }
    }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}..{}", self.kind, self.span.start, self.span.end)
    }
}

impl std::error::Error for LexError {}

/// Converts source text into tokens.
///
/// Layout is made explicit: every logical line ends in `Newline`, and changes
/// in leading whitespace produce `Indent`/`Dedent`. Blank and comment-only
/// lines are ignored, as are line breaks inside brackets and before a deeper
/// line that starts with `|>`. The stream always ends with `Eof`, preceded by
/// a `Dedent` for each block still open.
pub fn tokenize(file: FileId, src: &str) -> Result<Vec<Token>, LexError> {
    Lexer {
        file,
        src,
        pos: 0,
        tokens: Vec::new(),
        indents: vec![""],
        brackets: Vec::new(),
        at_line_start: true,
    }
    .run()
}

/// Whether `s` is an identifier: one that isn't a keyword.
pub fn is_identifier(s: &str) -> bool {
    let Ok(tokens) = tokenize(FileId::default(), s) else {
        return false;
    };
    matches!(&tokens[..], [first, rest @ ..]
        if first.kind == TokenKind::Ident(s.to_string())
            && rest.iter().all(|t| matches!(t.kind, TokenKind::Newline | TokenKind::Eof)))
}

impl<'a> Lexer<'a> {
    fn run(mut self) -> Result<Vec<Token>, LexError> {
        loop {
            if self.at_line_start {
                self.indentation()?;
            }
            self.skip_whitespace();
            let start = self.pos;
            let Some(c) = self.bump() else { break };
            let kind = match c {
                '\n' | '\r' => {
                    if c == '\r' {
                        self.eat('\n');
                    }
                    if self.brackets.is_empty() {
                        self.push(TokenKind::Newline, start);
                        self.at_line_start = true;
                    }
                    continue;
                }
                '"' => self.string(start)?,
                '0'..='9' if self.after(TokenKind::Dot) => self.tuple_index(start)?,
                '0'..='9' => self.number(start)?,
                c if is_ident_start(c) => self.ident(start),

                '(' | '[' | '{' => {
                    self.brackets.push((c, self.span(start)));
                    match c {
                        '(' => TokenKind::LParen,
                        '[' => TokenKind::LBracket,
                        _ => TokenKind::LBrace,
                    }
                }
                ')' | ']' | '}' => {
                    self.close_bracket(c, start)?;
                    match c {
                        ')' => TokenKind::RParen,
                        ']' => TokenKind::RBracket,
                        _ => TokenKind::RBrace,
                    }
                }

                ',' => TokenKind::Comma,
                ':' => TokenKind::Colon,
                ';' => TokenKind::Semi,
                '.' if self.eat('*') => TokenKind::DotStar,
                '.' => TokenKind::Dot,
                '&' => TokenKind::Amp,
                '|' if self.eat('>') => TokenKind::PipeArrow,
                '|' => TokenKind::Pipe,
                '^' => TokenKind::Caret,
                '~' => TokenKind::Tilde,
                '+' if self.eat('=') => TokenKind::PlusEq,
                '+' => TokenKind::Plus,
                '-' if self.eat('>') => TokenKind::Arrow,
                '-' if self.eat('=') => TokenKind::MinusEq,
                '-' => TokenKind::Minus,
                '*' if self.eat('=') => TokenKind::StarEq,
                '*' => TokenKind::Star,
                '/' if self.eat('=') => TokenKind::SlashEq,
                '/' => TokenKind::Slash,
                '%' if self.eat('=') => TokenKind::PercentEq,
                '%' => TokenKind::Percent,
                '=' if self.eat('=') => TokenKind::EqEq,
                '=' => TokenKind::Eq,
                '!' if self.eat('=') => TokenKind::NotEq,
                '<' if self.eat('<') => TokenKind::Shl,
                '<' if self.eat('=') => TokenKind::Le,
                '<' => TokenKind::Lt,
                '>' if self.eat('>') => TokenKind::Shr,
                '>' if self.eat('=') => TokenKind::Ge,
                '>' => TokenKind::Gt,

                c => return Err(self.error(LexErrorKind::UnexpectedChar(c), start)),
            };
            self.push(kind, start);
        }
        self.finish()
    }

    /// Consumes blank lines and leading whitespace at the start of a line,
    /// emitting `Indent`/`Dedent` tokens as needed. A line that starts with
    /// `|>` and is indented deeper than its block continues the line above
    /// instead, which takes back that line's `Newline`.
    fn indentation(&mut self) -> Result<(), LexError> {
        let src = self.src;
        let start = loop {
            let line_start = self.pos;
            while matches!(self.peek(), Some(' ' | '\t')) {
                self.bump();
            }
            if self.peek() == Some('#') {
                self.skip_comment();
            }
            match self.peek() {
                None => return Ok(()),
                Some('\n') => {
                    self.bump();
                }
                Some('\r') => {
                    self.bump();
                    self.eat('\n');
                }
                Some(_) => break line_start,
            }
        };
        self.at_line_start = false;

        let indent = &src[start..self.pos];
        let mut dedented = false;
        loop {
            let top = *self.indents.last().unwrap();
            if indent == top {
                return Ok(());
            }
            if !dedented && indent.starts_with(top) {
                if src[self.pos..].starts_with("|>") && self.after(TokenKind::Newline) {
                    self.tokens.pop();
                    return Ok(());
                }
                self.indents.push(indent);
                self.push(TokenKind::Indent, start);
                return Ok(());
            }
            if top.starts_with(indent) {
                self.indents.pop();
                self.push(TokenKind::Dedent, self.pos);
                dedented = true;
                continue;
            }
            return Err(self.error(LexErrorKind::InconsistentIndent, start));
        }
    }

    fn finish(mut self) -> Result<Vec<Token>, LexError> {
        if let Some(&(c, span)) = self.brackets.last() {
            return Err(LexError {
                kind: LexErrorKind::Unclosed(c),
                span,
            });
        }
        if self
            .tokens
            .last()
            .is_some_and(|t| t.kind != TokenKind::Newline)
        {
            self.push(TokenKind::Newline, self.pos);
        }
        while self.indents.len() > 1 {
            self.indents.pop();
            self.push(TokenKind::Dedent, self.pos);
        }
        self.push(TokenKind::Eof, self.pos);
        Ok(self.tokens)
    }

    fn close_bracket(&mut self, found: char, start: usize) -> Result<(), LexError> {
        let Some((open, _)) = self.brackets.pop() else {
            return Err(self.error(LexErrorKind::UnmatchedClose(found), start));
        };
        let expected = match open {
            '(' => ')',
            '[' => ']',
            _ => '}',
        };
        if found != expected {
            return Err(self.error(LexErrorKind::MismatchedClose { expected, found }, start));
        }
        Ok(())
    }

    fn ident(&mut self, start: usize) -> TokenKind {
        while self.peek().is_some_and(is_ident_continue) {
            self.bump();
        }
        match &self.src[start..self.pos] {
            "pub" => TokenKind::Pub,
            "fn" => TokenKind::Fn,
            "let" => TokenKind::Let,
            "var" => TokenKind::Var,
            "return" => TokenKind::Return,
            "if" => TokenKind::If,
            "else" => TokenKind::Else,
            "while" => TokenKind::While,
            "for" => TokenKind::For,
            "in" => TokenKind::In,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "pass" => TokenKind::Pass,
            "match" => TokenKind::Match,
            "struct" => TokenKind::Struct,
            "enum" => TokenKind::Enum,
            "union" => TokenKind::Union,
            "extern" => TokenKind::Extern,
            "use" => TokenKind::Use,
            "module" => TokenKind::Module,
            "and" => TokenKind::And,
            "or" => TokenKind::Or,
            "not" => TokenKind::Not,
            "true" => TokenKind::True,
            "false" => TokenKind::False,
            "as" if self.eat('!') => TokenKind::AsUnchecked,
            "as" => TokenKind::As,
            name => TokenKind::Ident(name.to_string()),
        }
    }

    /// Lexes an integer (decimal, `0x`, `0o`, `0b`) or decimal float. The
    /// first digit has already been consumed. `_` may be used as a separator.
    fn number(&mut self, start: usize) -> Result<TokenKind, LexError> {
        let first = self.src.as_bytes()[start];
        let radix = match self.peek() {
            Some('x' | 'X') if first == b'0' => 16,
            Some('o' | 'O') if first == b'0' => 8,
            Some('b' | 'B') if first == b'0' => 2,
            _ => 10,
        };

        if radix != 10 {
            self.bump();
            let digits_start = self.pos;
            self.skip_ident_chars();
            let digits = self.src[digits_start..self.pos].replace('_', "");
            if digits.is_empty() {
                return Err(self.error(LexErrorKind::InvalidNumber, start));
            }
            return self.parse_int(&digits, radix, start);
        }

        self.skip_digits();
        let mut is_float = false;
        if self.peek() == Some('.') && self.peek_nth(1).is_some_and(|c| c.is_ascii_digit()) {
            is_float = true;
            self.bump();
            self.skip_digits();
        }
        if matches!(self.peek(), Some('e' | 'E')) {
            let sign = matches!(self.peek_nth(1), Some('+' | '-')) as usize;
            if self.peek_nth(1 + sign).is_some_and(|c| c.is_ascii_digit()) {
                is_float = true;
                for _ in 0..1 + sign {
                    self.bump();
                }
                self.skip_digits();
            }
        }
        if self.peek().is_some_and(is_ident_continue) {
            self.skip_ident_chars();
            return Err(self.error(LexErrorKind::InvalidNumber, start));
        }

        let text = self.src[start..self.pos].replace('_', "");
        if is_float {
            text.parse()
                .map(TokenKind::Float)
                .map_err(|_| self.error(LexErrorKind::InvalidNumber, start))
        } else {
            self.parse_int(&text, 10, start)
        }
    }

    /// Lexes the index in `tuple.0`, which is plain decimal without leading
    /// zeros, so that `t.0.1` isn't `t.` then `0.1`. The first digit has
    /// already been consumed.
    fn tuple_index(&mut self, start: usize) -> Result<TokenKind, LexError> {
        while self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.bump();
        }
        let digits = &self.src[start..self.pos];
        if (digits.len() > 1 && digits.starts_with('0'))
            || self.peek().is_some_and(is_ident_continue)
        {
            self.skip_ident_chars();
            return Err(self.error(LexErrorKind::InvalidNumber, start));
        }
        self.parse_int(digits, 10, start)
    }

    fn parse_int(&self, digits: &str, radix: u32, start: usize) -> Result<TokenKind, LexError> {
        use std::num::IntErrorKind;
        u64::from_str_radix(digits, radix)
            .map(TokenKind::Int)
            .map_err(|e| {
                let kind = match e.kind() {
                    IntErrorKind::PosOverflow => LexErrorKind::IntTooLarge,
                    _ => LexErrorKind::InvalidNumber,
                };
                self.error(kind, start)
            })
    }

    /// Lexes a string literal. The opening quote has already been consumed.
    fn string(&mut self, start: usize) -> Result<TokenKind, LexError> {
        let mut value = String::new();
        loop {
            let c = match self.peek() {
                None | Some('\n' | '\r') => {
                    return Err(self.error(LexErrorKind::UnterminatedString, start));
                }
                Some(c) => c,
            };
            let escape_start = self.pos;
            self.bump();
            match c {
                '"' => return Ok(TokenKind::Str(value)),
                '\\' => {
                    let escaped = self
                        .escape()
                        .ok_or_else(|| self.error(LexErrorKind::InvalidEscape, escape_start))?;
                    value.push(escaped);
                }
                c => value.push(c),
            }
        }
    }

    /// Decodes the escape after a `\`: `\n \r \t \0 \\ \" \'` or `\u{XXXX}`.
    fn escape(&mut self) -> Option<char> {
        let c = match self.bump()? {
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            '0' => '\0',
            '\\' => '\\',
            '"' => '"',
            '\'' => '\'',
            'u' => {
                if !self.eat('{') {
                    return None;
                }
                let hex_start = self.pos;
                while self.peek().is_some_and(|c| c.is_ascii_hexdigit()) {
                    self.bump();
                }
                let hex = &self.src[hex_start..self.pos];
                if !self.eat('}') || hex.is_empty() || hex.len() > 6 {
                    return None;
                }
                char::from_u32(u32::from_str_radix(hex, 16).ok()?)?
            }
            _ => return None,
        };
        Some(c)
    }

    fn skip_whitespace(&mut self) {
        while matches!(self.peek(), Some(' ' | '\t')) {
            self.bump();
        }
        if self.peek() == Some('#') {
            self.skip_comment();
        }
    }

    fn skip_comment(&mut self) {
        while !matches!(self.peek(), None | Some('\n' | '\r')) {
            self.bump();
        }
    }

    fn skip_digits(&mut self) {
        while self.peek().is_some_and(|c| c.is_ascii_digit() || c == '_') {
            self.bump();
        }
    }

    fn skip_ident_chars(&mut self) {
        while self.peek().is_some_and(is_ident_continue) {
            self.bump();
        }
    }

    fn peek(&self) -> Option<char> {
        self.src[self.pos..].chars().next()
    }

    fn peek_nth(&self, n: usize) -> Option<char> {
        self.src[self.pos..].chars().nth(n)
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.pos += c.len_utf8();
        Some(c)
    }

    fn eat(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn span(&self, start: usize) -> Span {
        Span {
            file: self.file,
            start,
            end: self.pos,
        }
    }

    /// Whether the last token pushed is `kind`.
    fn after(&self, kind: TokenKind) -> bool {
        self.tokens.last().is_some_and(|t| t.kind == kind)
    }

    fn push(&mut self, kind: TokenKind, start: usize) {
        let span = self.span(start);
        self.tokens.push(Token { kind, span });
    }

    fn error(&self, kind: LexErrorKind, start: usize) -> LexError {
        LexError {
            kind,
            span: self.span(start),
        }
    }
}

fn is_ident_start(c: char) -> bool {
    c == '_' || c.is_alphabetic()
}

fn is_ident_continue(c: char) -> bool {
    c == '_' || c.is_alphanumeric()
}

#[cfg(test)]
mod tests {
    use super::TokenKind::*;
    use super::*;
    use crate::file::{DummyManager, FileManager};

    fn lex(src: &str) -> Result<Vec<Token>, LexError> {
        tokenize(DummyManager::new().entry_point(), src)
    }

    fn kinds(src: &str) -> Vec<TokenKind> {
        lex(src).unwrap().into_iter().map(|t| t.kind).collect()
    }

    fn ident(name: &str) -> TokenKind {
        Ident(name.to_string())
    }

    fn error(src: &str) -> LexErrorKind {
        lex(src).unwrap_err().kind
    }

    #[test]
    fn example_program() {
        let src = include_str!("../example.duck");
        #[rustfmt::skip]
        let expected = vec![
            Extern, Colon, Newline,
            Indent, Fn, ident("logi"), LParen, ident("num"), Colon, ident("i32"), RParen, Newline,
            Fn, ident("logf"), LParen, ident("num"), Colon, ident("f32"), RParen,
                Eq, Str("log_f32".to_string()), Newline,
            Fn, ident("logs"), LParen, ident("text"), Colon, ident("array"), LParen, ident("u8"),
                RParen, RParen, Eq, Str("log_str".to_string()), Newline,
            Dedent, Pub, Let, ident("global"), Eq, True, Newline,
            Pub, Var, ident("counter"), Eq, Int(0), Newline,
            Pub, Let, ident("greeting"), Eq, Str("Hello, duck!".to_string()), Newline,
            Pub, Let, ident("primes"), Colon, ident("array"), LParen, ident("u8"), RParen, Eq,
                LBracket, Int(2), Comma, Int(3), Comma, Int(5), Comma, Int(7), RBracket, Newline,
            Pub, Struct, ident("Point"), Colon, Newline,
            Indent, ident("x"), Colon, ident("f32"), Newline,
            ident("y"), Colon, ident("f32"), Newline,
            Dedent, Pub, Fn, ident("add"), LParen, ident("a"), Colon, ident("i32"), Comma,
                ident("b"), Colon, ident("i32"), RParen, Arrow, ident("i32"), Colon, Newline,
            Indent, Return, ident("a"), Plus, ident("b"), Newline,
            Dedent, Pub, Fn, ident("main"), LParen, RParen, Colon, Newline,
            Indent, Let, ident("a"), Eq, Int(1), Newline,
            Let, ident("b"), Eq, Int(2), Newline,
            Let, ident("c"), Eq, ident("add"), LParen, ident("a"), Comma, ident("b"), RParen, Newline,
            ident("logi"), LParen, ident("c"), RParen, Newline,
            ident("logf"), LParen, Float(1.5), RParen, Newline,
            ident("logs"), LParen, ident("greeting"), RParen, Newline,
            For, ident("p"), In, ident("primes"), Colon, Newline,
            Indent, ident("logi"), LParen, ident("p"), As, ident("i32"), RParen, Newline,
            Dedent, Var, ident("i"), Eq, Int(0), Newline,
            While, ident("i"), Lt, Int(3), Colon, Newline,
            Indent, ident("i"), PlusEq, Int(1), Newline,
            Continue, Newline,
            Dedent, While, True, Colon, Newline,
            Indent, Break, Newline,
            Dedent, Dedent, Eof,
        ];
        assert_eq!(kinds(src), expected);
    }

    #[test]
    fn nested_blocks_dedent_together() {
        let src = "if a:\n  if b:\n    x\ny\n";
        #[rustfmt::skip]
        let expected = vec![
            If, ident("a"), Colon, Newline,
            Indent, If, ident("b"), Colon, Newline,
            Indent, ident("x"), Newline,
            Dedent, Dedent, ident("y"), Newline,
            Eof,
        ];
        assert_eq!(kinds(src), expected);
    }

    #[test]
    fn blank_and_comment_lines_are_ignored() {
        let src = "a\n\n   \n    # comment\nb # trailing\n";
        assert_eq!(
            kinds(src),
            vec![ident("a"), Newline, ident("b"), Newline, Eof]
        );
    }

    #[test]
    fn newlines_inside_brackets_are_ignored() {
        let src = "f(a,\n    b)\nc";
        #[rustfmt::skip]
        let expected = vec![
            ident("f"), LParen, ident("a"), Comma, ident("b"), RParen, Newline,
            ident("c"), Newline, Eof,
        ];
        assert_eq!(kinds(src), expected);
    }

    #[test]
    fn leading_pipe_continues_the_line_above() {
        let chain = vec![
            ident("a"),
            PipeArrow,
            ident("b"),
            PipeArrow,
            ident("c"),
            Newline,
            ident("d"),
            Newline,
            Eof,
        ];
        assert_eq!(kinds("a\n  |> b\n  |> c\nd\n"), chain);
        // Steps needn't line up, and blank and comment lines may sit between.
        assert_eq!(
            kinds("a # one\n  |> b\n\n  # two\n      |> c\r\nd\n"),
            chain
        );

        // The block the chain is in stays open.
        #[rustfmt::skip]
        let expected = vec![
            ident("f"), Colon, Newline,
            Indent, ident("a"), PipeArrow, ident("b"), Newline,
            ident("c"), Newline,
            Dedent, Eof,
        ];
        assert_eq!(kinds("f:\n  a\n    |> b\n  c\n"), expected);
    }

    #[test]
    fn leading_pipe_must_be_indented_deeper() {
        // At the block's own indentation, or shallower, it starts a line.
        assert_eq!(
            kinds("a\n|> b\n"),
            vec![ident("a"), Newline, PipeArrow, ident("b"), Newline, Eof]
        );
        #[rustfmt::skip]
        let expected = vec![
            ident("f"), Colon, Newline,
            Indent, ident("a"), Newline,
            Dedent, PipeArrow, ident("b"), Newline,
            Eof,
        ];
        assert_eq!(kinds("f:\n  a\n|> b\n"), expected);
        assert_eq!(
            error("f:\n    a\n  |> b\n"),
            LexErrorKind::InconsistentIndent
        );
    }

    #[test]
    fn crlf_line_endings() {
        let src = "a:\r\n\tb\r\n";
        assert_eq!(
            kinds(src),
            vec![
                ident("a"),
                Colon,
                Newline,
                Indent,
                ident("b"),
                Newline,
                Dedent,
                Eof
            ]
        );
    }

    #[test]
    fn empty_source() {
        assert_eq!(kinds(""), vec![Eof]);
        assert_eq!(kinds("\n  \n# hi\n"), vec![Eof]);
    }

    #[test]
    fn numbers() {
        assert_eq!(
            kinds("1_000 0xff 0b101 0o17 1.5 2e3 1.5e-2 x.0"),
            vec![
                Int(1000),
                Int(255),
                Int(5),
                Int(15),
                Float(1.5),
                Float(2000.0),
                Float(0.015),
                ident("x"),
                Dot,
                Int(0),
                Newline,
                Eof
            ]
        );
        assert_eq!(
            kinds("1.foo"),
            vec![Int(1), Dot, ident("foo"), Newline, Eof]
        );
        assert_eq!(error("123abc"), LexErrorKind::InvalidNumber);
        assert_eq!(error("0x"), LexErrorKind::InvalidNumber);
        assert_eq!(error("99999999999999999999"), LexErrorKind::IntTooLarge);
    }

    #[test]
    fn tuple_indices() {
        assert_eq!(
            kinds("t.0.1 t.10 1.5"),
            vec![
                ident("t"),
                Dot,
                Int(0),
                Dot,
                Int(1),
                ident("t"),
                Dot,
                Int(10),
                Float(1.5),
                Newline,
                Eof
            ]
        );
        for src in ["t.01", "t.1_0", "t.0x1", "t.1e3", "t.1a"] {
            assert_eq!(error(src), LexErrorKind::InvalidNumber, "{src}");
        }
    }

    #[test]
    fn strings() {
        assert_eq!(
            kinds(r#""hi\n\"there\" \u{1F986}""#),
            vec![Str("hi\n\"there\" 🦆".to_string()), Newline, Eof]
        );
        assert_eq!(error("\"abc"), LexErrorKind::UnterminatedString);
        assert_eq!(error("\"abc\ndef\""), LexErrorKind::UnterminatedString);
        assert_eq!(error(r#""\q""#), LexErrorKind::InvalidEscape);
    }

    #[test]
    fn operators() {
        assert_eq!(
            kinds("-> == != <= >= << >> += -= *= /= %= < > = - + * / % & | ^ ~"),
            vec![
                Arrow, EqEq, NotEq, Le, Ge, Shl, Shr, PlusEq, MinusEq, StarEq, SlashEq, PercentEq,
                Lt, Gt, Eq, Minus, Plus, Star, Slash, Percent, Amp, Pipe, Caret, Tilde, Newline,
                Eof
            ]
        );
        assert_eq!(
            kinds("a |> b | > c |>= d"),
            vec![
                ident("a"),
                PipeArrow,
                ident("b"),
                Pipe,
                Gt,
                ident("c"),
                PipeArrow,
                Eq,
                ident("d"),
                Newline,
                Eof
            ]
        );
        assert_eq!(
            kinds("[0; n]"),
            vec![LBracket, Int(0), Semi, ident("n"), RBracket, Newline, Eof]
        );
        assert_eq!(
            kinds("p as! &u8 as uint"),
            vec![
                ident("p"),
                AsUnchecked,
                Amp,
                ident("u8"),
                As,
                ident("uint"),
                Newline,
                Eof
            ]
        );
        assert_eq!(error("as !"), LexErrorKind::UnexpectedChar('!'));
        assert_eq!(error("!"), LexErrorKind::UnexpectedChar('!'));
    }

    #[test]
    fn inconsistent_indent() {
        assert_eq!(error("a:\n    b\n  c\n"), LexErrorKind::InconsistentIndent);
        assert_eq!(error("a:\n\tb\n    c\n"), LexErrorKind::InconsistentIndent);
    }

    #[test]
    fn bracket_errors() {
        assert_eq!(
            error("(]"),
            LexErrorKind::MismatchedClose {
                expected: ')',
                found: ']'
            }
        );
        assert_eq!(error(")"), LexErrorKind::UnmatchedClose(')'));
        assert_eq!(error("f(a,\n"), LexErrorKind::Unclosed('('));
    }

    #[test]
    fn spans() {
        let file = DummyManager::new().entry_point();
        let tokens = tokenize(file, "let x").unwrap();
        assert_eq!(
            tokens[0].span,
            Span {
                file,
                start: 0,
                end: 3
            }
        );
        assert_eq!(
            tokens[1].span,
            Span {
                file,
                start: 4,
                end: 5
            }
        );
    }
}

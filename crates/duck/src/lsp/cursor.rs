//! What is being written at a place in a source, which seldom parses as it
//! is: the line there is replaced by a statement that does, for the checker
//! to be asked of.

use duck_compiler::file::FileId;
use duck_compiler::lex::{self, LexError, LexErrorKind, Token, TokenKind};

/// A source with the line being written replaced.
pub struct Cursor {
    pub source: String,
    /// The byte the statement in place of the line starts at.
    pub probe: usize,
}

/// What is being written where something is to be suggested.
pub enum Completing {
    /// A name, which the names in scope at the statement are suggested for.
    Names(Cursor),
    /// What follows a `.`, after the expression that the statement is.
    Members(Cursor),
    /// What follows `module.`.
    Module,
    /// A `.name`, which the type expected at the place the statement names
    /// it is suggested the variants or members of.
    Expected(Cursor),
    /// A name of the path of a `use`, after these. The line is a `use` of
    /// them alone, with the last where the statement is said to start, if
    /// there are any.
    Used(Vec<String>, Option<Cursor>),
}

/// A call whose arguments are being written.
pub struct Calling {
    /// The statement is what is called.
    pub cursor: Cursor,
    /// How many arguments come before the one being written.
    pub index: usize,
    /// The label of the one being written, if it has one.
    pub label: Option<String>,
    /// Whether what is called is a `.name` of the type expected where the
    /// statement names it, rather than the statement itself.
    pub expected: bool,
    /// The labels of the arguments written so far.
    pub labels: Vec<String>,
    /// Whether nothing of the argument is written yet, but for the start
    /// of a name, so that it may be given a label.
    pub starts: bool,
}

/// The line being written: a statement up to a place in it, which may be
/// lines down from where it starts.
struct Line<'s> {
    src: &'s str,
    /// The byte the place is at.
    offset: usize,
    /// The byte its first line starts at.
    start: usize,
    /// The indentation of its first line.
    indent: &'s str,
    /// Its tokens before the place.
    tokens: Vec<Token>,
}

/// The most brackets a line being written is taken to leave open.
const MAX_OPEN: usize = 64;

/// The name written after a `.` that has none yet, for the line to parse:
/// one that no variant or member is likely to have.
const UNNAMED: &str = "zz";

/// What is being written at byte `offset` of `src`, if something can be
/// suggested there. Nothing is in a comment, a string or a number, for the
/// name that a declaration gives, or for a `.name` that the type expected
/// of it has.
pub fn completing(src: &str, offset: usize) -> Option<Completing> {
    let line = Line::at(src, offset, false)?;
    let mut tokens = &line.tokens[..];
    // A name being written is narrowed to by the editor.
    match tokens.split_last() {
        Some((last, rest)) if last.span.end == offset => match last.kind {
            TokenKind::Ident(_) => tokens = rest,
            TokenKind::Int(_) | TokenKind::Float(_) => return None,
            _ => {}
        },
        _ => {}
    }
    let public = tokens
        .first()
        .is_some_and(|first| first.kind == TokenKind::Pub);
    if let Some(TokenKind::Use) = tokens.get(public as usize).map(|token| &token.kind) {
        return used(&line, &tokens[public as usize + 1..]);
    }
    match tokens.last().map(|token| &token.kind) {
        Some(TokenKind::Dot) => {
            let dot = tokens.len() - 1;
            let start = postfix(tokens, dot);
            if let [only] = &tokens[start..dot]
                && only.kind == TokenKind::Module
            {
                return Some(Completing::Module);
            }
            // Nothing comes before the `.` of a `.name`.
            let Some(receiver) = line.text(&tokens[start..dot]) else {
                let end = tokens[dot].span.end;
                return Some(Completing::Expected(line.expecting(end, UNNAMED, end)));
            };
            Some(Completing::Members(line.asking(receiver)))
        }
        Some(
            TokenKind::Let
            | TokenKind::Var
            | TokenKind::Fn
            | TokenKind::Struct
            | TokenKind::Union
            | TokenKind::For,
        ) => None,
        _ => Some(Completing::Names(line.replaced(match line.indent {
            "" => "",
            _ => "pass",
        }))),
    }
}

/// What is being written of the path of a `use`, whose `tokens` these are
/// after the `use`, on `line`. `None` after an `as`, which gives a name.
fn used(line: &Line, tokens: &[Token]) -> Option<Completing> {
    // The names before each group being written, outermost first.
    let mut groups: Vec<Vec<String>> = Vec::new();
    let mut path = Vec::new();
    for token in tokens {
        match &token.kind {
            TokenKind::Ident(name) => path.push(name.clone()),
            TokenKind::Dot => {}
            TokenKind::LBrace => groups.push(path.clone()),
            TokenKind::Comma => path = groups.last()?.clone(),
            TokenKind::RBrace => path = groups.pop()?,
            _ => return None,
        }
    }
    let ends = tokens.last().map(|token| &token.kind);
    if matches!(ends, Some(TokenKind::Ident(_) | TokenKind::RBrace)) {
        return None;
    }
    let cursor = path.last().map(|last| {
        let statement = format!("use {}", path.join("."));
        let mut cursor = line.replaced(&statement);
        cursor.probe += statement.len() - last.len();
        cursor
    });
    Some(Completing::Used(path, cursor))
}

/// The innermost call that byte `offset` of `src` is in the arguments of, if
/// it's in those of any.
pub fn calling(src: &str, offset: usize) -> Option<Calling> {
    let line = Line::at(src, offset, true)?;
    let tokens = &line.tokens[..];
    // The brackets left open, innermost last.
    let mut open = Vec::new();
    for (i, token) in tokens.iter().enumerate() {
        match token.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => open.push(i),
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                open.pop();
            }
            _ => {}
        }
    }
    // What comes before the parenthesis of a call is called, as nothing
    // before that of a group or of a declaration's parameters is.
    let declares = |start: usize| {
        let before = tokens[..start].last().map(|token| &token.kind);
        matches!(before, Some(TokenKind::Fn | TokenKind::RParen))
            && tokens.iter().any(|token| token.kind == TokenKind::Fn)
    };
    let (start, paren) = open.into_iter().rev().find_map(|paren| {
        let start = postfix(tokens, paren);
        let called = tokens[paren].kind == TokenKind::LParen && start < paren;
        (called && !declares(start)).then_some((start, paren))
    })?;
    let callee = line.text(&tokens[start..paren])?;
    let label = |argument: &[Token]| match argument {
        [name, colon, ..] if colon.kind == TokenKind::Colon => match &name.kind {
            TokenKind::Ident(name) => Some(name.clone()),
            _ => None,
        },
        _ => None,
    };
    let (mut index, mut depth, mut argument) = (0, 0usize, paren + 1);
    let mut labels = Vec::new();
    for (i, token) in tokens.iter().enumerate().skip(paren + 1) {
        match token.kind {
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                depth = depth.saturating_sub(1);
            }
            TokenKind::Comma if depth == 0 => {
                labels.extend(label(&tokens[argument..i]));
                index += 1;
                argument = i + 1;
            }
            _ => {}
        }
    }
    let starts = match &tokens[argument..] {
        [] => true,
        [name] => matches!(name.kind, TokenKind::Ident(_)) && name.span.end == offset,
        _ => false,
    };
    // A `.name` is of the type expected of it where it is, so the line is
    // kept up to it.
    let expected = tokens[start].kind == TokenKind::Dot;
    let cursor = match expected {
        true => {
            let name = &tokens[paren - 1];
            line.expecting(name.span.end, "", name.span.start)
        }
        false => line.asking(callee),
    };
    Some(Calling {
        cursor,
        index,
        label: label(&tokens[argument..]),
        expected,
        labels,
        starts,
    })
}

impl<'s> Line<'s> {
    /// The line being written at byte `offset` of `src`. `None` in a comment
    /// or a string, or where what comes before doesn't lex.
    ///
    /// A bracket left open above makes all that follows one line. Unless
    /// the `whole` of that is wanted, a line below it that looks to start a
    /// statement is taken to: one indented no deeper than the line with the
    /// bracket, which closes none.
    fn at(src: &'s str, offset: usize, whole: bool) -> Option<Self> {
        let before = src.get(..offset)?;
        let line = Self::lexed(src, offset, before)?;
        let last = before.rfind('\n').map_or(0, |i| i + 1);
        let rest = src[last..].trim_start_matches([' ', '\t']);
        let indent = src.len() - last - rest.len();
        if whole
            || line.start == last
            || indent > line.indent.len()
            || rest.starts_with([')', ']', '}'])
        {
            return Some(line);
        }
        // Blank, so that the last line is where it was.
        let alone = " ".repeat(last) + &before[last..];
        Self::lexed(src, offset, &alone)
    }

    /// The line that ends at byte `offset` of `src`, of which `before` is
    /// what comes before, or stands for it.
    fn lexed(src: &'s str, offset: usize, before: &str) -> Option<Self> {
        let tokens = lex_open(before)?;
        // Those of the source, and none of what closed its brackets.
        let layout = |kind: &TokenKind| {
            matches!(kind, TokenKind::Indent | TokenKind::Dedent | TokenKind::Eof)
        };
        let mut tokens: Vec<_> = (tokens.into_iter())
            .filter(|token| token.span.start < offset && !layout(&token.kind))
            .collect();
        // Only a comment comes between tokens, but for spaces, and it ends
        // with its line.
        let written = tokens.last().map_or(0, |token| token.span.end);
        let last = before.rfind('\n').map_or(0, |i| i + 1);
        if before.get(written.max(last)..)?.contains('#') {
            return None;
        }
        let newline = |token: &Token| token.kind == TokenKind::Newline;
        let ended = tokens.iter().rposition(newline).map_or(0, |i| i + 1);
        tokens.drain(..ended);
        let within = tokens.first().map_or(offset, |first| first.span.start);
        let start = src[..within].rfind('\n').map_or(0, |i| i + 1);
        let line = &src[start..];
        let indent = &line[..line.len() - line.trim_start_matches([' ', '\t']).len()];
        Some(Self {
            src,
            offset,
            start,
            indent,
            tokens,
        })
    }

    /// The source that `tokens` of the line span. `None` if there are none.
    fn text(&self, tokens: &[Token]) -> Option<&'s str> {
        let (first, last) = (tokens.first()?, tokens.last()?);
        self.src.get(first.span.start..last.span.end)
    }

    /// The source with the expression `expr` as a statement in place of the
    /// line, which the checker is asked the type of. In a module that is a
    /// global bound to nothing.
    fn asking(&self, expr: &str) -> Cursor {
        match self.indent {
            "" => self.replaced(&format!("let _ = {expr}")),
            _ => self.replaced(expr),
        }
    }

    /// The source with the line cut short at byte `end` of it, where `name`
    /// is written, and made to parse from there: the brackets it has open
    /// by then are closed, and a line that heads a block has one. The
    /// statement is said to start at byte `probe` of the source, which is
    /// in the line and no later than `end`.
    fn expecting(&self, end: usize, name: &str, probe: usize) -> Cursor {
        let Some(first) = self.tokens.first() else {
            return self.replaced(name);
        };
        let mut open = Vec::new();
        for token in self.tokens.iter().filter(|token| token.span.end <= end) {
            match token.kind {
                TokenKind::LParen => open.push(')'),
                TokenKind::LBracket => open.push(']'),
                TokenKind::LBrace => open.push('}'),
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => {
                    open.pop();
                }
                _ => {}
            }
        }
        let closed: String = open.into_iter().rev().collect();
        // An arm of a `match`, and the statements that test a condition.
        let kinds: Vec<_> = self.tokens.iter().map(|token| &token.kind).collect();
        let heads = matches!(
            kinds[..],
            [TokenKind::Dot | TokenKind::If | TokenKind::While, ..]
                | [TokenKind::Else, TokenKind::If, ..]
        );
        let block = match (heads, self.has_block()) {
            (false, _) => String::new(),
            (true, true) => ":".to_string(),
            (true, false) => format!(":\n{}\tpass", self.indent),
        };
        let head = &self.src[first.span.start..end];
        let mut cursor = self.replaced(&format!("{head}{name}{closed}{block}"));
        cursor.probe += probe - first.span.start;
        cursor
    }

    /// Whether the lines under the one the place is on are a block of it:
    /// the next that isn't blank is indented deeper than the line is.
    fn has_block(&self) -> bool {
        let rest = &self.src[self.offset..];
        let below = rest.split_once('\n').map_or("", |(_, below)| below);
        let mut lines = below.lines().filter(|line| !line.trim().is_empty());
        let indent = |line: &str| line.len() - line.trim_start_matches([' ', '\t']).len();
        lines
            .next()
            .is_some_and(|line| indent(line) > self.indent.len())
    }

    /// The source with `statement` in place of the line, indented as it is,
    /// and of the rest of the line the place is on. What the line goes on
    /// to on the lines below is left there, not to parse.
    fn replaced(&self, statement: &str) -> Cursor {
        let rest = &self.src[self.offset..];
        let rest = &rest[rest.find('\n').unwrap_or(rest.len())..];
        let before = &self.src[..self.start];
        Cursor {
            source: [before, self.indent, statement, rest].concat(),
            probe: before.len() + self.indent.len(),
        }
    }
}

/// The tokens of `before`, a source up to a place in it, closing the
/// brackets it leaves open there. `None` if it doesn't lex for more than
/// that.
fn lex_open(before: &str) -> Option<Vec<Token>> {
    let mut closed = before.to_string();
    for _ in 0..MAX_OPEN {
        let open = match lex::tokenize(FileId::default(), &closed) {
            Ok(tokens) => return Some(tokens),
            Err(LexError {
                kind: LexErrorKind::Unclosed(open),
                ..
            }) => open,
            Err(_) => return None,
        };
        // On a line of its own, as the last may end in a comment.
        closed.push('\n');
        closed.push(match open {
            '(' => ')',
            '[' => ']',
            _ => '}',
        });
    }
    None
}

/// Where the operand that ends before token `end` of `tokens` starts: a
/// name, or something in brackets, and all that is read of it by `.name`,
/// `.*`, a call or an index. `end` itself if no operand ends there.
fn postfix(tokens: &[Token], end: usize) -> usize {
    let mut start = end;
    while let Some(last) = start.checked_sub(1) {
        match tokens[last].kind {
            // What is called or indexed comes before, if anything is.
            TokenKind::RParen | TokenKind::RBracket => match opening(tokens, last) {
                Some(open) => start = open,
                None => break,
            },
            TokenKind::DotStar => start = last,
            TokenKind::Ident(_) | TokenKind::Int(_) | TokenKind::Module => {
                start = last;
                match last.checked_sub(1) {
                    Some(dot) if tokens[dot].kind == TokenKind::Dot => start = dot,
                    _ => break,
                }
            }
            _ => break,
        }
    }
    start
}

/// The bracket that the one at `close` of `tokens` closes.
fn opening(tokens: &[Token], close: usize) -> Option<usize> {
    let mut depth = 0usize;
    for (i, token) in tokens[..=close].iter().enumerate().rev() {
        match token.kind {
            TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace => depth += 1,
            TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `src` without the `@` that marks a place in it, and the place.
    fn marked(src: &str) -> (String, usize) {
        let offset = src.find('@').unwrap();
        (src.replacen('@', "", 1), offset)
    }

    /// `cursor`'s source, with `@` where its statement starts.
    fn shown(cursor: &Cursor) -> String {
        let (before, after) = cursor.source.split_at(cursor.probe);
        format!("{before}@{after}")
    }

    /// What is suggested at the `@` of `src`: `names`, `members` or
    /// `module`, and the source the checker is asked of.
    fn completing_at(src: &str) -> Option<(&'static str, String)> {
        let (src, offset) = marked(src);
        Some(match completing(&src, offset)? {
            Completing::Names(cursor) => ("names", shown(&cursor)),
            Completing::Members(cursor) => ("members", shown(&cursor)),
            Completing::Module => ("module", String::new()),
            Completing::Expected(cursor) => ("expected", shown(&cursor)),
            Completing::Used(_, Some(cursor)) => ("used", shown(&cursor)),
            Completing::Used(..) => ("used", String::new()),
        })
    }

    /// The call that the `@` of `src` is in the arguments of: the source the
    /// checker is asked of, and which argument is there.
    fn calling_at(src: &str) -> Option<(String, usize, Option<String>)> {
        let (src, offset) = marked(src);
        let calling = calling(&src, offset)?;
        Some((shown(&calling.cursor), calling.index, calling.label))
    }

    fn asked(kind: &'static str, source: &str) -> Option<(&'static str, String)> {
        Some((kind, source.to_string()))
    }

    #[test]
    fn a_name_is_suggested_in_place_of_its_line() {
        assert_eq!(
            completing_at("fn f():\n    let a = 1\n    ret@\n    done()\n"),
            asked("names", "fn f():\n    let a = 1\n    @pass\n    done()\n")
        );
        // Where nothing is written yet, and where a name is being changed.
        assert_eq!(
            completing_at("fn f():\n    @\n"),
            asked("names", "fn f():\n    @pass\n")
        );
        assert_eq!(
            completing_at("fn f():\n    if a < li@mit:\n        pass\n"),
            asked("names", "fn f():\n    @pass\n        pass\n")
        );
        // A module has no statements, and a struct only `pass`.
        assert_eq!(
            completing_at("let a = Po@\nfn f():\n    pass\n"),
            asked("names", "@\nfn f():\n    pass\n")
        );
        assert_eq!(
            completing_at("struct S:\n    at: &Po@\n"),
            asked("names", "struct S:\n    @pass\n")
        );
        // A line goes on through the brackets it leaves open.
        assert_eq!(
            completing_at("fn f():\n    g(\n        a, # one\n        b@\n    )\n"),
            asked("names", "fn f():\n    @pass\n    )\n")
        );
        assert_eq!(
            completing_at("fn f():\n    g(\n        a,\n    @)\n"),
            asked("names", "fn f():\n    @pass\n")
        );
        // But not through a line that looks to start another statement,
        // above which a bracket was only left open.
        assert_eq!(
            completing_at("fn f():\n    g(a.b,\n    le@\n"),
            asked("names", "fn f():\n    g(a.b,\n    @pass\n")
        );
        assert_eq!(
            completing_at("fn f():\n    # g(\n    g(a,\n    @\nfn h():\n    pass\n"),
            asked(
                "names",
                "fn f():\n    # g(\n    g(a,\n    @pass\nfn h():\n    pass\n"
            )
        );
        assert_eq!(
            completing_at("fn f():\n    g(a,\n    b.c.@\n"),
            asked("members", "fn f():\n    g(a,\n    @b.c\n")
        );
    }

    #[test]
    fn what_follows_a_dot_is_suggested_of_what_is_before_it() {
        assert_eq!(
            completing_at("fn f(p: P):\n    let a = p.@\n    return\n"),
            asked("members", "fn f(p: P):\n    @p\n    return\n")
        );
        assert_eq!(
            completing_at("fn f():\n    g(a, -b.c[i + 1].@x, 2)\n"),
            asked("members", "fn f():\n    @b.c[i + 1]\n")
        );
        assert_eq!(
            completing_at("fn f():\n    return (a + b).0.@\n"),
            asked("members", "fn f():\n    @(a + b).0\n")
        );
        assert_eq!(
            completing_at("fn f():\n    if make(1, (2)).first.*.na@:\n        pass\n"),
            asked(
                "members",
                "fn f():\n    @make(1, (2)).first.*\n        pass\n"
            )
        );
        // In a module the expression is an initializer.
        assert_eq!(
            completing_at("let far = geo.origin.@\n"),
            asked("members", "@let _ = geo.origin\n")
        );
        assert_eq!(
            completing_at("fn f(p: geo.@):\n    pass\n"),
            asked("members", "@let _ = geo\n    pass\n")
        );
        assert_eq!(completing_at("let n = module.@\n"), asked("module", ""));
    }

    #[test]
    fn nothing_is_suggested_where_no_name_in_scope_is_written() {
        assert_eq!(completing_at("fn f():\n    pass # see p.@\n"), None);
        assert_eq!(completing_at("# p.@\n"), None);
        assert_eq!(completing_at("let s = \"a.@\"\n"), None);
        assert_eq!(completing_at("let n = 12@\n"), None);
        assert_eq!(completing_at("fn f():\n    let @\n"), None);
        assert_eq!(completing_at("fn na@\n"), None);
        assert_eq!(completing_at("use geo.len as @\n"), None);
        assert_eq!(completing_at("use geo.len @\n"), None);
    }

    #[test]
    fn a_dot_alone_is_suggested_of_the_type_expected_of_it() {
        // The line is kept up to the `.`, where a name is written for it,
        // and made to parse from there.
        assert_eq!(
            completing_at("fn f() -> Shape:\n    return .@\n"),
            asked("expected", "fn f() -> Shape:\n    return .@zz\n")
        );
        assert_eq!(
            completing_at("fn f():\n    g(a, [.em@pty, 1], 2)\n    h()\n"),
            asked("expected", "fn f():\n    g(a, [.@zz])\n    h()\n")
        );
        assert_eq!(
            completing_at("let mode: Mode = .@\n"),
            asked("expected", "let mode: Mode = .@zz\n")
        );
        // A line that heads a block is given one, unless it has one.
        assert_eq!(
            completing_at("fn f():\n    if s == .@\n    done()\n"),
            asked(
                "expected",
                "fn f():\n    if s == .@zz:\n    \tpass\n    done()\n"
            )
        );
        assert_eq!(
            completing_at("fn f():\n    while s != .@:\n        step()\n"),
            asked(
                "expected",
                "fn f():\n    while s != .@zz:\n        step()\n"
            )
        );
        // An arm of a `match` is one, and its pattern is matched against
        // what the `match` is of.
        assert_eq!(
            completing_at("fn f():\n    match s:\n        .@\n"),
            asked(
                "expected",
                "fn f():\n    match s:\n        .@zz:\n        \tpass\n"
            )
        );
        assert_eq!(
            completing_at("fn f():\n    match s:\n        .some(.c@):\n            pass\n"),
            asked(
                "expected",
                "fn f():\n    match s:\n        .some(.@zz):\n            pass\n"
            )
        );
    }

    #[test]
    fn the_path_of_a_use_is_suggested_of_what_comes_before() {
        let used = |src: &str| {
            let (src, offset) = marked(src);
            match completing(&src, offset) {
                Some(Completing::Used(path, cursor)) => {
                    Some((path.join("."), cursor.as_ref().map(shown)))
                }
                _ => None,
            }
        };
        let path =
            |path: &str, source: Option<&str>| Some((path.to_string(), source.map(str::to_string)));
        assert_eq!(used("use @\n"), path("", None));
        assert_eq!(used("pub use ge@\nfn f():\n    pass\n"), path("", None));
        // The line is a `use` of the names before, at the last of them.
        assert_eq!(used("use geo.@\n"), path("geo", Some("use @geo\n")));
        assert_eq!(
            used("use util.geo.Po@int\nlet a = 1\n"),
            path("util.geo", Some("use util.@geo\nlet a = 1\n"))
        );
        // In a group, the names before it and those before in it.
        assert_eq!(used("use geo.{Point, @\n"), path("geo", Some("use @geo\n")));
        assert_eq!(used("use geo.{ @ }\n"), path("geo", Some("use @geo\n")));
        assert_eq!(
            used("use a.{b.{c, d}, e.f.@\n"),
            path("a.e.f", Some("use a.e.@f\n"))
        );
        assert_eq!(
            used("use a.{\n\tb,\n\tc.@\n}\n"),
            path("a.c", Some("use a.@c\n}\n"))
        );
    }

    #[test]
    fn a_call_says_which_arguments_it_has_and_what_is_expected_of_it() {
        let (src, offset) = marked("fn f():\n    area(1.0, h: 2.0, sc@\n");
        let calling = calling(&src, offset).unwrap();
        assert_eq!(
            (calling.index, &calling.labels[..]),
            (2, &["h".to_string()][..])
        );
        assert!(calling.starts && !calling.expected);
        let (src, offset) = marked("fn f():\n    area(1.0, h: @\n");
        let calling = super::calling(&src, offset).unwrap();
        assert!(!calling.starts && calling.labels.is_empty());
        let (src, offset) = marked("fn f():\n    area(w + @\n");
        assert!(!super::calling(&src, offset).unwrap().starts);
        // A `.name` is called as the type expected of it has it.
        let (src, offset) = marked("fn f() -> result(i32, u8):\n    return g(.ok(@\n");
        let calling = super::calling(&src, offset).unwrap();
        assert!(calling.expected);
        assert_eq!(
            shown(&calling.cursor),
            "fn f() -> result(i32, u8):\n    return g(.@ok)\n"
        );
    }

    #[test]
    fn a_call_is_the_innermost_whose_arguments_are_open() {
        let call = |source: &str, index, label: Option<&str>| {
            Some((source.to_string(), index, label.map(str::to_string)))
        };
        assert_eq!(
            calling_at("fn f():\n    area(@\n"),
            call("fn f():\n    @area\n", 0, None)
        );
        assert_eq!(
            calling_at("fn f():\n    let v = geo.len(p, sc@ale: 1.0)\n"),
            call("fn f():\n    @geo.len\n", 1, None)
        );
        assert_eq!(
            calling_at("fn f():\n    area(2.0, h: 3@)\n"),
            call("fn f():\n    @area\n", 1, Some("h"))
        );
        assert_eq!(
            calling_at("fn f():\n    a(b(c, d), [e, (g, @\n"),
            call("fn f():\n    @a\n", 1, None)
        );
        assert_eq!(
            calling_at("fn f():\n    a(b(c, d, @\n"),
            call("fn f():\n    @b\n", 2, None)
        );
        assert_eq!(
            calling_at("fn f():\n    a(\n        b,\n        @\n    )\n"),
            call("fn f():\n    @a\n    )\n", 1, None)
        );
        // A generic type is called once it has its type arguments.
        assert_eq!(
            calling_at("let b = Box(u8)(@\n"),
            call("@let _ = Box(u8)\n", 0, None)
        );
        assert_eq!(
            calling_at("let s = steps[0](1, @\n"),
            call("@let _ = steps[0]\n", 1, None)
        );
    }

    #[test]
    fn nothing_is_called_in_a_group_or_a_declaration() {
        assert_eq!(calling_at("fn f():\n    let x = (a + @\n"), None);
        assert_eq!(calling_at("fn f():\n    a(b)@\n"), None);
        assert_eq!(calling_at("fn area(w: f64, @\n"), None);
        assert_eq!(calling_at("fn(T) boxed(value: T, @\n"), None);
        assert_eq!(calling_at("extern:\n    pub fn log(n: @\n"), None);
        assert_eq!(calling_at("let f: fn(i32, @\n"), None);
        assert_eq!(calling_at("struct(T, @\n"), None);
        assert_eq!(calling_at("fn f():\n    a( # b(@\n"), None);
        // But a default is an expression like any other.
        assert_eq!(
            calling_at("fn area(w: f64, h: f64 = unit(@\n"),
            Some(("@let _ = unit\n".to_string(), 0, None))
        );
    }
}

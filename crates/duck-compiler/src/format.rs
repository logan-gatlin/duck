//! `duck format`: lays source text out as the language is written.
//!
//! The tokens of the source are written again as they were, with the spaces
//! between them, the indentation of each line and the blank lines among them
//! made regular. A statement is on one line if it fits, wherever the source
//! breaks it, and is otherwise broken at its brackets and its pipes, as only
//! they let a statement go on. Comments stay as they are, and only the commas
//! that end what is in brackets come and go.

use std::mem;

use crate::Error;
use crate::file::FileId;
use crate::lex::{self, Token, TokenKind};
use crate::parse;

/// A line of the formatted text. It is blank if it has no code and no comment.
#[derive(Default)]
struct Line<'a> {
    /// How many levels it is indented.
    indent: usize,
    /// Its tokens, spaced. Empty if it has none.
    code: String,
    /// The comment it ends with.
    comment: Option<Comment<'a>>,
    /// How deep the statement or item it starts is in blocks, if it starts
    /// one.
    starts: Option<usize>,
    /// Whether the block of its statement or item follows it.
    opens: bool,
}

/// A `#` comment, which ends the line it is on.
#[derive(Clone, Copy)]
struct Comment<'a> {
    /// The whitespace the source has before it.
    gap: &'a str,
    text: &'a str,
    /// Whether the source has it on a line of its own.
    alone: bool,
}

/// A part of a statement: a token, or brackets and what they hold.
struct Piece<'a> {
    /// Whether a space is before it, where it doesn't start a line.
    spaced: bool,
    kind: PieceKind<'a>,
    /// The comments between it and the token after it.
    after: Vec<Comment<'a>>,
}

enum PieceKind<'a> {
    Token(&'a str),
    Group(Group<'a>),
}

/// A pair of brackets and the items between them, which commas separate.
#[derive(Default)]
struct Group<'a> {
    open: &'a str,
    close: &'a str,
    /// The comments between the opening bracket and the first item.
    opened: Vec<Comment<'a>>,
    items: Vec<Item<'a>>,
    /// Whether the source has a comma after the last item, which keeps the
    /// items a line each.
    trailing_comma: bool,
    /// Whether the items are a list that a comma may end, however many they
    /// are: not an index, the length of `[value; len]` or a value in
    /// parentheses.
    list: bool,
    /// Whether the brackets are those of a call, as far as their own tokens
    /// say. Those of a pattern, `.name(pattern)`, are no list.
    call: bool,
    /// All of it on one line, unless a comment or a trailing comma breaks it.
    flat: Option<String>,
}

struct Item<'a> {
    pieces: Vec<Piece<'a>>,
    /// The comments between it and the item after it, or the closing bracket.
    after: Vec<Comment<'a>>,
    /// All of it on one line, unless a comment or a trailing comma breaks it.
    flat: Option<String>,
}

/// Brackets that are open, and the item being read in them.
struct Frame<'a> {
    /// Whether a space is before the opening bracket.
    spaced: bool,
    group: Group<'a>,
    item: Vec<Piece<'a>>,
}

/// What the last token read is, which the comments after it are kept with.
#[derive(Clone, Copy)]
enum Last {
    /// The last piece of the item being read.
    Piece,
    /// The bracket that opened the innermost group.
    Open,
    /// The comma after the last item of the innermost group.
    Comma,
}

struct Formatter<'a> {
    src: &'a str,
    tokens: &'a [Token],
    /// The columns a line fits in.
    width: usize,
    lines: Vec<Line<'a>>,
    /// Where the last token read ends in `src`.
    end: usize,
    /// How many blocks are open.
    depth: usize,
    /// The indentation the source gives each open block, as the lexer has
    /// it. Blocks that end stay until the comments after them are placed.
    indents: Vec<&'a str>,
    /// The statement being read, but for what is in its open brackets.
    pieces: Vec<Piece<'a>>,
    /// The brackets that are open, outermost first.
    frames: Vec<Frame<'a>>,
    /// The first token of the statement being read, if it has one yet.
    first: Option<&'a TokenKind>,
    /// The last token read, if it is of the statement being read.
    prev: Option<&'a TokenKind>,
    last: Last,
    /// Whether `prev` is an operator before its operand, as in `-x`.
    prefix: bool,
    /// Whether `prev` is the index of a tuple element, as in `t.0`.
    index: bool,
    /// Whether the source starts a line of the statement being read with
    /// `|>`, which keeps each of its pipes at the start of a line.
    piped: bool,
    /// Whether the statement being written is the pattern of a `match` arm.
    arm: bool,
    /// Whether a comment ends the line being written, so that what comes
    /// next starts another.
    ended: bool,
}

/// One level of indentation.
const INDENT: &str = "\t";

/// How many columns a level of indentation is counted as.
const INDENT_WIDTH: usize = 4;

/// The columns a line fits in. A line is longer only if nothing in it can
/// be broken, or for its comment.
const MAX_WIDTH: usize = 100;

/// The widest that every item of an array is for several to share a line
/// where the array is broken.
const SHORT_WIDTH: usize = 10;

/// What sets a comment apart from the code before it, where the source has
/// no spaces that do.
const COMMENT_GAP: &str = "  ";

/// Lays `src` out as the language is written, changing only its whitespace
/// and the commas that end what is in brackets. A source that doesn't parse
/// has no layout: its errors are returned.
///
/// - A block is indented with one tab more than the statement it is of.
/// - Tokens are a space apart, except inside brackets, around `.`, before
///   `,`, `;` and `:`, after an operator that comes before its operand, and
///   before the brackets of a call, an index or type parameters.
/// - A statement is on one line if it fits in 100 columns, a tab being 4,
///   wherever the source breaks it. Otherwise each `|>` outside brackets
///   starts a line, indented once. A line that is still too long is broken
///   at the last brackets that it fits up to, or first at the parameters of
///   a function: their items are a line each, indented once and each ended
///   with a comma, and the closing bracket starts the line after. Brackets
///   that hold only a call are broken at its brackets, and the items of an
///   array that are all short share lines.
/// - The source keeps a statement broken with a line that starts with `|>`,
///   which breaks it at every pipe, and with a comma after the last item in
///   brackets or a comment in them, which break them.
/// - No more than one line in a row is blank, and none are at the start of
///   the file, at its end, at the start of a block or inside brackets. One
///   sets apart each item that has a block from the items before and after.
/// - Comments are kept, each as far from the code before it as it was.
pub fn format(src: &str) -> Result<String, Vec<Error>> {
    format_within(src, MAX_WIDTH)
}

/// [`format`], with lines that fit in `width` columns.
fn format_within(src: &str, width: usize) -> Result<String, Vec<Error>> {
    let tokens = lex::tokenize(FileId::default(), src).map_err(|e| vec![Error::Lex(e)])?;
    if let Err(errors) = parse::parse(&tokens) {
        return Err(errors.into_iter().map(Error::Parse).collect());
    }
    let formatted = Formatter::new(src, &tokens, width).run();
    let same = lex::tokenize(FileId::default(), &formatted).is_ok_and(|formatted| {
        kinds(&formatted).eq(kinds(&tokens)) && parse::parse(&formatted).is_ok()
    });
    assert!(same, "formatting changed more than whitespace");
    Ok(formatted)
}

impl Line<'_> {
    fn is_blank(&self) -> bool {
        self.code.is_empty() && self.comment.is_none()
    }

    /// Whether it is a comment alone, outside every block and statement.
    fn is_top_comment(&self) -> bool {
        self.code.is_empty() && self.comment.is_some() && self.indent == 0
    }

    /// Whether it starts an item, or is a comment among the items.
    fn is_top(&self) -> bool {
        self.starts == Some(0) || self.is_top_comment()
    }

    /// The column after its code.
    fn width(&self) -> usize {
        self.indent * INDENT_WIDTH + width(&self.code)
    }
}

impl<'a> Frame<'a> {
    /// Ends the item being read, which is one if it has a token.
    fn end_item(&mut self) {
        if self.item.is_empty() {
            return;
        }
        // The comma that ends the item comes before the comments that do.
        let after = tail(&mut self.item);
        let flat = flat(&self.item);
        self.group.items.push(Item {
            pieces: mem::take(&mut self.item),
            after,
            flat,
        });
    }
}

impl<'a> Formatter<'a> {
    fn new(src: &'a str, tokens: &'a [Token], width: usize) -> Self {
        Self {
            src,
            tokens,
            width,
            lines: Vec::new(),
            end: 0,
            depth: 0,
            indents: vec![""],
            pieces: Vec::new(),
            frames: Vec::new(),
            first: None,
            prev: None,
            last: Last::Piece,
            prefix: false,
            index: false,
            piped: false,
            arm: false,
            ended: false,
        }
    }

    fn run(mut self) -> String {
        let tokens = self.tokens;
        for (index, token) in tokens.iter().enumerate() {
            match token.kind {
                TokenKind::Newline => self.statement(),
                TokenKind::Indent => {
                    self.depth += 1;
                    self.indents.push(self.text(token));
                    if let Some(line) = self.lines.last_mut() {
                        line.opens = true;
                    }
                }
                TokenKind::Dedent => self.depth -= 1,
                TokenKind::Eof => self.gap(self.src.len(), true),
                _ => self.token(index),
            }
        }
        render(&self.lines)
    }

    /// Reads the token at `index` into the statement it is of, after what
    /// the source has before it.
    fn token(&mut self, index: usize) {
        use TokenKind::*;
        let tokens = self.tokens;
        let token = &tokens[index];
        let kind = &token.kind;
        let text = self.text(token);
        // Outside brackets, only a line that starts with `|>` goes on with
        // a statement.
        let between = &self.src[self.end..token.span.start];
        if self.prev.is_some() && self.frames.is_empty() && between.contains(['\n', '\r']) {
            self.piped = true;
        }
        self.gap(token.span.start, false);

        let prefix = match kind {
            Tilde => true,
            Minus | Amp | Dot => !self.prev.is_some_and(ends_operand),
            _ => false,
        };
        let spaced = self
            .prev
            .is_some_and(|prev| self.spaced(prev, kind, prefix));
        self.last = Last::Piece;
        match kind {
            LParen | LBracket | LBrace => {
                let call = *kind == LParen && self.prev.is_some_and(ends_operand);
                let list = match kind {
                    LParen => call || matches!(self.prev, Some(Fn | Struct | Union)),
                    LBracket => !self.prev.is_some_and(ends_operand),
                    _ => true,
                };
                let group = Group {
                    open: text,
                    list,
                    call,
                    ..Group::default()
                };
                self.frames.push(Frame {
                    spaced,
                    group,
                    item: Vec::new(),
                });
                self.last = Last::Open;
            }
            RParen | RBracket | RBrace => self.close(text),
            Comma if !self.frames.is_empty() => {
                self.frames.last_mut().unwrap().end_item();
                self.last = Last::Comma;
            }
            _ => {
                // `[value; len]` is no list.
                if let (Semi, Some(frame)) = (kind, self.frames.last_mut()) {
                    frame.group.list = false;
                }
                self.item().push(Piece {
                    spaced,
                    kind: PieceKind::Token(text),
                    after: Vec::new(),
                });
            }
        }
        self.first = self.first.or(Some(kind));
        self.index = matches!(kind, Int(_)) && self.prev == Some(&Dot);
        self.prefix = prefix;
        self.prev = Some(kind);
        self.end = token.span.end;
    }

    /// Reads the bracket that closes the innermost group.
    fn close(&mut self, close: &'a str) {
        let mut frame = self.frames.pop().expect("the lexer pairs brackets");
        let trailing_comma = frame.item.is_empty() && !frame.group.items.is_empty();
        frame.end_item();
        let mut group = frame.group;
        group.close = close;
        group.trailing_comma = trailing_comma;
        // The comma of a tuple of one is what makes it one, and so is no
        // comma that asks for a line each.
        let single = trailing_comma && group.open == "(" && !group.list && group.items.len() == 1;
        if group.opened.is_empty() && (!group.trailing_comma || single) {
            let items = group.items.iter().map(|item| match item.after.is_empty() {
                true => item.flat.as_deref(),
                false => None,
            });
            let items: Option<Vec<_>> = items.collect();
            let comma = if single { "," } else { "" };
            group.flat = items.map(|items| [group.open, &items.join(", "), comma, close].concat());
        }
        self.item().push(Piece {
            spaced: frame.spaced,
            kind: PieceKind::Group(group),
            after: Vec::new(),
        });
    }

    /// The item being read: that of the innermost brackets, or the
    /// statement.
    fn item(&mut self) -> &mut Vec<Piece<'a>> {
        match self.frames.last_mut() {
            Some(frame) => &mut frame.item,
            None => &mut self.pieces,
        }
    }

    /// The comments after the last token read.
    fn comments(&mut self) -> &mut Vec<Comment<'a>> {
        let Some(frame) = self.frames.last_mut() else {
            return &mut self.pieces.last_mut().unwrap().after;
        };
        match self.last {
            Last::Piece => &mut frame.item.last_mut().unwrap().after,
            Last::Open => &mut frame.group.opened,
            Last::Comma => &mut frame.group.items.last_mut().unwrap().after,
        }
    }

    /// Reads what the source has from the last token to `until`, which is
    /// the next token or, if `at_end`, the end of the file: the comment that
    /// ends the last token's line, and then each blank line and each comment
    /// alone on its line. Between statements they are written, and inside
    /// one the comments are kept with the token before them.
    fn gap(&mut self, until: usize, at_end: bool) {
        let gap = &self.src[self.end..until];
        let count = lines(gap).count();
        for (i, text) in lines(gap).enumerate() {
            let comment = Comment {
                gap: &text[..text.len() - text.trim_start().len()],
                text: text.trim(),
                alone: i > 0 || self.prev.is_none() && self.lines.is_empty(),
            };
            if self.prev.is_some() {
                if !comment.text.is_empty() {
                    self.comments().push(comment);
                }
            } else if !comment.alone {
                if let (false, Some(line)) = (comment.text.is_empty(), self.lines.last_mut()) {
                    line.comment = Some(comment);
                }
            } else if i + 1 < count || at_end {
                let line = match comment.text.is_empty() {
                    true => Line::default(),
                    false => Line {
                        indent: self.comment_indent(comment.gap),
                        comment: Some(comment),
                        ..Line::default()
                    },
                };
                self.lines.push(line);
            }
        }
        self.indents.truncate(self.depth + 1);
    }

    /// How far to indent a comment alone on its line between statements,
    /// which the source indents with `whitespace`.
    fn comment_indent(&mut self, whitespace: &str) -> usize {
        // Where blocks end, a comment is of the deepest one that it is
        // indented as far as, and those after it are of none deeper.
        let depth = (self.depth..self.indents.len())
            .rev()
            .find(|&depth| whitespace.starts_with(self.indents[depth]))
            .unwrap_or(self.depth);
        self.indents.truncate(depth + 1);
        depth
    }

    /// Whether a space is between `prev` and `kind`, a token that is or
    /// isn't an operator before its operand, as `prefix` says.
    fn spaced(&self, prev: &TokenKind, kind: &TokenKind, prefix: bool) -> bool {
        use TokenKind::*;
        match (prev, kind) {
            // `1.0` would be a float, where `1 .0` is the first element of 1.
            (Int(_), Dot) if !self.index => true,
            (_, Comma | Semi | Colon | RParen | RBracket | RBrace | DotStar | DotDot) => false,
            (LParen | LBracket | LBrace | Dot | DotDot, _) => false,
            _ if self.prefix => false,
            (_, Dot) => prefix,
            // The brackets of a call, an index or type parameters.
            (_, LParen | LBracket | LBrace) => {
                !(ends_operand(prev) || matches!(prev, Fn | Struct | Union | Enum))
            }
            _ => true,
        }
    }

    fn text(&self, token: &Token) -> &'a str {
        &self.src[token.span.start..token.span.end]
    }

    /// Writes the statement that has been read: on one line if it fits, and
    /// otherwise broken at its pipes, and then at its brackets.
    fn statement(&mut self) {
        use TokenKind::*;
        if self.pieces.is_empty() {
            return;
        }
        let mut pieces = mem::take(&mut self.pieces);
        let piped = mem::take(&mut self.piped);
        // Only the pattern of an arm ends with `:` and starts with no keyword.
        let keyword = matches!(
            self.first.take(),
            Some(Pub | Fn | If | Else | While | For | Match | Struct | Enum | Union | Extern)
        );
        self.arm = self.prev.take() == Some(&Colon) && !keyword;
        self.ended = false;
        self.lines.push(Line {
            indent: self.depth,
            starts: Some(self.depth),
            ..Line::default()
        });

        let room = self.width.saturating_sub(self.depth * INDENT_WIDTH);
        if let Some(flat) = flat(&pieces).filter(|flat| !piped && width(flat) <= room) {
            self.line().code = flat;
            return;
        }
        let is_pipe = |piece: &Piece| matches!(piece.kind, PieceKind::Token("|>"));
        if !pieces.iter().any(is_pipe) {
            let parameters = parameters(&pieces);
            return self.sequence(&pieces, self.depth, 0, parameters);
        }
        // What each pipe is given, last first.
        let mut steps = Vec::new();
        while let Some(pipe) = pieces.iter().rposition(is_pipe) {
            steps.push(pieces.split_off(pipe));
        }
        steps.push(pieces);
        for (i, mut step) in steps.into_iter().rev().enumerate() {
            if i > 0 {
                self.newline(self.depth + 1);
            }
            let after = tail(&mut step);
            self.sequence(&step, self.depth + i.min(1), 0, None);
            self.comment(&after, self.depth + 1);
        }
    }

    /// Writes `pieces` from where the line being written ends. A line that
    /// they start is indented `indent` levels, and `tail` columns of the
    /// line they end are for what follows them. Brackets are broken if their
    /// line is too long with them on it, up to where the next brackets may
    /// break it, or if they are the piece at `broken`.
    fn sequence(
        &mut self,
        pieces: &[Piece<'a>],
        indent: usize,
        tail: usize,
        broken: Option<usize>,
    ) {
        for (i, piece) in pieces.iter().enumerate() {
            match &piece.kind {
                PieceKind::Token(text) => self.word(text, piece.spaced, indent),
                PieceKind::Group(group) => {
                    self.start(indent);
                    let (width, line) = (self.width, self.line());
                    let space = (piece.spaced && !line.code.is_empty()) as usize;
                    let room = width.saturating_sub(line.width() + space);
                    let fits = |flat: &String| {
                        group.items.is_empty()
                            || self::width(flat) + rest(&pieces[i + 1..], tail) <= room
                    };
                    match group
                        .flat
                        .as_ref()
                        .filter(|flat| broken != Some(i) && fits(flat))
                    {
                        Some(flat) => self.word(flat, piece.spaced, indent),
                        None => self.group(group, piece.spaced, indent),
                    }
                }
            }
            self.comment(&piece.after, indent);
        }
    }

    /// Writes `group` broken: its items a line each, indented once more
    /// than the line its opening bracket is on, and its closing bracket at
    /// the start of a line indented as that one. A comma ends each item
    /// that one may.
    fn group(&mut self, group: &Group<'a>, spaced: bool, indent: usize) {
        self.word(group.open, spaced, indent);
        // Brackets that hold only a call, or only other brackets, are broken
        // as the brackets in them are.
        if let [item] = &group.items[..]
            && let Some((last, callee)) = item.pieces.split_last()
            && matches!(&last.kind, PieceKind::Group(inner) if !inner.items.is_empty())
            && callee.iter().all(|piece| {
                matches!(piece.kind, PieceKind::Token(_)) && !piece.spaced && piece.after.is_empty()
            })
            && group.opened.is_empty()
            && item.after.is_empty()
            && !group.trailing_comma
        {
            self.sequence(&item.pieces, indent, 1, Some(callee.len()));
            return self.line().code.push_str(group.close);
        }
        let outer = self.line().indent;
        let inner = outer + 1;
        self.comment(&group.opened, inner);
        // A comma ends the last item if it may: one of several is of a list.
        let list = group.list && !(group.call && self.arm);
        let comma = list || group.items.len() > 1 || group.trailing_comma;
        let short = |item: &Item| {
            item.after.is_empty()
                && item
                    .flat
                    .as_ref()
                    .is_some_and(|flat| width(flat) <= SHORT_WIDTH)
        };
        let filled = group.open == "["
            && group.list
            && group.items.len() > 1
            && group.items.iter().all(short);
        for (i, item) in group.items.iter().enumerate() {
            let comma = i + 1 < group.items.len() || comma;
            match item.flat.as_ref().filter(|_| filled) {
                // As many short items to a line as fit, each with its comma.
                Some(flat) => {
                    if i == 0 || self.line().width() + 1 + width(flat) + 1 > self.width {
                        self.newline(inner);
                    }
                    self.word(flat, true, inner);
                }
                None => {
                    self.newline(inner);
                    self.sequence(&item.pieces, inner, comma as usize, None);
                }
            }
            if comma {
                self.line().code.push(',');
            }
            self.comment(&item.after, inner);
        }
        self.newline(outer);
        self.line().code.push_str(group.close);
    }

    /// Writes `text` on the line being written, after a space if it is
    /// `spaced` and the line has code, or on a line of its own if a comment
    /// ended that one.
    fn word(&mut self, text: &str, spaced: bool, indent: usize) {
        self.start(indent);
        let line = self.line();
        if spaced && !line.code.is_empty() {
            line.code.push(' ');
        }
        line.code.push_str(text);
    }

    /// Writes each of `comments` at the end of the line being written, or
    /// on a line of its own, indented `indent` levels, if it is alone on one
    /// or the line has a comment.
    fn comment(&mut self, comments: &[Comment<'a>], indent: usize) {
        for &comment in comments {
            if comment.alone || self.line().comment.is_some() {
                self.newline(indent);
            }
            self.line().comment = Some(comment);
            self.ended = true;
        }
    }

    /// Starts a line, indented `indent` levels, if a comment ended the one
    /// being written.
    fn start(&mut self, indent: usize) {
        if self.ended {
            self.newline(indent);
        }
    }

    fn newline(&mut self, indent: usize) {
        self.ended = false;
        self.lines.push(Line {
            indent,
            ..Line::default()
        });
    }

    /// The line being written.
    fn line(&mut self) -> &mut Line<'a> {
        self.lines.last_mut().expect("a statement starts a line")
    }
}

/// The lines as text, with the blank lines that belong among them.
fn render(lines: &[Line]) -> String {
    let mut out = String::new();
    // Whether a blank line comes before the next line.
    let mut blank = false;
    // Whether the last line written opens a block.
    let mut opened = false;
    // Whether the last item has a block, and nothing has followed it.
    let mut after_block = false;
    for (i, line) in lines.iter().enumerate() {
        if line.is_blank() {
            blank = true;
            continue;
        }
        // An item with a block is set apart with the comments right above it.
        let heads = line.is_top() && !(i > 0 && lines[i - 1].is_top_comment());
        if line.is_top() && (after_block || heads && has_block(&lines[i..])) {
            blank = true;
        }
        if blank && !opened && !out.is_empty() {
            out.push('\n');
        }
        (0..line.indent).for_each(|_| out.push_str(INDENT));
        out.push_str(&line.code);
        if let Some(comment) = line.comment {
            let spaces = !comment.gap.is_empty() && comment.gap.bytes().all(|b| b == b' ');
            match (line.code.is_empty(), spaces) {
                (true, _) => {}
                (false, true) => out.push_str(comment.gap),
                (false, false) => out.push_str(COMMENT_GAP),
            }
            out.push_str(comment.text);
        }
        out.push('\n');

        blank = false;
        opened = line.opens;
        match line.starts {
            _ if line.is_top() => after_block = false,
            Some(_) => after_block = true,
            None => {}
        }
    }
    out
}

/// Whether the item that `lines` starts with, after any comments right above
/// it, has a block.
fn has_block(lines: &[Line]) -> bool {
    let mut lines = lines.iter().skip_while(|line| line.is_top_comment());
    lines.next().is_some_and(|item| item.starts == Some(0))
        && lines
            .find_map(|line| line.starts)
            .is_some_and(|depth| depth > 0)
}

/// `pieces` on one line, unless a comment or a trailing comma breaks them.
fn flat(pieces: &[Piece]) -> Option<String> {
    let mut flat = String::new();
    for piece in pieces {
        if !piece.after.is_empty() {
            return None;
        }
        if piece.spaced && !flat.is_empty() {
            flat.push(' ');
        }
        match &piece.kind {
            PieceKind::Token(text) => flat.push_str(text),
            PieceKind::Group(group) => flat.push_str(group.flat.as_ref()?),
        }
    }
    Some(flat)
}

/// How many columns `pieces` take of the line they are written on, each
/// after a space if it has one, up to where the line may next be broken:
/// after the next bracket that opens, or after a comment. If it may not be,
/// `tail` more follow them.
fn rest(pieces: &[Piece], tail: usize) -> usize {
    let mut columns = 0;
    for piece in pieces {
        columns += piece.spaced as usize;
        match &piece.kind {
            PieceKind::Token(text) => columns += width(text),
            PieceKind::Group(group) => match group.flat.as_ref().filter(|_| group.items.is_empty())
            {
                Some(flat) => columns += width(flat),
                None => return columns + width(group.open),
            },
        }
        if !piece.after.is_empty() {
            return columns;
        }
    }
    columns + tail
}

/// The comments after the last of `pieces`, which it is left without.
fn tail<'a>(pieces: &mut [Piece<'a>]) -> Vec<Comment<'a>> {
    pieces
        .last_mut()
        .map(|piece| mem::take(&mut piece.after))
        .unwrap_or_default()
}

/// Which of `pieces` are the parameters of the function they declare, if
/// they declare one that has any.
fn parameters(pieces: &[Piece]) -> Option<usize> {
    let is = |piece: Option<&Piece>, token: &str| {
        piece.is_some_and(|piece| matches!(piece.kind, PieceKind::Token(text) if text == token))
    };
    let start = is(pieces.first(), "pub") as usize;
    if !is(pieces.get(start), "fn") {
        return None;
    }
    // After the name, which follows the type parameters if there are any.
    let generic = matches!(pieces.get(start + 1)?.kind, PieceKind::Group(_));
    let parameters = start + 2 + generic as usize;
    match &pieces.get(parameters)?.kind {
        PieceKind::Group(group) if !group.items.is_empty() => Some(parameters),
        _ => None,
    }
}

/// How many columns `text` takes.
fn width(text: &str) -> usize {
    text.chars().count()
}

/// Whether a token of this kind ends an operand, so that an operator after
/// it is between two, and a bracket after it is a call or an index.
fn ends_operand(kind: &TokenKind) -> bool {
    use TokenKind::*;
    matches!(
        kind,
        Ident(_) | Int(_) | Float(_) | Str(_) | True | False | Module | DotStar
    ) || is_closer(kind)
}

fn is_closer(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace
    )
}

/// The lines of `text`, each without the line break that ends it, as the
/// lexer breaks lines. The last is what follows the last break.
fn lines(text: &str) -> impl Iterator<Item = &str> {
    let mut rest = Some(text);
    std::iter::from_fn(move || {
        let text = rest?;
        let Some(at) = text.find(['\n', '\r']) else {
            rest = None;
            return Some(text);
        };
        let line_break = match text[at..].starts_with("\r\n") {
            true => 2,
            false => 1,
        };
        rest = Some(&text[at + line_break..]);
        Some(&text[..at])
    })
}

/// The kinds of `tokens`, but for the commas that end what is in brackets.
fn kinds(tokens: &[Token]) -> impl Iterator<Item = &TokenKind> {
    let kinds = tokens.iter().map(|token| &token.kind);
    let after = kinds.clone().skip(1).map(Some).chain([None]);
    kinds
        .zip(after)
        .filter(|(kind, after)| **kind != TokenKind::Comma || !after.is_some_and(is_closer))
        .map(|(kind, _)| kind)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::LexErrorKind;
    use crate::parse::ParseErrorKind;

    /// `src` formatted, which formatting again leaves as it is.
    fn formatted(src: &str) -> String {
        within(MAX_WIDTH, src)
    }

    /// `src` formatted with lines that fit in `width` columns.
    fn within(width: usize, src: &str) -> String {
        let formatted = format_within(src, width).unwrap();
        assert_eq!(format_within(&formatted, width).as_ref(), Ok(&formatted));
        formatted
    }

    #[test]
    fn example_program_is_formatted() {
        let src = include_str!("../example.duck");
        assert_eq!(formatted(src), src);
        // However narrow its lines, it is the same program.
        for width in 0..MAX_WIDTH {
            within(width, src);
        }
    }

    #[test]
    fn tokens_are_a_space_apart() {
        assert_eq!(formatted("let  x:i32=1+2*3\n"), "let x: i32 = 1 + 2 * 3\n");
        assert_eq!(
            formatted("pub  fn add(a:i32,b:i32=1)->i32:\n\treturn a+b\n"),
            "pub fn add(a: i32, b: i32 = 1) -> i32:\n\treturn a + b\n"
        );
        assert_eq!(
            formatted("fn f():\n\tx+=1\n\tif a<=b and not c or d!=e:\n\t\tpass\n"),
            "fn f():\n\tx += 1\n\tif a <= b and not c or d != e:\n\t\tpass\n"
        );
        assert_eq!(
            formatted("fn f():\n\tfor  i ,( k,v )in pairs:\n\t\tpass\n"),
            "fn f():\n\tfor i, (k, v) in pairs:\n\t\tpass\n"
        );
        assert_eq!(
            formatted("fn f():\n\tfor i in 0 .. n-1:\n\t\tpass\n"),
            "fn f():\n\tfor i in 0..n - 1:\n\t\tpass\n"
        );
        assert_eq!(
            formatted("fn f():\n\tfor i in - 1 .. - n:\n\t\tpass\n"),
            "fn f():\n\tfor i in -1..-n:\n\t\tpass\n"
        );
        assert_eq!(
            formatted("let b:varray(u8)=[ 0 ;SIZE ]\n"),
            "let b: varray(u8) = [0; SIZE]\n"
        );
        assert_eq!(
            formatted("pub let Make:type=fn( uint )->&var u8\nfn(R:Make)f(make:R):\n\tpass\n"),
            "pub let Make: type = fn(uint) -> &var u8\n\nfn(R: Make) f(make: R):\n\tpass\n"
        );
        assert_eq!(
            formatted("fn f()->option(opaque( fn( i32 )->i32 )):\n\tpass\n"),
            "fn f() -> option(opaque(fn(i32) -> i32)):\n\tpass\n"
        );
        assert_eq!(
            formatted("struct(T,R:Make=lib.bump,N=u8)Vec:\n\tnext:&Vec(T,N:i32)\n"),
            "struct(T, R: Make = lib.bump, N = u8) Vec:\n\tnext: &Vec(T, N: i32)\n"
        );
        assert_eq!(
            formatted("use geo . { Point ,len  as length }\n"),
            "use geo.{Point, len as length}\n"
        );
        assert_eq!(
            formatted("extern\"js\":\n\tfn print ( s:array(u8) )=\"p\"\n"),
            "extern \"js\":\n\tfn print(s: array(u8)) = \"p\"\n"
        );
    }

    #[test]
    fn operators_before_their_operands_touch_them() {
        assert_eq!(formatted("let x = - 1 - - 2\n"), "let x = -1 - -2\n");
        assert_eq!(formatted("let x = a&b & ~ c\n"), "let x = a & b & ~c\n");
        assert_eq!(
            formatted("let p:& var i32=& var 0\n"),
            "let p: &var i32 = &var 0\n"
        );
        assert_eq!(
            formatted("fn f(p:&u8)->& u8:\n\treturn(- x)as!& u8\n"),
            "fn f(p: &u8) -> &u8:\n\treturn (-x) as! &u8\n"
        );
        // `.name` is of the type expected, and `x.name` a field.
        assert_eq!(
            formatted("fn f():\n\tif s==. empty:\n\t\treturn . err( . huge )\n"),
            "fn f():\n\tif s == .empty:\n\t\treturn .err(.huge)\n"
        );
        assert_eq!(
            formatted("let x = p .* . a . 0 .1\n"),
            "let x = p.*.a.0.1\n"
        );
        assert_eq!(formatted("fn f():\n\tp .*=1\n"), "fn f():\n\tp.* = 1\n");
        assert_eq!(
            formatted("let x = module . min-1\n"),
            "let x = module.min - 1\n"
        );
    }

    #[test]
    fn brackets_touch_what_they_are_of() {
        assert_eq!(formatted("let x = f (a) [0] (b)\n"), "let x = f(a)[0](b)\n");
        assert_eq!(formatted("let x = a* ( b+c )\n"), "let x = a * (b + c)\n");
        assert_eq!(
            formatted("let x = [ ( 1,2 ) ,( 3,4 ) ]\n"),
            "let x = [(1, 2), (3, 4)]\n"
        );
        assert_eq!(
            formatted("struct (T,B:Box (T)) Pair:\n\ta:fn (T)->B\n"),
            "struct(T, B: Box(T)) Pair:\n\ta: fn(T) -> B\n"
        );
        assert_eq!(
            formatted("fn (T:( Head,Box (T) ),U:( )) f(x:T):\n\tpass\n"),
            "fn(T: (Head, Box(T)), U: ()) f(x: T):\n\tpass\n"
        );
        assert_eq!(
            formatted("struct S:\n\tuse   Head\n\tuse Box (T)\n\tx:i32\n"),
            "struct S:\n\tuse Head\n\tuse Box(T)\n\tx: i32\n"
        );
        assert_eq!(
            formatted("enum (u8) Color:\n\tred\nfn (T) id(x:T)->T:\n\treturn x\n"),
            "enum(u8) Color:\n\tred\n\nfn(T) id(x: T) -> T:\n\treturn x\n"
        );
        assert_eq!(
            formatted(
                "fn f():\n\tlet( a,_ )=t\n\tmatch( a,b ):\n\t\t( 1,[ x,_ ] ):\n\t\t\treturn( )\n"
            ),
            "fn f():\n\tlet (a, _) = t\n\tmatch (a, b):\n\t\t(1, [x, _]):\n\t\t\treturn ()\n"
        );
    }

    #[test]
    fn tokens_are_written_as_they_were() {
        let src = "let x = (0xFF, 1_000, 1e3, \"a\\u{62}\\n\", ((y)))\n";
        assert_eq!(formatted(src), src);
        // Without its space, the first element of 1 would be a float.
        assert_eq!(formatted("let x = 1 . 0\n"), "let x = 1 .0\n");
    }

    #[test]
    fn blocks_are_indented_with_tabs() {
        let src = "fn f():\n  while a:\n      if b:\n         pass\n      else  :\n         x = 1\n  return\n";
        let expected =
            "fn f():\n\twhile a:\n\t\tif b:\n\t\t\tpass\n\t\telse:\n\t\t\tx = 1\n\treturn\n";
        assert_eq!(formatted(src), expected);
    }

    #[test]
    fn a_return_is_laid_out_wherever_an_expression_is() {
        let src = "fn f():\n  x|>g( _ )|>return _\n  a or return-1\n  f(return,return x,[return],(return))\n  a==return(b,c).0\n  ~return&x\n";
        let expected = "fn f():\n\tx |> g(_) |> return _\n\ta or return -1\n\tf(return, return x, [return], (return))\n\ta == return (b, c).0\n\t~return &x\n";
        assert_eq!(formatted(src), expected);
        // So are a `break` and a `continue`.
        let src = "fn f():\n  while a:\n    b  or  break\n    f(continue,-break)and(break)\n";
        let expected = "fn f():\n\twhile a:\n\t\tb or break\n\t\tf(continue, -break) and (break)\n";
        assert_eq!(formatted(src), expected);
        // And a `todo`.
        let src = "fn f():\n  a  or  todo\n  f(todo,-todo)and(todo)\n";
        let expected = "fn f():\n\ta or todo\n\tf(todo, -todo) and (todo)\n";
        assert_eq!(formatted(src), expected);
        // A chain that is broken is broken before the `return` that ends it.
        let src = "fn f():\n\tn * 2\n\t\t|> add(_, 1) |> return _\n";
        let expected = "fn f():\n\tn * 2\n\t\t|> add(_, 1)\n\t\t|> return _\n";
        assert_eq!(formatted(src), expected);
    }

    #[test]
    fn a_defer_is_laid_out_as_the_statement_or_block_it_holds() {
        let src = "fn f():\n  defer  close( h )\n  defer(a,b).0=1\n  defer  :\n      x=1\n  pass\n";
        let expected =
            "fn f():\n\tdefer close(h)\n\tdefer (a, b).0 = 1\n\tdefer:\n\t\tx = 1\n\tpass\n";
        assert_eq!(formatted(src), expected);
    }

    #[test]
    fn a_statement_that_fits_is_on_one_line() {
        let src =
            "fn f(\na: i32,\n      b: i32\n  ) -> i32:\n    return g(a,\n  [\n1, 2],\n\n  b)\n";
        let expected = "fn f(a: i32, b: i32) -> i32:\n\treturn g(a, [1, 2], b)\n";
        assert_eq!(formatted(src), expected);
        assert_eq!(
            formatted("let x = (a\n\t|> f(_)\n)\n"),
            "let x = (a |> f(_))\n"
        );
        // A tab is 4 of the columns that it fits in.
        let src = "fn f():\n\tlet abc = g(a, b)\n";
        assert_eq!(within(21, src), src);
        assert_eq!(
            within(20, src),
            "fn f():\n\tlet abc = g(\n\t\ta,\n\t\tb,\n\t)\n"
        );
    }

    #[test]
    fn a_tuple_of_one_keeps_its_comma_on_its_line() {
        let src = "let x = ( a , )\nlet (b,):tuple( i32 )=((1,),).0\nlet y = f((a,), (b))\n";
        let expected = "let x = (a,)\nlet (b,): tuple(i32) = ((1,),).0\nlet y = f((a,), (b))\n";
        assert_eq!(formatted(src), expected);
        assert_eq!(formatted(expected), expected);
        // It is broken as any brackets are where it is too long, and is a
        // tuple still.
        assert_eq!(within(12, "let x = (first,)\n"), "let x = (\n\tfirst,\n)\n");
    }

    #[test]
    fn a_trailing_comma_keeps_brackets_broken() {
        let src = "let x = f(a, g(b, c,), d)\n";
        let expected = "let x = f(\n\ta,\n\tg(\n\t\tb,\n\t\tc,\n\t),\n\td,\n)\n";
        assert_eq!(formatted(src), expected);
        assert_eq!(formatted("let x = [a,]\n"), "let x = [\n\ta,\n]\n");
        assert_eq!(
            formatted("use geo.{\nPoint,\n}\nfn f(\na: i32,\n):\n\tpass\n"),
            "use geo.{\n\tPoint,\n}\n\nfn f(\n\ta: i32,\n):\n\tpass\n"
        );
    }

    #[test]
    fn a_line_that_is_too_long_is_broken_at_brackets() {
        let src = "let x = call(first, second + 1, third)\n";
        assert_eq!(within(38, src), src);
        let expected = "let x = call(\n\tfirst,\n\tsecond + 1,\n\tthird,\n)\n";
        assert_eq!(within(37, src), expected);

        // Brackets inside them only if their own line is too long.
        let src = "let x = call(first(a, b), second(c, d), third)\n";
        let expected =
            "let x = call(\n\tfirst(a, b),\n\tsecond(\n\t\tc,\n\t\td,\n\t),\n\tthird,\n)\n";
        assert_eq!(within(16, src), expected);

        // The last brackets that the line fits up to, and what follows them
        // on the line that closes them.
        let src = "let x = first(a, b).second(c, d).third(e) as u8\n";
        let expected = "let x = first(a, b).second(c, d).third(\n\te,\n) as u8\n";
        assert_eq!(within(40, src), expected);
        let expected = "let x = first(a, b).second(\n\tc,\n\td,\n).third(e) as u8\n";
        assert_eq!(within(36, src), expected);
        let expected =
            "let x = first(\n\ta,\n\tb,\n).second(\n\tc,\n\td,\n).third(\n\te,\n) as u8\n";
        assert_eq!(within(15, src), expected);

        // Nothing else breaks a line.
        let src = "let x = first_name + second_name + \"a string\"\n";
        assert_eq!(within(10, src), src);
        assert_eq!(within(10, "let x = f()\n"), "let x = f()\n");
    }

    #[test]
    fn a_function_is_broken_at_its_parameters_first() {
        let src = "pub fn(T) get(items: array(T), at: uint) -> option(T):\n\tpass\n";
        assert_eq!(within(54, src), src);
        let expected = "pub fn(T) get(\n\titems: array(T),\n\tat: uint,\n) -> option(T):\n\tpass\n";
        assert_eq!(within(53, src), expected);
        let src = "extern:\n\tfn read(into: varray(u8)) -> result(uint, Fault) = \"r\"\n";
        let expected =
            "extern:\n\tfn read(\n\t\tinto: varray(u8),\n\t) -> result(uint, Fault) = \"r\"\n";
        assert_eq!(within(40, src), expected);
        let expected = "extern:\n\tfn read(\n\t\tinto: varray(u8),\n\t) -> result(\n\t\tuint,\n\t\tFault,\n\t) = \"r\"\n";
        assert_eq!(within(28, src), expected);
    }

    #[test]
    fn a_function_in_a_function_is_laid_out_as_a_statement_is() {
        // Blank lines around it are the author's, and it is broken at its
        // parameters as any function is.
        let src = "fn f()->i32:\n  let a=1\n  fn  g( x:i32 )->i32:\n      return x\n\n  fn h():\n      pass\n  return g(a)\n";
        let expected = "fn f() -> i32:\n\tlet a = 1\n\tfn g(x: i32) -> i32:\n\t\treturn x\n\n\tfn h():\n\t\tpass\n\treturn g(a)\n";
        assert_eq!(formatted(src), expected);
        let src = "fn f():\n\tfn sum(first: i32, second: i32) -> i32:\n\t\treturn first\n\tpass\n";
        let expected = "fn f():\n\tfn sum(\n\t\tfirst: i32,\n\t\tsecond: i32,\n\t) -> i32:\n\t\treturn first\n\tpass\n";
        assert_eq!(within(30, src), expected);
    }

    #[test]
    fn a_comma_ends_a_broken_list_only() {
        // A call of one argument is a list, and so is an array of one.
        let src = "let x = f(first + second)[first + second]\n";
        let expected = "let x = f(\n\tfirst + second,\n)[\n\tfirst + second\n]\n";
        assert_eq!(within(14, src), expected);
        assert_eq!(
            within(12, "let x = [first + second]\n"),
            "let x = [\n\tfirst + second,\n]\n"
        );
        // A value in parentheses, the length of an array and the type of an
        // enum's values are not.
        assert_eq!(
            within(12, "let x = (first + second)\n"),
            "let x = (\n\tfirst + second\n)\n"
        );
        assert_eq!(
            within(12, "let x = [first; second]\n"),
            "let x = [\n\tfirst; second\n]\n"
        );
        assert_eq!(
            within(18, "enum(fn(i32) -> i32) E:\n\ta = f\n"),
            "enum(\n\tfn(i32) -> i32\n) E:\n\ta = f\n"
        );
        // Nor is what a variant holds in a pattern, as it is in a value.
        let src = "fn f():\n\tmatch s:\n\t\t.some(first_name):\n\t\t\treturn .some(first_name)\n";
        let expected = "fn f():\n\tmatch s:\n\t\t.some(\n\t\t\tfirst_name\n\t\t):\n\t\t\treturn .some(\n\t\t\t\tfirst_name,\n\t\t\t)\n";
        assert_eq!(within(20, src), expected);
    }

    #[test]
    fn brackets_that_hold_only_a_call_are_broken_as_it_is() {
        let src = "let x = f(a.g([first, second_name]))\n";
        let expected = "let x = f(a.g([\n\tfirst,\n\tsecond_name,\n]))\n";
        assert_eq!(within(20, src), expected);
        let src = "fn f():\n\tmatch s:\n\t\t.some((first_name, second_name)):\n\t\t\tpass\n";
        let expected = "fn f():\n\tmatch s:\n\t\t.some((\n\t\t\tfirst_name,\n\t\t\tsecond_name,\n\t\t)):\n\t\t\tpass\n";
        assert_eq!(within(30, src), expected);
        // Not with an operand beside it, or a comma or a comment in them.
        let src = "let x = (a + g(first, second))\n";
        let expected = "let x = (\n\ta + g(first, second)\n)\n";
        assert_eq!(within(24, src), expected);
        let src = "let x = f(g(a, b),)\nlet y = f( # one\n\tg(a, b))\n";
        let expected = "let x = f(\n\tg(a, b),\n)\nlet y = f( # one\n\tg(a, b),\n)\n";
        assert_eq!(formatted(src), expected);
    }

    #[test]
    fn short_items_of_a_broken_array_share_lines() {
        let src = "let x: array(u8) = [1, 22, 333, 4444, 55555, 666666, 7777777, 8]\n";
        let expected =
            "let x: array(u8) = [\n\t1, 22, 333, 4444, 55555,\n\t666666, 7777777, 8,\n]\n";
        assert_eq!(within(30, src), expected);
        // Unless one is longer than 10 columns, or the brackets are a call's.
        let src = "let x = [1, 22, 12345678901]\nlet y = f(1, 22, 333)\n";
        let expected =
            "let x = [\n\t1,\n\t22,\n\t12345678901,\n]\nlet y = f(\n\t1,\n\t22,\n\t333,\n)\n";
        assert_eq!(within(16, src), expected);
    }

    #[test]
    fn a_statement_is_broken_at_every_pipe_or_none() {
        let src = "fn f():\n\treturn n * 2 |> add(_, 1) |> half(_)\n";
        assert_eq!(formatted(src), src);
        let expected = "fn f():\n\treturn n * 2\n\t\t|> add(_, 1)\n\t\t|> half(_)\n";
        assert_eq!(within(30, src), expected);

        // A line that starts with `|>` keeps it so.
        let src = "fn f():\n  return n * 2 |> add(_,1)\n\n       |>half(_)\n  pass\n";
        let expected = "fn f():\n\treturn n * 2\n\t\t|> add(_, 1)\n\t\t|> half(_)\n\tpass\n";
        assert_eq!(formatted(src), expected);

        // What a pipe is given is broken as a line is.
        let src = "let x = first(a, b) |> second(_, c, d) |> third(_)\n";
        let expected =
            "let x = first(a, b)\n\t|> second(\n\t\t_,\n\t\tc,\n\t\td,\n\t)\n\t|> third(_)\n";
        assert_eq!(within(20, src), expected);
    }

    #[test]
    fn comments_are_kept() {
        // As far from the code as they were, or two spaces where they touch
        // it or a tab is between.
        let src = "let a=1 # one\nlet bc=2      # two\nlet d=3#three\nlet e=4\t# four  \n";
        let expected =
            "let a = 1 # one\nlet bc = 2      # two\nlet d = 3  #three\nlet e = 4  # four\n";
        assert_eq!(formatted(src), expected);

        let src = "   # first\nfn f(): # f\n        # body\n    pass\n#last";
        let expected = "# first\nfn f(): # f\n\t# body\n\tpass\n\n#last\n";
        assert_eq!(formatted(src), expected);
        assert_eq!(
            formatted("# only\n\n\n#   comments  "),
            "# only\n\n#   comments\n"
        );
        // A line is no longer for its comment.
        let src = "let x = f(a, b)   # a comment that goes on\n";
        assert_eq!(within(15, src), src);
    }

    #[test]
    fn comments_in_brackets_break_them() {
        let src = "let x = f(a, # one\n  b)   # end\n";
        assert_eq!(formatted(src), "let x = f(\n\ta, # one\n\tb,\n)   # end\n");

        // Each ends the line of the token before it, after its item's comma.
        let src = "let x = f( # open\n# alone\na # one\n, b # two\n# last\n)\n";
        let expected = "let x = f( # open\n\t# alone\n\ta, # one\n\tb, # two\n\t# last\n)\n";
        assert_eq!(formatted(src), expected);
        let src = "let x = [a + # plus\n\n  # alone\n b]\nlet y = (  # none\n)\n";
        let expected = "let x = [\n\ta + # plus\n\t# alone\n\tb,\n]\nlet y = (  # none\n)\n";
        assert_eq!(formatted(src), expected);

        let src =
            "fn f():\n\treturn n # one\n\t# alone\n\t\t|> g(_) # two\n\t\t|> h(_ # three\n\t\t)\n";
        let expected = "fn f():\n\treturn n # one\n\t\t# alone\n\t\t|> g(_) # two\n\t\t|> h(\n\t\t\t_, # three\n\t\t)\n";
        assert_eq!(formatted(src), expected);
    }

    #[test]
    fn comments_after_a_block_are_of_the_block_they_are_indented_as() {
        let src = "fn f():\n    if a:\n        pass\n        # of the if\n      # of f\n    # of f too\n        # and this\n# of nothing\nlet x = 1\n";
        let expected = "fn f():\n\tif a:\n\t\tpass\n\t\t# of the if\n\t# of f\n\t# of f too\n\t# and this\n\n# of nothing\nlet x = 1\n";
        assert_eq!(formatted(src), expected);

        let src =
            "fn f():\n  if a:\n    pass\n    # of the if\n  else:\n    pass\n    # of the else";
        let expected =
            "fn f():\n\tif a:\n\t\tpass\n\t\t# of the if\n\telse:\n\t\tpass\n\t\t# of the else\n";
        assert_eq!(formatted(src), expected);
    }

    #[test]
    fn blank_lines_are_at_most_one() {
        let src = "\n\nlet a = 1\n\n\n\nlet b = 2\nlet c = 3\n \t\n\n";
        assert_eq!(formatted(src), "let a = 1\n\nlet b = 2\nlet c = 3\n");

        // And none start a block.
        let src = "fn f():\n\n\t# first\n\n\tif a:\n\n\n\t\tpass\n\n\n\treturn\n";
        let expected = "fn f():\n\t# first\n\n\tif a:\n\t\tpass\n\n\treturn\n";
        assert_eq!(formatted(src), expected);
        assert_eq!(formatted(""), "");
        assert_eq!(formatted("\n \n\t\n"), "");
    }

    #[test]
    fn export_blocks_are_laid_out_as_extern_blocks_are() {
        let src = "pub   \"my:pkg/math@0.1.0\" :\n\tfn add ( a:i32,b:i32 )->i32:\n\t\treturn a+b\n\
                   \tpub fn double_it(n:i32)->i32=\"double\":\n\t\treturn n*2\nfn idle():\n\tpass\n\
                   pub fn tick()=\"tick-now\":\n\tpass\n";
        let expected = "pub \"my:pkg/math@0.1.0\":\n\tfn add(a: i32, b: i32) -> i32:\n\t\treturn a + b\n\
                        \tpub fn double_it(n: i32) -> i32 = \"double\":\n\t\treturn n * 2\n\n\
                        fn idle():\n\tpass\n\npub fn tick() = \"tick-now\":\n\tpass\n";
        assert_eq!(formatted(src), expected);
        assert_eq!(formatted(expected), expected);
    }

    #[test]
    fn items_with_blocks_are_set_apart() {
        let src = "use a.b\nlet x = 1\nstruct S:\n\ta: i32\nlet y = 2\nlet z = 3\n# of f\n# and more\nfn f(\n\ta: i32,\n):\n\tpass\n# of nothing\n\n# of g\nfn g():\n\tpass\nextern:\n\tfn h()\n";
        let expected = "use a.b\nlet x = 1\n\nstruct S:\n\ta: i32\n\nlet y = 2\nlet z = 3\n\n# of f\n# and more\nfn f(\n\ta: i32,\n):\n\tpass\n\n# of nothing\n\n# of g\nfn g():\n\tpass\n\nextern:\n\tfn h()\n";
        assert_eq!(formatted(src), expected);
    }

    #[test]
    fn lines_end_as_one_newline() {
        assert_eq!(
            formatted("fn f():  \r\n  pass\t\r\n\r\n\r\nlet x = 1\rlet y = 2"),
            "fn f():\n\tpass\n\nlet x = 1\nlet y = 2\n"
        );
    }

    #[test]
    fn a_source_that_does_not_parse_has_no_layout() {
        let errors = format("let x = \"unterminated\n").unwrap_err();
        assert!(matches!(
            &errors[..],
            [Error::Lex(e)] if e.kind == LexErrorKind::UnterminatedString
        ));

        let errors = format("fn f()\nlet x = 1 +\n").unwrap_err();
        let kinds: Vec<_> = errors
            .iter()
            .map(|error| match error {
                Error::Parse(e) => Some(&e.kind),
                _ => None,
            })
            .collect();
        assert!(matches!(
            &kinds[..],
            [
                Some(ParseErrorKind::MissingFnBody),
                Some(ParseErrorKind::Expected { .. }),
            ]
        ));
    }
}

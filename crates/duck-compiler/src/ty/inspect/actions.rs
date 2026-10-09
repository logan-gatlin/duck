//! What can be written to mend an error, where the error says enough of
//! what is missing for it to be written for whoever made it.

use std::ops::Range;

use crate::file::{FileId, FileManager};
use crate::lex::Span;
use crate::parse::{self, Arm, ExprKind, PatternKind, StmtKind};

use super::super::{Prim, Ty, TypeErrorKind, convertible};
use super::visit::{self, Node};
use super::{Analysis, Item, Sources, line_start};

/// A change that mends an error.
#[derive(Debug, Clone, PartialEq)]
pub struct Action {
    /// What it does, as it is offered.
    pub title: String,
    /// What it writes, each in place of what is at its span, which is none
    /// of the source where it only adds.
    pub edits: Vec<(Span, String)>,
}

/// How the body of an arm is indented past its pattern where no arm of its
/// `match` says.
const INDENT: &str = "\t";

impl Analysis {
    /// What mends the errors in bytes `within` of `file`: the arms that a
    /// `match` leaves out, the `use` of a name that another module has and
    /// this one doesn't, and the `as` that makes a number the kind of
    /// number expected of it.
    pub fn actions(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        within: Range<usize>,
    ) -> Vec<Action> {
        // One in an instance of a generic function is mended where the
        // function is declared, which is elsewhere.
        let errors = self
            .ck
            .errors
            .iter()
            .filter(|error| error.instances.is_empty());
        let errors = errors.filter_map(|error| {
            let span = error.span.filter(|span| {
                span.file == file && span.start <= within.end && within.start <= span.end
            });
            Some((span?, &error.kind))
        });
        let mut actions = Vec::new();
        for (span, kind) in errors {
            match kind {
                TypeErrorKind::NonExhaustive(witness) => {
                    actions.extend(self.missing_arms(files, span, witness));
                }
                TypeErrorKind::UnknownName(name) | TypeErrorKind::UnknownType(name) => {
                    actions.extend(self.missing_uses(files, file, name));
                }
                TypeErrorKind::Mismatch { expected, found } => {
                    actions.extend(self.cast(span, expected, found));
                }
                _ => {}
            }
        }
        actions
    }

    /// Adds the arms that the `match` of the value at `span` leaves out:
    /// one for each variant or member that no arm names, or else one for
    /// `witness`, a pattern of what no arm matches.
    fn missing_arms(
        &self,
        files: &mut impl FileManager,
        span: Span,
        witness: &str,
    ) -> Option<Action> {
        let arms = self.arms_of(span)?;
        let last = arms.last()?;
        let named: Vec<_> = (arms.iter())
            .filter_map(|arm| match &arm.pattern.kind {
                PatternKind::Variant(name, _) => Some(name.name.as_str()),
                _ => None,
            })
            .collect();
        let mut patterns: Vec<String> = match self.ck.known(self.ty_at(span)?) {
            Ty::Enum(id) => {
                let members = self.ck.enums[id.0 as usize].members.iter();
                let left = members.filter(|member| !named.contains(&member.name.as_str()));
                left.map(|member| format!(".{}", member.name)).collect()
            }
            ty => match self.ck.union_id(ty) {
                Some(id) => {
                    let variants = self.ck.structs[id.0 as usize].fields.iter();
                    let left = variants.filter(|variant| !named.contains(&variant.name.as_str()));
                    let pattern = |variant: &super::super::FieldDef| match variant.bare {
                        true => format!(".{}", variant.name),
                        false => format!(".{}(_)", variant.name),
                    };
                    left.map(pattern).collect()
                }
                None => Vec::new(),
            },
        };
        // What an arm that names a variant leaves of it, or what has no
        // variants to name: every other value is matched by `else`.
        if patterns.is_empty() {
            patterns.push(match witness {
                "_" => "else".to_string(),
                witness => witness.to_string(),
            });
        }
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        let text = src.file(span.file);
        // Indented as the last arm is, each with a body indented as its is.
        let indent = |at: usize| text.get(line_start(text, at)..at).unwrap_or_default();
        let arm = indent(last.pattern.span.start);
        let body = last.body.first().map(|stmt| indent(stmt.span.start));
        let body = match body.filter(|body| body.len() > arm.len() && body.trim().is_empty()) {
            Some(body) => body.to_string(),
            None => format!("{arm}{INDENT}"),
        };
        let end = last
            .body
            .last()
            .map_or(last.pattern.span.end, |stmt| stmt.span.end);
        let end = end + text.get(end..)?.find('\n').unwrap_or(text.len() - end);
        let arms = patterns
            .iter()
            .map(|pattern| format!("\n{arm}{pattern}:\n{body}pass"));
        let at = Span {
            file: span.file,
            start: end,
            end,
        };
        Some(Action {
            title: match patterns.len() {
                1 => format!("Add an arm for `{}`", patterns[0]),
                _ => "Add the arms that are left out".to_string(),
            },
            edits: vec![(at, arms.collect())],
        })
    }

    /// The arms of the `match` whose value is written at `span`.
    fn arms_of(&self, span: Span) -> Option<&[Arm]> {
        let mut arms = None;
        let items = self.program.items.iter();
        for item in items.filter(|item| item.span.file == span.file) {
            visit::each(item, &mut |node| {
                if let Node::Stmt(stmt) = node
                    && let StmtKind::Match { value, arms: found } = &stmt.kind
                    && value.span == span
                {
                    arms = Some(&found[..]);
                }
            });
        }
        arms
    }

    /// Adds a `use` of `name` to `file` for each module of the program
    /// that makes something so named `pub`, and that a path names from it.
    fn missing_uses(&self, files: &mut impl FileManager, file: FileId, name: &str) -> Vec<Action> {
        let mut paths = Vec::new();
        for module in self.files().into_iter().filter(|module| *module != file) {
            let has = self
                .ck
                .scopes
                .get(&module)
                .and_then(|scope| scope.get(name));
            if has.is_some_and(|entry| entry.is_pub && !matches!(entry.item, Item::Module(_)))
                && let Some(path) = self.use_path(files, file, module)
            {
                paths.push(path);
            }
        }
        let mut read = |id| files.contents(id);
        let start = self.use_site(&mut Sources::new(&mut read), file);
        let at = Span {
            file,
            start,
            end: start,
        };
        let action = |path: String| Action {
            title: format!("Add `use {path}.{name}`"),
            edits: vec![(at, format!("use {path}.{name}\n"))],
        };
        paths.into_iter().map(action).collect()
    }

    /// Casts the expression at `span` with `as` to the number that is
    /// `expected` of it, from the one that it is `found` to be.
    fn cast(&self, span: Span, expected: &str, found: &str) -> Option<Action> {
        let (to, from) = (Prim::from_name(expected)?, Prim::from_name(found)?);
        if !convertible(from, to) {
            return None;
        }
        let mut cast = None;
        let items = self.program.items.iter();
        for item in items.filter(|item| item.span.file == span.file) {
            visit::each(item, &mut |node| {
                if let Node::Expr(expr) = node
                    && expr.span == span
                {
                    cast = cast.take().or(Some(expr));
                }
            });
        }
        let end = Span {
            start: span.end,
            ..span
        };
        let start = Span {
            end: span.start,
            ..span
        };
        // `as` binds tighter than every operator written between operands.
        let edits = match binds_loosely(cast?) {
            true => vec![(start, "(".to_string()), (end, format!(") as {expected}"))],
            false => vec![(end, format!(" as {expected}"))],
        };
        Some(Action {
            title: format!("Cast to `{expected}` with `as`"),
            edits,
        })
    }
}

/// Whether `expr` is one that `as` after it would cast only the end of:
/// one written with an operator that binds looser than `as` does.
fn binds_loosely(expr: &parse::Expr) -> bool {
    matches!(
        expr.kind,
        ExprKind::Binary(..)
            | ExprKind::Unary(..)
            | ExprKind::AddrOf(..)
            | ExprKind::Pipe(..)
            | ExprKind::Assign { .. }
    )
}

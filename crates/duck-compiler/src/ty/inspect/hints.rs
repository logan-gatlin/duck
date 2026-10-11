//! What isn't written and would say more of what is: the type of a name
//! that is bound without one, and the parameter that an argument is for.

use std::ops::Range;

use crate::file::FileId;
use crate::parse::{self, Arg, Binding, ExprKind, ItemKind, Pattern, StmtKind};

use super::symbols::bound;
use super::visit::{self, Node};
use super::{Analysis, Item, Target};

/// Something to show at a place as if it were written there.
#[derive(Debug, Clone, PartialEq)]
pub struct Hint {
    /// The byte of the file it is shown at.
    pub offset: usize,
    pub label: String,
    pub kind: HintKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HintKind {
    /// `: Type`, after a name.
    Type,
    /// `name: `, before an argument.
    Parameter,
}

impl Analysis {
    /// What to show in bytes `within` of `file`, in order: the type of each
    /// name that a `let`, a `var` or a `for` binds without one, and the
    /// parameter that each argument without a label is given to, unless
    /// the argument is named as the parameter is.
    pub fn hints(&self, file: FileId, within: Range<usize>) -> Vec<Hint> {
        let mut hints = Vec::new();
        let items = self.program.items.iter();
        let overlaps = |item: &&parse::Item| {
            let span = item.span;
            span.file == file && span.start <= within.end && within.start <= span.end
        };
        for item in items.filter(overlaps) {
            if let ItemKind::Binding(binding) = &item.kind {
                self.binding_hints(binding, &mut hints);
            }
            visit::each(item, &mut |node| match node {
                Node::Stmt(stmt) => match &stmt.kind {
                    StmtKind::Binding(binding) => self.binding_hints(binding, &mut hints),
                    StmtKind::For { index, pattern, .. } => {
                        for pattern in index.iter().chain([pattern]) {
                            self.pattern_hints(pattern, &mut hints);
                        }
                    }
                    _ => {}
                },
                Node::Expr(expr) => {
                    if let ExprKind::Call(callee, args) = &expr.kind {
                        self.argument_hints(file, callee, args, &mut hints);
                    }
                }
            });
        }
        hints.retain(|hint| within.start <= hint.offset && hint.offset <= within.end);
        hints.sort_by_key(|hint| hint.offset);
        hints
    }

    /// The type of each name that `binding` binds, if it writes none.
    fn binding_hints(&self, binding: &Binding, hints: &mut Vec<Hint>) {
        if binding.ty.is_some() {
            return;
        }
        self.pattern_hints(&binding.pattern, hints);
    }

    /// The type of each name that `pattern` binds.
    fn pattern_hints(&self, pattern: &Pattern, hints: &mut Vec<Hint>) {
        let mut names = Vec::new();
        bound(pattern, &mut names);
        for (_, span) in names {
            hints.extend(self.type_at(span).map(|ty| Hint {
                offset: span.end,
                label: format!(": {ty}"),
                kind: HintKind::Type,
            }));
        }
    }

    /// The parameter that each of `args` is given to by its place, in a
    /// call of `callee` in `file`, if that names a function.
    fn argument_hints(
        &self,
        file: FileId,
        callee: &parse::Expr,
        args: &[Arg],
        hints: &mut Vec<Hint>,
    ) {
        let named = match &callee.kind {
            ExprKind::Name(_) => callee.span.start,
            ExprKind::Field(_, field) => field.span.start,
            _ => return,
        };
        let site = self.locate(file, named, false);
        let Some(Target::Item(item @ (Item::Func(_) | Item::GenericFn(_)))) = self.target(&site)
        else {
            return;
        };
        let Some((_, sig)) = self.fn_decl(item) else {
            return;
        };
        // Those given by their place come first.
        let placed = args.iter().take_while(|arg| arg.label.is_none());
        for (arg, param) in placed.zip(&sig.params) {
            let name = &param.name.name;
            let says = match &arg.value.kind {
                ExprKind::Name(written) => written == name,
                ExprKind::Field(_, field) => field.name == *name,
                _ => false,
            };
            if !says {
                hints.push(Hint {
                    offset: arg.value.span.start,
                    label: format!("{name}: "),
                    kind: HintKind::Parameter,
                });
            }
        }
    }
}

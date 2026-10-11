//! What a program declares and never uses: nothing is wrong with it, but
//! something was likely meant to use it. And what it declares apart from
//! the value that it is given at once, which says in two lines what one
//! does.

use std::collections::HashSet;
use std::slice;

use crate::file::{FileId, FileManager};
use crate::lex::Span;
use crate::parse::{self, ExprKind, Ident, ItemKind, Mutability, PatternKind, StmtKind};
use crate::visit::{self, Node};

use super::symbols::bound;
use super::{Analysis, Sources, names, type_param_names};

/// Something declared that nothing uses.
#[derive(Debug, Clone, PartialEq)]
pub struct Unused {
    pub name: String,
    /// Where it is named, where it is declared.
    pub span: Span,
    pub kind: UnusedKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnusedKind {
    /// A variable of a function, or a global.
    Variable,
    Function,
    /// A type parameter of a function, a struct or a union.
    TypeParam,
    /// A name that a `use` gives.
    Use,
}

/// A variable declared without a value that the next statement of its
/// block to name it assigns one, whatever else is so: it has no need to be
/// declared apart from it.
#[derive(Debug, Clone, PartialEq)]
pub struct Apart {
    pub name: String,
    /// Where it is named, where it is declared.
    pub span: Span,
    /// The statement that declares it.
    pub(super) declared: Span,
    pub(super) mutability: Mutability,
    /// Where its type is written.
    pub(super) ty: Span,
    /// Where the assignment names it.
    pub(super) assigned: Span,
}

impl Apart {
    /// What names the kind of warning, as [`UnusedKind::code`] does.
    pub const CODE: &'static str = "declared-apart";
}

impl UnusedKind {
    /// What names the kind of warning, as [`crate::Error::code`] names a
    /// kind of error.
    pub fn code(self) -> &'static str {
        match self {
            Self::Variable => "unused-variable",
            Self::Function => "unused-function",
            Self::TypeParam => "unused-type-parameter",
            Self::Use => "unused-use",
        }
    }
}

impl Analysis {
    /// What the program declares that nothing in it names again, in the
    /// order of its files: a variable or a global, a function, a type
    /// parameter, or what a `use` names. Nothing `pub` is among them, as
    /// another program may use it, nor a parameter, as its function may be
    /// one of several that are called alike, nor a name that starts with
    /// `_`, which says as much. A type parameter is among them whatever
    /// declares it: only its own declaration names it, and no function
    /// that has one is called as another is.
    pub fn unused(&self, files: &mut impl FileManager) -> Vec<Unused> {
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        // Where each `use` writes a name, which is no use of what it names.
        let uses = self.program.uses.iter();
        let written =
            uses.flat_map(|used| used.path.iter().chain(&used.members).chain([&used.name]));
        let written: HashSet<Span> = written.map(|name| name.span).collect();
        // What is named somewhere other than where it is declared, and in
        // which files by which names.
        let mut named: HashSet<Span> = HashSet::new();
        let mut named_as: HashSet<(FileId, &str, Span)> = HashSet::new();
        let texts: Vec<_> = (self.files().into_iter())
            .map(|file| (file, src.file(file).to_string()))
            .collect();
        for (file, text) in &texts {
            for (start, word) in names(text) {
                let span = Span {
                    file: *file,
                    start,
                    end: start + word.len(),
                };
                let Some(declared) = self.definition(*file, start).filter(|d| *d != span) else {
                    continue;
                };
                named.insert(declared);
                // What a module leads to isn't named by what a `use` calls
                // it, even where that is the same.
                let reached = text[..start].trim_end().ends_with('.');
                if !written.contains(&span) && !reached {
                    named_as.insert((*file, word, declared));
                }
            }
        }

        let mut unused = Vec::new();
        let mut declares = |name: &str, span: Span, kind: UnusedKind| {
            if !named.contains(&span) && !name.starts_with('_') {
                let name = name.to_string();
                unused.push(Unused { name, span, kind });
            }
        };
        for item in &self.program.items {
            let variable = UnusedKind::Variable;
            let type_params: Vec<&Ident> = match &item.kind {
                ItemKind::Fn(decl) => type_param_names(&decl.sig),
                ItemKind::Struct(decl) => decl.params.iter().map(|param| &param.name).collect(),
                ItemKind::Union(decl) => decl.params.iter().map(|param| &param.name).collect(),
                _ => Vec::new(),
            };
            for name in type_params {
                declares(&name.name, name.span, UnusedKind::TypeParam);
            }
            match &item.kind {
                ItemKind::Fn(decl) if !item.is_pub => {
                    let name = &decl.sig.name;
                    // The function a module starts with is run by its host,
                    // which calls what an interface exports too.
                    let starts = item.span.file == self.program.entry
                        && self.start.as_ref() == Some(&name.name);
                    if !starts && decl.interface.is_none() {
                        declares(&name.name, name.span, UnusedKind::Function);
                    }
                }
                ItemKind::Extern(block) => {
                    for imported in block.fns.iter().filter(|imported| !imported.is_pub) {
                        let name = &imported.sig.name;
                        declares(&name.name, name.span, UnusedKind::Function);
                    }
                }
                ItemKind::Binding(binding) if !item.is_pub => {
                    let mut bindings = Vec::new();
                    bound(&binding.pattern, &mut bindings);
                    for (name, span) in bindings {
                        declares(name, span, variable);
                    }
                }
                _ => {}
            }
            visit::each(item, &mut |node| {
                let Node::Stmt(stmt) = node else {
                    return;
                };
                let mut bindings = Vec::new();
                match &stmt.kind {
                    StmtKind::Fn(decl) => {
                        let name = &decl.sig.name;
                        return declares(&name.name, name.span, UnusedKind::Function);
                    }
                    StmtKind::Binding(binding) => bound(&binding.pattern, &mut bindings),
                    StmtKind::For { index, pattern, .. } => {
                        for pattern in index.iter().chain([pattern]) {
                            bound(pattern, &mut bindings);
                        }
                    }
                    StmtKind::Match { arms, .. } => {
                        for arm in arms {
                            bound(&arm.pattern, &mut bindings);
                        }
                    }
                    _ => {}
                }
                for (name, span) in bindings {
                    declares(name, span, variable);
                }
            });
        }
        // A `use` is used by the names that stand for what it names, in the
        // file it gives the name to.
        for used in self.program.uses.iter().filter(|used| !used.is_pub) {
            let name = &used.name;
            let item = self.item(used.module, &name.name);
            let Some(declared) = item.and_then(|item| self.item_span(item)) else {
                continue;
            };
            if !named_as.contains(&(used.module, name.name.as_str(), declared))
                && !name.name.starts_with('_')
            {
                unused.push(Unused {
                    name: name.name.clone(),
                    span: name.span,
                    kind: UnusedKind::Use,
                });
            }
        }
        // In the order they are written, file by file.
        let order: Vec<_> = texts.iter().map(|(file, _)| *file).collect();
        let place = |unused: &Unused| {
            let file = order.iter().position(|file| *file == unused.span.file);
            (file, unused.span.start)
        };
        unused.sort_by_key(place);
        unused
    }

    /// Each variable that the program declares without a value and then
    /// assigns one where it may as well be declared with it: the next
    /// statement of its block that names it assigns it whole. Only a name
    /// declared alone is among them, as a tuple of names is assigned one
    /// at a time.
    pub fn apart(&self) -> Vec<Apart> {
        let mut apart = Vec::new();
        for item in &self.program.items {
            if let ItemKind::Fn(decl) = &item.kind {
                apart.extend(apart_in(&decl.body));
            }
            visit::each(item, &mut |node| {
                let Node::Stmt(stmt) = node else {
                    return;
                };
                match &stmt.kind {
                    StmtKind::If {
                        then_body,
                        else_body,
                        ..
                    } => {
                        apart.extend(apart_in(then_body));
                        apart.extend(else_body.iter().flat_map(|body| apart_in(body)));
                    }
                    StmtKind::While { body, .. }
                    | StmtKind::For { body, .. }
                    | StmtKind::Defer(body) => apart.extend(apart_in(body)),
                    StmtKind::Match { arms, .. } => {
                        apart.extend(arms.iter().flat_map(|arm| apart_in(&arm.body)));
                    }
                    StmtKind::Fn(decl) => apart.extend(apart_in(&decl.body)),
                    StmtKind::Binding(_) | StmtKind::Expr(_) | StmtKind::Pass => {}
                }
            });
        }
        // In the order they are written, file by file.
        let order = self.files();
        let place = |apart: &Apart| {
            let file = order.iter().position(|file| *file == apart.span.file);
            (file, apart.span.start)
        };
        apart.sort_by_key(place);
        apart
    }
}

/// Each variable that a statement of `block` itself declares apart from
/// the value that a later one of them gives it.
fn apart_in(block: &[parse::Stmt]) -> impl Iterator<Item = Apart> {
    block.iter().enumerate().filter_map(|(i, stmt)| {
        let StmtKind::Binding(binding) = &stmt.kind else {
            return None;
        };
        let (PatternKind::Name(name), Some(ty), None) =
            (&binding.pattern.kind, &binding.ty, &binding.value)
        else {
            return None;
        };
        // The next of them that has anything to do with it.
        let next = block[i + 1..]
            .iter()
            .find(|stmt| binds(stmt, name) || mentions(stmt, name))?;
        let StmtKind::Expr(parse::Expr {
            kind:
                ExprKind::Assign {
                    target,
                    op: None,
                    value,
                },
            ..
        }) = &next.kind
        else {
            return None;
        };
        let named =
            |expr: &parse::Expr| matches!(&expr.kind, ExprKind::Name(found) if found == name);
        let mut reads = false;
        visit::expr(value, &mut |node| {
            reads |= matches!(node, Node::Expr(expr) if named(expr));
        });
        (named(target) && !reads).then(|| Apart {
            name: name.clone(),
            span: binding.pattern.span,
            declared: stmt.span,
            mutability: binding.mutability,
            ty: ty.span,
            assigned: target.span,
        })
    })
}

/// Whether `stmt` binds `name` for the statements of its block that follow
/// it, so that it is another that they name.
fn binds(stmt: &parse::Stmt, name: &str) -> bool {
    match &stmt.kind {
        StmtKind::Binding(binding) => {
            let mut names = Vec::new();
            bound(&binding.pattern, &mut names);
            names.iter().any(|(bound, _)| *bound == name)
        }
        StmtKind::Fn(decl) => decl.sig.name.name == name,
        _ => false,
    }
}

/// Whether `stmt` names `name` as a value, anywhere in it.
fn mentions(stmt: &parse::Stmt, name: &str) -> bool {
    let mut mentions = false;
    visit::block(slice::from_ref(stmt), &mut |node| {
        mentions |= matches!(
            node,
            Node::Expr(parse::Expr { kind: ExprKind::Name(found), .. }) if found == name
        );
    });
    mentions
}

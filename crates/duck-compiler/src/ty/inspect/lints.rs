//! What a program declares and never uses: nothing is wrong with it, but
//! something was likely meant to use it.

use std::collections::HashSet;

use crate::file::{FileId, FileManager};
use crate::lex::Span;
use crate::parse::{ItemKind, StmtKind};

use super::symbols::bound;
use super::visit::{self, Node};
use super::{Analysis, Sources, names};

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
    /// A name that a `use` gives.
    Use,
}

impl Analysis {
    /// What the program declares that nothing in it names again, in the
    /// order of its files: a variable or a global, a function, or what a
    /// `use` names. Nothing `pub` is among them, as another program may use
    /// it, nor a parameter, as its function may be one of several that are
    /// called alike, nor a name that starts with `_`, which says as much.
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
                    StmtKind::Binding(binding) => bound(&binding.pattern, &mut bindings),
                    StmtKind::For { var, .. } => bindings.push((&var.name, var.span)),
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
}

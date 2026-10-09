//! What each file of a program declares, for an editor to list and to find
//! by name.

use crate::file::FileId;
use crate::lex::Span;
use crate::parse::{Entry, Ident, ItemKind, Pattern, PatternKind};

use super::Analysis;

/// Something a file declares by name.
#[derive(Debug, Clone, PartialEq)]
pub struct Symbol {
    pub name: String,
    pub kind: SymbolKind,
    /// The whole of its declaration.
    pub span: Span,
    /// Where it is named in it.
    pub name_span: Span,
    /// The fields of a struct, the variants of a union or the members of an
    /// enum that it writes itself.
    pub children: Vec<Symbol>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolKind {
    Function,
    Struct,
    Union,
    Enum,
    /// A global.
    Variable,
    Field,
    Variant,
    Member,
}

impl Analysis {
    /// What `file` declares, in the order it does: its functions, those it
    /// imports, its types with what each is made of, and its globals.
    pub fn symbols(&self, file: FileId) -> Vec<Symbol> {
        let mut symbols = Vec::new();
        let items = self.program.items.iter();
        for item in items.filter(|item| item.span.file == file) {
            let symbol = |name: &Ident, kind, children| Symbol {
                name: name.name.clone(),
                kind,
                span: item.span,
                name_span: name.span,
                children,
            };
            let child = |kind| {
                move |(name, span): (&Ident, Span)| Symbol {
                    name: name.name.clone(),
                    kind,
                    span,
                    name_span: name.span,
                    children: Vec::new(),
                }
            };
            match &item.kind {
                ItemKind::Fn(decl) => {
                    symbols.push(symbol(&decl.sig.name, SymbolKind::Function, Vec::new()));
                }
                ItemKind::Extern(block) => {
                    let fns = block.fns.iter().map(|f| (&f.sig.name, f.span));
                    symbols.extend(fns.map(child(SymbolKind::Function)));
                }
                ItemKind::Struct(decl) => {
                    let fields = decl.entries.iter().filter_map(Entry::own);
                    let fields = fields.map(|field| (&field.name, field.span));
                    let fields = fields.map(child(SymbolKind::Field)).collect();
                    symbols.push(symbol(&decl.name, SymbolKind::Struct, fields));
                }
                ItemKind::Union(decl) => {
                    let variants = decl.entries.iter().filter_map(Entry::own);
                    let variants = variants.map(|variant| (&variant.name, variant.span));
                    let variants = variants.map(child(SymbolKind::Variant)).collect();
                    symbols.push(symbol(&decl.name, SymbolKind::Union, variants));
                }
                ItemKind::Enum(decl) => {
                    let members = decl.entries.iter().filter_map(Entry::own);
                    let members = members.map(|member| (&member.name, member.span));
                    let members = members.map(child(SymbolKind::Member)).collect();
                    symbols.push(symbol(&decl.name, SymbolKind::Enum, members));
                }
                ItemKind::Binding(binding) => {
                    let mut names = Vec::new();
                    bound(&binding.pattern, &mut names);
                    let global = |(name, span): (&String, Span)| Symbol {
                        name: name.clone(),
                        kind: SymbolKind::Variable,
                        span: item.span,
                        name_span: span,
                        children: Vec::new(),
                    };
                    symbols.extend(names.into_iter().map(global));
                }
                ItemKind::Use(_) => {}
            }
        }
        symbols
    }
}

/// The names that `pattern` binds, and where each is.
pub(super) fn bound<'p>(pattern: &'p Pattern, names: &mut Vec<(&'p String, Span)>) {
    match &pattern.kind {
        PatternKind::Name(name) => names.push((name, pattern.span)),
        PatternKind::Tuple(elems) | PatternKind::Array(elems) => {
            for elem in elems {
                bound(elem, names);
            }
        }
        PatternKind::Variant(_, holds) => {
            if let Some(holds) = holds {
                bound(holds, names);
            }
        }
        PatternKind::Discard | PatternKind::Literal(_) => {}
    }
}

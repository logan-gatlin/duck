//! What an editor asks of a checked program: what is written at a place,
//! where it is declared, what a call there takes, and what can be written
//! there.
//!
//! The checker keeps the type of every expression and of every name a
//! pattern binds. What a name stands for is found here, as the checker finds
//! it: a variable of the function it's in, or else an item of its module.

use std::collections::{HashMap, HashSet};
use std::ops::Range;

use crate::file::{FileId, FileManager, Settings};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{
    self, Binding, Entry, ExprKind, FnSig, Ident, ItemKind, Mutability, Param, Pattern,
    PatternKind, StmtKind, TypeKind, TypeParam,
};

pub use actions::Action;
pub use hints::{Hint, HintKind};
pub use lints::{Unused, UnusedKind};
pub use symbols::{Symbol, SymbolKind};

use super::{
    ARRAY, ARRAY_FIELDS, Checker, EXTERNREF, EnumId, Item, MODULE_CONSTS, MODULE_FUNCS, OPTION,
    Prim, RESULT, STRING, StructId, TUPLE, TYPE, TYPE_FIELDS, Ty, TypeError, VARRAY, is_builtin_type,
    lower_program,
};

mod actions;
mod hints;
mod lints;
mod symbols;
mod visit;

/// A program as checked, with the type of all that is written in it.
pub struct Analysis {
    program: Program,
    ck: Checker,
    /// The function the module runs when it is instantiated, by its name.
    start: Option<String>,
}

/// What is written at a place.
#[derive(Debug, Clone, PartialEq)]
pub struct Hover {
    /// All of what is described.
    pub span: Span,
    /// Its declaration or its type, as source.
    pub text: String,
    /// The comment on its declaration: the lines above it, or else the one
    /// that ends its line. Empty if it has none.
    pub docs: String,
}

/// Something that can be written at a place.
#[derive(Debug, Clone, PartialEq)]
pub struct Completion {
    pub name: String,
    pub kind: CompletionKind,
    /// Its type, or its signature. Empty if it has neither.
    pub detail: String,
    /// What is written with it for it to be in scope: a `use`, on a line of
    /// its own that starts at this byte of the file.
    pub import: Option<(usize, String)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompletionKind {
    /// A variable, a parameter or a global.
    Variable,
    Function,
    Struct,
    Union,
    Enum,
    /// A member of an enum.
    Member,
    /// A variant of a union.
    Variant,
    /// A field of a value, or of a type.
    Field,
    Module,
    /// A type parameter, or a type of the language's own.
    Type,
}

/// What a call takes.
#[derive(Debug, Clone, PartialEq)]
pub struct Signature {
    /// The whole of it, as source: `fn area(w: f64, h: f64 = 1.0) -> f64`.
    pub label: String,
    pub params: Vec<Parameter>,
}

/// A parameter of a [`Signature`].
#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    /// What an argument is labelled to be given to it. `None` for one of a
    /// function pointer or of a variant, which take no labels.
    pub name: Option<String>,
    /// Where in the label it is written.
    pub range: Range<usize>,
}

/// A name that the body of a function binds.
#[derive(Clone, Copy)]
struct Local<'p> {
    name: &'p str,
    /// Where it is bound.
    span: Span,
    kind: LocalKind<'p>,
}

#[derive(Clone, Copy)]
enum LocalKind<'p> {
    Param(&'p Param),
    Let,
    Var,
    /// Bound by a `for` or by an arm of a `match`.
    Bound,
}

/// What a walk of the program found at a place.
enum Found<'p> {
    /// The innermost expression there.
    Expr(&'p parse::Expr),
    /// A name where it is bound.
    Local(Local<'p>),
    /// The name of a type or of a module that leads to one, after the
    /// modules it is reached through.
    Path { names: Vec<&'p str>, span: Span },
    /// The name of a function, a struct, a union or an enum where it is
    /// declared.
    Declared(&'p Ident),
    /// A name that a `use` leads through or binds, and what it names.
    Used { item: Item, name: &'p Ident },
    /// The label of an argument of a call of `callee`.
    Label {
        callee: &'p parse::Expr,
        label: &'p Ident,
    },
    /// The name of a variant or member that `pattern` matches.
    Variant {
        pattern: &'p Pattern,
        name: &'p Ident,
    },
    /// The name of a field, a variant or a member where it is written, in
    /// the item of the program so numbered.
    Entry(usize, &'p Ident),
    /// The name of a type parameter where it is declared.
    TypeParam(&'p Ident),
    /// The statement that starts there, and the expression it is, if it's
    /// one.
    Statement(Option<&'p parse::Expr>),
}

/// A place in a file, and what is in scope there.
struct Site<'p> {
    file: FileId,
    offset: usize,
    found: Option<Found<'p>>,
    /// The variables in scope, innermost last.
    locals: Vec<Local<'p>>,
    /// The type parameters of the item the place is in.
    type_params: Vec<&'p Ident>,
}

/// What a name stands for.
enum Target<'p> {
    Local(Local<'p>),
    Item(Item),
    /// A type parameter, by the name that declares it.
    TypeParam(&'p Ident),
    /// A parameter of a function, which a label names.
    Param(&'p Param),
    /// The field, variant or member so named of the struct, union or enum
    /// that an item of the program declares, which may have it by a `use`.
    Entry(usize, &'p str),
}

/// A walk of the items of a file for what is at a place.
struct Walk<'p> {
    site: Site<'p>,
    /// Which item of the program it is in.
    item: usize,
    /// Whether it looks for the statement that starts at the place, rather
    /// than the innermost of what is there.
    statement: bool,
}

/// The source of the program's files, each read once.
struct Sources<'f> {
    read: &'f mut dyn FnMut(FileId) -> String,
    files: HashMap<FileId, String>,
}

/// Every primitive type.
const PRIMS: [Prim; 13] = [
    Prim::I8,
    Prim::I16,
    Prim::I32,
    Prim::I64,
    Prim::Int,
    Prim::U8,
    Prim::U16,
    Prim::U32,
    Prim::U64,
    Prim::Uint,
    Prim::F32,
    Prim::F64,
    Prim::Bool,
];

/// The longest initializer shown with a global: one longer says less of the
/// global than its type does.
const MAX_INITIALIZER: usize = 60;

/// What stands for a default that isn't written where its field is shown.
const ELIDED: &str = "..";

/// The functions of `module`, each with its parameters and their types, and
/// the type of what it gives, as they would be written. One that takes an
/// integer of any type has no type for it, and gives one of that type.
#[allow(clippy::type_complexity)]
const MODULE_SIGNATURES: [(&str, &[(&str, &str)], &str); 8] = [
    ("memory", &[], "varray(u8)"),
    ("size", &[], "uint"),
    ("grow", &[("pages", "uint")], "int"),
    (
        "fill",
        &[("dst", "&var u8"), ("value", "u8"), ("len", "uint")],
        "",
    ),
    (
        "copy",
        &[("dst", "&var u8"), ("src", "&u8"), ("len", "uint")],
        "",
    ),
    ("unreachable", &[], ""),
    ("count_leading_zeros", &[("value", "")], ""),
    ("count_trailing_zeros", &[("value", "")], ""),
];

/// The most declarations that a field, variant or member is looked for
/// through, each by a `use` of the next: more lead back to themselves.
const MAX_USES: usize = 64;

/// Checks `program` as [`super::errors`] does, keeping what it found of it.
pub fn analyze(program: Program, settings: &Settings) -> Analysis {
    let (ck, ..) = lower_program(&program, settings, true);
    let start = settings.start.clone();
    Analysis { program, ck, start }
}

/// What can be written after `module.`.
pub fn module_members() -> Vec<Completion> {
    let member = |kind| {
        move |name: &&str| Completion {
            name: name.to_string(),
            kind,
            detail: match module_signature(name) {
                Some(signature) => signature.label,
                None => Prim::Uint.name().to_string(),
            },
            import: None,
        }
    };
    let funcs = MODULE_FUNCS.iter().map(member(CompletionKind::Function));
    let consts = MODULE_CONSTS.iter().map(member(CompletionKind::Variable));
    funcs.chain(consts).collect()
}

/// What a call of the function `name` of `module` takes, if it is one.
fn module_signature(name: &str) -> Option<Signature> {
    let (_, params, ret) = MODULE_SIGNATURES.iter().find(|(func, ..)| *func == name)?;
    let param = |(name, ty): &(&str, &str)| {
        let text = match ty.is_empty() {
            true => name.to_string(),
            false => format!("{name}: {ty}"),
        };
        (Some(name.to_string()), text)
    };
    let tail = match ret.is_empty() {
        true => String::new(),
        false => format!(" -> {ret}"),
    };
    let params = params.iter().map(param).collect();
    Some(signature(format!("module.{name}"), params, &tail))
}

impl Analysis {
    /// The errors that [`super::check`] finds in the program.
    pub fn errors(&self) -> &[TypeError] {
        &self.ck.errors
    }

    /// What is written at byte `offset` of `file`: the declaration of what a
    /// name there stands for, or the type of the innermost expression there.
    pub fn hover(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        offset: usize,
    ) -> Option<Hover> {
        let site = self.locate(file, offset, false);
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        let described = match site.found.as_ref()? {
            Found::Local(local) => Some((local.span, self.local_text(&mut src, local)?)),
            Found::Path { names, span } => {
                let item = self.path(file, names)?;
                let text = self.item_text(&mut src, &site, item, names.last()?)?;
                Some((*span, text))
            }
            Found::Declared(name) => {
                let item = self.item(file, &name.name)?;
                let text = self.item_text(&mut src, &site, item, &name.name)?;
                Some((name.span, text))
            }
            Found::Used { item, name } => {
                let text = self.item_text(&mut src, &site, *item, &name.name)?;
                Some((name.span, text))
            }
            Found::Label { label, .. } => match self.target(&site)? {
                Target::Param(param) => Some((label.span, param_text(&mut src, param))),
                _ => None,
            },
            Found::Expr(expr) => self.expr_text(&mut src, &site, expr),
            Found::Variant { .. } | Found::Entry(..) | Found::TypeParam(_) => None,
            Found::Statement(_) => return None,
        };
        // A field, a variant or a member that is named in no expression is
        // as it is written where it is declared.
        let (span, text) = match (described, self.target(&site), site.found.as_ref()?) {
            (Some(described), ..) => described,
            (
                None,
                Some(Target::Entry(index, entry)),
                Found::Label { label: name, .. }
                | Found::Variant { name, .. }
                | Found::Entry(_, name),
            ) => {
                let declared = self.entry_span(index, entry, MAX_USES)?;
                (
                    name.span,
                    declaration(src.file(declared.file), declared.start),
                )
            }
            _ => return None,
        };
        // What an item or a field, variant or member is said to be where it
        // is declared. A module is declared by its file, which says nothing.
        let declared = match self.target(&site) {
            Some(Target::Item(_) | Target::Entry(..)) => self.definition(file, offset),
            _ => None,
        };
        let docs = match declared.filter(|declared| declared.start < declared.end) {
            Some(declared) => docs(src.file(declared.file), declared.start),
            None => String::new(),
        };
        Some(Hover { span, text, docs })
    }

    /// Where the type of what is at byte `offset` of `file` is declared: of
    /// a variable or an expression, the struct, union or enum that its type
    /// is, or points to, or is an array of.
    pub fn type_definition(&self, file: FileId, offset: usize) -> Option<Span> {
        let site = self.locate(file, offset, false);
        let mut ty = match site.found.as_ref()? {
            Found::Local(local) => self.ty_at(local.span)?,
            Found::Expr(expr) => match (&expr.kind, self.ty_at(expr.span)) {
                (_, Some(ty)) => ty,
                (ExprKind::Name(name), None) => self.ty_at(site.local(name)?.span)?,
                _ => return None,
            },
            _ => return None,
        };
        loop {
            ty = match ty {
                Ty::Ptr(id) => self.ck.pointee(id),
                Ty::Array(id) => self.ck.element(id),
                _ => break,
            };
        }
        match self.ck.known(ty) {
            Ty::Struct(id) => self.item_span(Item::Struct(id)),
            Ty::Enum(id) => self.item_span(Item::Enum(id)),
            _ => None,
        }
    }

    /// Where what the name at byte `offset` of `file` stands for is
    /// declared: a variable where it is bound, an item, a field, a variant,
    /// a member or a parameter by its name, and a module at the start of
    /// its file. `None` for what the language declares, and for what isn't
    /// a name.
    pub fn definition(&self, file: FileId, offset: usize) -> Option<Span> {
        let site = self.locate(file, offset, false);
        match self.target(&site)? {
            Target::Local(local) => Some(local.span),
            Target::Item(item) => self.item_span(item),
            Target::TypeParam(name) => Some(name.span),
            Target::Param(param) => Some(param.name.span),
            Target::Entry(index, name) => self.entry_span(index, name, MAX_USES),
        }
    }

    /// Where each name is written that stands for what the name at byte
    /// `offset` of `file` does, in every file of the program: where it is
    /// `declared` too, if that is wanted. A name of the language's own has
    /// none, as nothing declares it.
    pub fn references(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        offset: usize,
        declared: bool,
    ) -> Vec<Span> {
        let Some(wanted) = self.definition(file, offset) else {
            return Vec::new();
        };
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        // It is written as it is declared, or as a `use` names it.
        let name = src.text(wanted);
        let uses = self.program.uses.iter();
        let used = uses.flat_map(|used| used.path.last().into_iter().chain([&used.name]));
        let used: HashSet<&str> = used.map(|name| name.name.as_str()).collect();
        let mut references = Vec::new();
        for file in self.files() {
            for (start, word) in names(src.file(file)) {
                let span = Span {
                    file,
                    start,
                    end: start + word.len(),
                };
                if (word == name || used.contains(word))
                    && (declared || span != wanted)
                    && self.definition(file, start) == Some(wanted)
                {
                    references.push(span);
                }
            }
        }
        references
    }

    /// What writing another name for the one at byte `offset` of `file`
    /// changes: where that name is, and every place that stands for the
    /// same and is written as it is there, the declaration among them
    /// unless a `use` names it otherwise. A module is declared by its file,
    /// which is not among them. `None` for a name that nothing declares:
    /// one of the language's own.
    pub fn rename(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        offset: usize,
    ) -> Option<(Span, Vec<Span>)> {
        let references = self.references(files, file, offset, true);
        let holds = |span: &&Span| span.file == file && (span.start..=span.end).contains(&offset);
        let at = *references.iter().find(holds)?;
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        let name = src.text(at);
        let mut written = references;
        written.retain(|span| src.text(*span) == name);
        Some((at, written))
    }

    /// Whether writing `name` for the name at byte `offset` of `file` would
    /// give it a name that something else has where it is declared or
    /// used, so that one of the two would no longer be what is named: an
    /// item or a `use` of the same module, a variable or a type parameter
    /// in scope, or a field, variant or member of the same type.
    pub fn collides(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        offset: usize,
        name: &str,
    ) -> bool {
        let site = self.locate(file, offset, false);
        let Some(declared) = self.definition(file, offset) else {
            return false;
        };
        // Only where the name is written anew is it one of two.
        let Some((_, renamed)) = self.rename(files, file, offset) else {
            return false;
        };
        let at = |span: &Span| self.locate(span.file, span.start, false);
        match self.target(&site) {
            Some(Target::Local(_) | Target::Param(_)) => {
                renamed.iter().any(|span| at(span).local(name).is_some())
            }
            Some(Target::TypeParam(_)) => renamed.iter().any(|span| {
                at(span).type_param(name).is_some() || self.item(span.file, name).is_some()
            }),
            Some(Target::Item(_)) => {
                // In the module that declares it, and in each that a `use`
                // gives the name to.
                let declares = renamed.contains(&declared).then_some(declared.file);
                let uses = self.program.uses.iter();
                let given = uses.filter(|used| renamed.contains(&used.name.span));
                let mut modules = declares.into_iter().chain(given.map(|used| used.module));
                is_builtin_type(name) || modules.any(|module| self.item(module, name).is_some())
            }
            Some(Target::Entry(_, old)) => {
                // In every type that has it, by a `use` or as its own.
                let has = |index: usize, name: &str| self.entry_span(index, name, MAX_USES);
                let mut items = 0..self.program.items.len();
                items.any(|index| has(index, old) == Some(declared) && has(index, name).is_some())
            }
            None => false,
        }
    }

    /// Where each type that is given for one bounded by the type named at
    /// byte `offset` of `file` is declared, in the order they are: the
    /// structs that start as a struct does, and the unions or enums that a
    /// union or an enum is wider than. A generic one is that for some type
    /// arguments of its own.
    pub fn implementations(&self, file: FileId, offset: usize) -> Vec<Span> {
        let site = self.locate(file, offset, false);
        let within: Vec<Item> = match self.target(&site) {
            Some(Target::Item(Item::Struct(bound))) if !self.is_builtin(bound) => {
                let structs = (0..self.ck.structs.len() as u32).map(StructId);
                let declared = structs.filter(|id| {
                    self.ck.structs[id.0 as usize].instance.is_none() && !self.is_builtin(*id)
                });
                let within = declared.filter(|id| *id != bound && self.struct_meets(*id, bound));
                within.map(Item::Struct).collect()
            }
            Some(Target::Item(Item::Enum(bound))) => {
                let enums = (0..self.ck.enums.len() as u32).map(EnumId);
                let within = enums
                    .filter(|id| *id != bound && self.ck.meets(Ty::Enum(*id), Ty::Enum(bound)));
                within.map(Item::Enum).collect()
            }
            _ => Vec::new(),
        };
        let spans = within.into_iter().filter_map(|item| self.item_span(item));
        spans.collect()
    }

    /// The names in scope at the statement that starts at byte `offset` of
    /// `file`, nearest first: the variables of its function, the type
    /// parameters of its item, the items of its module, and the types of
    /// the language. Without a statement there, those in scope in an item.
    pub fn names(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        offset: usize,
    ) -> Vec<Completion> {
        let site = self.locate(file, offset, true);
        let importable = self.importable(files, file);
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        let mut names = Vec::new();
        for local in site.locals.iter().rev() {
            let detail = match local.kind {
                LocalKind::Param(param) => param.ty.to_string(),
                _ => self.type_at(local.span).unwrap_or_default(),
            };
            names.push(Completion {
                name: local.name.to_string(),
                kind: CompletionKind::Variable,
                detail,
                import: None,
            });
        }
        let mut items: Vec<_> = self.ck.scopes.get(&file).into_iter().flatten().collect();
        items.sort_by_key(|(name, _)| *name);
        for (name, entry) in items {
            names.push(self.item_completion(&mut src, name, entry.item));
        }
        let type_params = site.type_params.iter().map(|param| param.name.as_str());
        let prims = PRIMS.iter().map(|prim| prim.name());
        let builtins = [ARRAY, VARRAY, STRING, TUPLE, OPTION, RESULT, EXTERNREF, TYPE];
        for name in type_params.chain(prims).chain(builtins) {
            names.push(Completion {
                name: name.to_string(),
                kind: CompletionKind::Type,
                detail: String::new(),
                import: None,
            });
        }
        // Last, what a `use` would bring into scope.
        let at = self.use_site(&mut src, file);
        for (name, item, path) in importable {
            let line = format!("use {path}.{name}");
            names.push(Completion {
                import: Some((at, format!("{line}\n"))),
                detail: line,
                ..self.item_completion(&mut src, name, item)
            });
        }
        // A name stands for the nearest thing it is the name of.
        let mut seen = HashSet::new();
        names.retain(|completion| seen.insert(completion.name.clone()));
        names
    }

    /// The variants or members that the `.name` at byte `offset` of `file`
    /// may name: those of the type expected of it, or of the value that a
    /// pattern there is matched against.
    pub fn expected(&self, file: FileId, offset: usize) -> Vec<Completion> {
        let site = self.locate(file, offset, false);
        match self.expected_at(&site) {
            Some((ty, _)) => self.sum_members(ty),
            None => Vec::new(),
        }
    }

    /// What can follow the path of the `use` whose last name is at byte
    /// `offset` of `file`: the items of the module it names that `file`
    /// sees.
    pub fn module_items(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        offset: usize,
    ) -> Vec<Completion> {
        let site = self.locate(file, offset, false);
        let Some(Found::Used {
            item: Item::Module(module),
            ..
        }) = site.found
        else {
            return Vec::new();
        };
        let mut read = |id| files.contents(id);
        self.items_of(&mut Sources::new(&mut read), file, module)
    }

    /// What can follow the `.` after the expression that the statement
    /// starting at byte `offset` of `file` is: the items of a module, the
    /// members or variants of a type, or the fields of a value.
    pub fn members(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        offset: usize,
    ) -> Vec<Completion> {
        let site = self.locate(file, offset, true);
        let Some(Found::Statement(Some(expr))) = site.found else {
            return Vec::new();
        };
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        if let Some(Item::Module(module)) = self.named(&site, expr) {
            return self.items_of(&mut src, file, module);
        }
        if let Some(ty) = self.type_named(&site, expr) {
            return self.type_members(ty);
        }
        if let ExprKind::Name(name) = &expr.kind
            && site.local(name).is_none()
            && self.item(file, name).is_none()
            && (site.type_param(name).is_some() || is_builtin_type(name))
        {
            return self.type_members(Ty::Type);
        }
        match self.ty_at(expr.span) {
            Some(ty) => self.value_members(file, ty),
            None => Vec::new(),
        }
    }

    /// What a call takes of the expression that the statement starting at
    /// byte `offset` of `file` is: the parameters of a function or of a
    /// pointer to one, the fields of a struct, or the value of a variant.
    pub fn signature(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        offset: usize,
    ) -> Option<Signature> {
        let site = self.locate(file, offset, true);
        let Some(Found::Statement(Some(expr))) = site.found else {
            return None;
        };
        if let ExprKind::Module(name) = &expr.kind {
            return module_signature(&name.name);
        }
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        match self.named(&site, self.generic(&site, expr)) {
            Some(item @ (Item::Func(_) | Item::GenericFn(_))) => {
                let (_, sig) = self.fn_decl(item)?;
                return Some(self.fn_signature(&mut src, sig));
            }
            Some(Item::Struct(id)) if !self.ck.structs[id.0 as usize].union => {
                return Some(self.struct_signature(&mut src, id));
            }
            _ => {}
        }
        if let ExprKind::Field(inner, field) = &expr.kind
            && let Some((def, variant)) = self.variant(&site, inner, field)
        {
            if variant.bare {
                return None;
            }
            let head = format!("{}.{}", def.name, variant.name);
            let holds = (None, self.ck.ty_name(variant.ty));
            return Some(signature(head, vec![holds], ""));
        }
        let Ty::Fn(id) = self.ty_at(expr.span)? else {
            return None;
        };
        let (params, ret) = &self.ck.fn_tys[id.0 as usize];
        let params = params.iter().map(|param| (None, self.ck.ty_name(*param)));
        let tail = match ret {
            Ty::Unit => String::new(),
            ret => format!(" -> {}", self.ck.ty_name(*ret)),
        };
        Some(signature("fn".to_string(), params.collect(), &tail))
    }

    /// What a call takes of the `.name` at byte `offset` of `file`: the
    /// value of the variant so named of the union expected of it.
    pub fn expected_signature(&self, file: FileId, offset: usize) -> Option<Signature> {
        let site = self.locate(file, offset, false);
        let (ty, name) = self.expected_at(&site)?;
        let def = &self.ck.structs[self.ck.union_id(ty)?.0 as usize];
        let variant = def.fields.iter().find(|variant| variant.name == name)?;
        if variant.bare {
            return None;
        }
        let head = format!("{}.{}", def.name, variant.name);
        let holds = (None, self.ck.ty_name(variant.ty));
        Some(signature(head, vec![holds], ""))
    }

    /// The type expected of the `.name` found at `site`, or matched by a
    /// pattern that is one, and the name.
    fn expected_at<'p>(&self, site: &Site<'p>) -> Option<(Ty, &'p str)> {
        let (span, name) = match site.found.as_ref()? {
            Found::Variant { pattern, name } => (pattern.span, *name),
            Found::Expr(expr) => match &expr.kind {
                ExprKind::Dot(name) => (expr.span, name),
                ExprKind::Call(callee, _) => match &callee.kind {
                    ExprKind::Dot(name) => (expr.span, name),
                    _ => return None,
                },
                _ => return None,
            },
            _ => return None,
        };
        Some((self.ck.known(self.ty_at(span)?), &name.name))
    }

    /// The items of `module` that `from` sees, by name, as things to write.
    fn items_of(&self, src: &mut Sources, from: FileId, module: FileId) -> Vec<Completion> {
        let scope = self.ck.scopes.get(&module).into_iter().flatten();
        let mut items: Vec<_> = scope
            .filter(|(_, entry)| entry.is_pub || module == from)
            .collect();
        items.sort_by_key(|(name, _)| *name);
        let completion =
            |(name, entry): (&String, &super::Entry)| self.item_completion(src, name, entry.item);
        items.into_iter().map(completion).collect()
    }

    /// The items that `file` has no name for and that a `use` would give it
    /// one for, by name: those that the modules of the program other than
    /// it make `pub`, each with the path that names its module from `file`.
    fn importable(
        &self,
        files: &mut impl FileManager,
        file: FileId,
    ) -> Vec<(&String, Item, String)> {
        let mut importable = Vec::new();
        for module in self.files().into_iter().filter(|module| *module != file) {
            let Some(path) = self.use_path(files, file, module) else {
                continue;
            };
            let scope = self.ck.scopes.get(&module).into_iter().flatten();
            let items = scope.filter(|(name, entry)| {
                let named = self.item(file, name).is_some();
                entry.is_pub && !named && !matches!(entry.item, Item::Module(_))
            });
            importable.extend(items.map(|(name, entry)| (name, entry.item, path.clone())));
        }
        importable.sort_by(|a, b| (a.0, &a.2).cmp(&(b.0, &b.2)));
        importable
    }

    /// The path of a `use` that names `module` from the file `from`, if
    /// some `use` of the program names it by one that does: a path is from
    /// the root of the package that writes it, or names its dependency.
    fn use_path(
        &self,
        files: &mut impl FileManager,
        from: FileId,
        module: FileId,
    ) -> Option<String> {
        let uses = self
            .program
            .uses
            .iter()
            .filter(|used| used.target == module);
        // One of `from` itself is one that the loader took from it.
        let (own, other): (Vec<_>, Vec<_>) = uses.partition(|used| used.module == from);
        own.into_iter().chain(other).find_map(|used| {
            let path: Vec<_> = used.path.iter().map(|name| name.name.as_str()).collect();
            let dependency = match path[..] {
                [name] => files.open_package(from, name),
                _ => None,
            };
            let leads = files.open(from, &path) == Some(module) || dependency == Some(module);
            leads.then(|| used.target_path.clone())
        })
    }

    /// The byte of `file` that the line of a new `use` starts at: where its
    /// first `use` does, or else its first item, with the comment on it.
    fn use_site(&self, src: &mut Sources, file: FileId) -> usize {
        let uses = self.program.uses.iter().filter(|used| used.module == file);
        let uses = uses.filter_map(|used| Some(used.path.first()?.span.start));
        let items = self.program.items.iter().map(|item| item.span);
        let items = items
            .filter(|span| span.file == file)
            .map(|span| span.start);
        let text = src.file(file);
        let first = uses.min().or(items.min());
        let Some(mut at) = first.map(|at| line_start(text, at)) else {
            return 0;
        };
        // The lines of the comment above it.
        while let Some(above) = at.checked_sub(1).map(|end| line_start(text, end))
            && text[above..at].trim_start().starts_with('#')
        {
            at = above;
        }
        at
    }

    /// The type that `expr` names at `site`, as a type is written where a
    /// value belongs: by its name, which a module may lead to, with its
    /// type arguments if it is generic. One of those is as it is declared.
    fn type_named(&self, site: &Site, expr: &parse::Expr) -> Option<Ty> {
        let named = |expr: &parse::Expr| match (&expr.kind, self.named(site, expr)) {
            (_, Some(Item::Struct(id))) => Some(Ty::Struct(id)),
            (_, Some(Item::Enum(id))) => Some(Ty::Enum(id)),
            // The unions of the language, which no module declares.
            (ExprKind::Name(name), None) if site.local(name).is_none() => {
                self.ck.builtin_union(name).map(Ty::Struct)
            }
            _ => None,
        };
        match &expr.kind {
            // Only a generic type is given type arguments: any other struct
            // is built by what it is called with.
            ExprKind::Call(callee, _) => match named(callee)? {
                Ty::Struct(id) if !self.ck.structs[id.0 as usize].params.is_empty() => {
                    Some(Ty::Struct(id))
                }
                _ => None,
            },
            _ => named(expr),
        }
    }

    /// Walks `file` for what is at byte `offset`: the innermost of what is
    /// written there, or the `statement` that starts there.
    fn locate(&self, file: FileId, offset: usize, statement: bool) -> Site<'_> {
        let mut walk = Walk {
            site: Site {
                file,
                offset,
                found: None,
                locals: Vec::new(),
                type_params: Vec::new(),
            },
            item: 0,
            statement,
        };
        if !statement && let Some(used) = self.used(file, offset) {
            walk.site.found = Some(used);
            return walk.site;
        }
        for (index, item) in self.program.items.iter().enumerate() {
            walk.item = index;
            if walk.holds(item.span) && walk.item(item) {
                break;
            }
        }
        walk.site
    }

    /// Every file of the program, the one it is entered by first.
    pub fn files(&self) -> Vec<FileId> {
        let mut files = vec![self.program.entry];
        let items = self.program.items.iter().map(|item| item.span.file);
        let uses = self.program.uses.iter();
        for file in items.chain(uses.flat_map(|used| [used.module, used.target])) {
            if !files.contains(&file) {
                files.push(file);
            }
        }
        files
    }

    /// The name of a `use` of `file` that byte `offset` is in, of those
    /// after the module its path leads into, and what it names.
    fn used(&self, file: FileId, offset: usize) -> Option<Found<'_>> {
        let holds = |name: &Ident| name.span.start <= offset && offset <= name.span.end;
        let mut uses = self.program.uses.iter().filter(|used| used.module == file);
        uses.find_map(|used| {
            let mut item = Item::Module(used.target);
            // The last name of the path to the module is the module's.
            if let Some(name) = used.path.last().filter(|name| holds(name)) {
                return Some(Found::Used { item, name });
            }
            for name in &used.members {
                let Item::Module(module) = item else {
                    return None;
                };
                item = self.member(file, module, &name.name)?;
                if holds(name) {
                    return Some(Found::Used { item, name });
                }
            }
            let name = &used.name;
            holds(name).then_some(Found::Used { item, name })
        })
    }

    /// What the name found at `site` stands for.
    fn target<'p>(&'p self, site: &Site<'p>) -> Option<Target<'p>> {
        match site.found.as_ref()? {
            // A global is bound as a variable is, and is an item.
            Found::Local(local) => Some(match self.item(site.file, local.name) {
                Some(item @ Item::Global(_)) if self.item_span(item) == Some(local.span) => {
                    Target::Item(item)
                }
                _ => Target::Local(*local),
            }),
            Found::Declared(name) => self.item(site.file, &name.name).map(Target::Item),
            Found::Used { item, .. } => Some(Target::Item(*item)),
            Found::Path { names, .. } => match (self.path(site.file, names), &names[..]) {
                (Some(item), _) => Some(Target::Item(item)),
                (None, [name]) => site.type_param(name).map(Target::TypeParam),
                (None, _) => None,
            },
            Found::Label { callee, label } => {
                match self.named(site, self.generic(site, callee))? {
                    item @ (Item::Func(_) | Item::GenericFn(_)) => {
                        let (_, sig) = self.fn_decl(item)?;
                        let mut params = sig.params.iter();
                        let param = params.find(|param| param.name.name == label.name)?;
                        Some(Target::Param(param))
                    }
                    Item::Struct(id) => self.entry(Ty::Struct(id), &label.name),
                    _ => None,
                }
            }
            Found::Variant { pattern, name } => self.entry(self.ty_at(pattern.span)?, &name.name),
            Found::Entry(index, name) => Some(Target::Entry(*index, &name.name)),
            Found::TypeParam(name) => Some(Target::TypeParam(name)),
            Found::Expr(expr) => self.expr_target(site, expr),
            Found::Statement(_) => None,
        }
    }

    /// What the name that `expr` is, or ends in, stands for at `site`.
    fn expr_target<'p>(&'p self, site: &Site<'p>, expr: &'p parse::Expr) -> Option<Target<'p>> {
        match &expr.kind {
            ExprKind::Name(name) => {
                let local = site.local(name).map(|local| Target::Local(*local));
                let item = || self.item(site.file, name).map(Target::Item);
                let type_param = || site.type_param(name).map(Target::TypeParam);
                local.or_else(item).or_else(type_param)
            }
            ExprKind::Field(inner, field) if field.span.start <= site.offset => {
                if let Some(item) = self.named(site, expr) {
                    return Some(Target::Item(item));
                }
                // A variant or a member of a type, or a field of a value,
                // which is reached through any number of pointers.
                let mut ty = match self.type_named(site, inner) {
                    Some(ty) => ty,
                    None => self.ty_at(inner.span)?,
                };
                while let Ty::Ptr(id) = ty {
                    ty = self.ck.pointee(id);
                }
                self.entry(ty, &field.name)
            }
            // `.name`, of the type expected of it.
            ExprKind::Dot(name) => self.entry(self.ty_at(expr.span)?, &name.name),
            ExprKind::Call(callee, _) => match &callee.kind {
                ExprKind::Dot(name) if site.offset <= name.span.end => {
                    self.entry(self.ty_at(expr.span)?, &name.name)
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// The field, variant or member `name` of a `ty`, which is that of its
    /// bound for a bounded type parameter. `None` for a type that no item
    /// declares.
    fn entry<'p>(&self, ty: Ty, name: &'p str) -> Option<Target<'p>> {
        let ty = self.ck.known(ty);
        // A list has the field of the struct that it lists.
        let has = |id: StructId| {
            let mut fields = self.ck.structs[id.0 as usize].fields.iter();
            fields.find(|field| field.name == name)?.used
        };
        let ty = match ty {
            Ty::Struct(id) if self.ck.listed(ty).is_some() => Ty::Struct(has(id)?.0),
            _ => ty,
        };
        let index = match ty {
            Ty::Struct(id) if !self.is_builtin(id) => self.ck.structs[id.0 as usize].item,
            Ty::Enum(id) => self.ck.enums[id.0 as usize].item,
            _ => return None,
        };
        Some(Target::Entry(index, name))
    }

    /// Where the name of `item` is declared. A module is declared by its
    /// file, and so at the start of it.
    fn item_span(&self, item: Item) -> Option<Span> {
        let declared = |index: usize| self.program.items.get(index).map(|item| &item.kind);
        match item {
            Item::Func(_) | Item::GenericFn(_) => Some(self.fn_decl(item)?.1.name.span),
            Item::Struct(id) if self.is_builtin(id) => None,
            Item::Struct(id) => match declared(self.ck.structs[id.0 as usize].item)? {
                ItemKind::Struct(decl) => Some(decl.name.span),
                ItemKind::Union(decl) => Some(decl.name.span),
                _ => None,
            },
            Item::Enum(id) => match declared(self.ck.enums[id.0 as usize].item)? {
                ItemKind::Enum(decl) => Some(decl.name.span),
                _ => None,
            },
            Item::Global(index) => {
                let item = *self.ck.global_items.get(index)?;
                let ItemKind::Binding(binding) = declared(item)? else {
                    return None;
                };
                Some(self.global_name(binding, index, item)?.span)
            }
            Item::Module(file) => Some(Span {
                file,
                start: 0,
                end: 0,
            }),
        }
    }

    /// Where the field, variant or member `name` of the struct, union or
    /// enum that item `index` of the program declares is written: in it, or
    /// in one that it has `name` by a `use` of, through at most `uses`.
    fn entry_span(&self, index: usize, name: &str, uses: usize) -> Option<Span> {
        fn split<'p, T>(
            entries: &'p [Entry<T>],
            name: impl Fn(&'p T) -> &'p Ident,
        ) -> (Vec<&'p Ident>, Vec<&'p parse::Type>) {
            let own = entries.iter().filter_map(Entry::own).map(name);
            let used = entries.iter().filter_map(|entry| match entry {
                Entry::Use(ty) => Some(ty),
                Entry::Own(_) => None,
            });
            (own.collect(), used.collect())
        }
        let item = self.program.items.get(index)?;
        let (own, used) = match &item.kind {
            ItemKind::Struct(decl) => split(&decl.entries, |field| &field.name),
            ItemKind::Union(decl) => split(&decl.entries, |variant| &variant.name),
            ItemKind::Enum(decl) => split(&decl.entries, |member| &member.name),
            _ => return None,
        };
        if let Some(own) = own.iter().find(|own| own.name == name) {
            return Some(own.span);
        }
        let uses = uses.checked_sub(1)?;
        used.iter().find_map(|ty| {
            let mut names = Vec::new();
            let mut last = *ty;
            while let TypeKind::Qualified(module, inner) = &last.kind {
                names.push(module.name.as_str());
                last = inner;
            }
            let TypeKind::Named(used, _) = &last.kind else {
                return None;
            };
            names.push(used);
            let index = match self.path(item.span.file, &names)? {
                Item::Struct(id) if !self.is_builtin(id) => self.ck.structs[id.0 as usize].item,
                Item::Enum(id) => self.ck.enums[id.0 as usize].item,
                _ => return None,
            };
            self.entry_span(index, name, uses)
        })
    }

    /// Whether struct or union `id`, as declared, is a type that `bound`
    /// bounds, as [`Checker::meets`] finds of two types, for some types in
    /// place of the type parameters of `bound`.
    fn struct_meets(&self, id: StructId, bound: StructId) -> bool {
        let def = |id: StructId| &self.ck.structs[id.0 as usize];
        // A struct starts as its bound does, and a union is what its bound
        // starts as.
        let (starts, first) = match (def(id).union, def(bound).union) {
            (false, false) => (id, bound),
            (true, true) => (bound, id),
            _ => return false,
        };
        let declared = |ty: Ty| match ty {
            Ty::Struct(id) => Some(def(id).instance.as_ref().map_or(id, |i| i.generic)),
            _ => None,
        };
        let mut starts = self.ck.starts(Ty::Struct(starts));
        starts.any(|ty| declared(ty) == Some(first))
    }

    /// The item `name` names in `module`.
    fn item(&self, module: FileId, name: &str) -> Option<Item> {
        Some(self.ck.scopes.get(&module)?.get(name)?.item)
    }

    /// The item `name` names in `module`, if the module `from` sees it.
    fn member(&self, from: FileId, module: FileId, name: &str) -> Option<Item> {
        let entry = self.ck.scopes.get(&module)?.get(name)?;
        (entry.is_pub || module == from).then_some(entry.item)
    }

    /// The item `expr` names at `site`: a name that no variable shadows, or
    /// `module.name`, an item another module lets this one see.
    fn named(&self, site: &Site, expr: &parse::Expr) -> Option<Item> {
        match &expr.kind {
            ExprKind::Name(name) if site.local(name).is_none() => self.item(site.file, name),
            ExprKind::Field(inner, field) => match self.named(site, inner)? {
                Item::Module(module) => self.member(site.file, module, &field.name),
                _ => None,
            },
            _ => None,
        }
    }

    /// The generic type that `expr` gives type arguments at `site`, as in
    /// `Box(u8)`, which is then called or has a variant named. Any other
    /// expression is itself.
    fn generic<'e>(&self, site: &Site, expr: &'e parse::Expr) -> &'e parse::Expr {
        match &expr.kind {
            ExprKind::Call(callee, _)
                if matches!(self.named(site, callee), Some(Item::Struct(_))) =>
            {
                callee
            }
            _ => expr,
        }
    }

    /// The variant `name` of the union that `expr` names at `site`, and the
    /// union, if it names one that has it.
    fn variant(
        &self,
        site: &Site,
        expr: &parse::Expr,
        name: &parse::Ident,
    ) -> Option<(&super::StructDef, &super::FieldDef)> {
        let Ty::Struct(id) = self.type_named(site, expr)? else {
            return None;
        };
        let def = self.ck.structs.get(id.0 as usize).filter(|def| def.union)?;
        let variant = def
            .fields
            .iter()
            .find(|variant| variant.name == name.name)?;
        Some((def, variant))
    }

    /// The item that the last of `names` names in the module `from`, each
    /// of those before it being the module the next is reached through.
    fn path(&self, from: FileId, names: &[&str]) -> Option<Item> {
        let (first, rest) = names.split_first()?;
        let mut item = self.item(from, first)?;
        for name in rest {
            let Item::Module(module) = item else {
                return None;
            };
            item = self.member(from, module, name)?;
        }
        Some(item)
    }

    /// The type of the expression at `span`, or of the name a pattern binds
    /// there, if it checked.
    fn ty_at(&self, span: Span) -> Option<Ty> {
        self.ck.types.as_ref()?.get(&span).copied()
    }

    /// The name of the type of what is written at `span`, if it has one.
    fn type_at(&self, span: Span) -> Option<String> {
        Some(self.ck.ty_name(self.ty_at(span)?))
    }

    /// The function that `item` is, as declared: the block it is imported
    /// in, if it's imported, and its signature.
    fn fn_decl(&self, item: Item) -> Option<(Option<&parse::ExternBlock>, &FnSig)> {
        let index = match item {
            Item::Func(id) => *self.ck.func_items.get(id.0 as usize)?,
            Item::GenericFn(id) => *self.ck.generic_fn_items.get(id.0 as usize)?,
            _ => return None,
        };
        match (&self.program.items.get(index)?.kind, item) {
            (ItemKind::Fn(decl), _) => Some((None, &decl.sig)),
            (ItemKind::Extern(block), Item::Func(id)) => {
                let name = &self.ck.funcs[id.0 as usize].name;
                let mut fns = block.fns.iter();
                let imported = fns.find(|imported| imported.sig.name.name == *name)?;
                Some((Some(block), &imported.sig))
            }
            _ => None,
        }
    }

    /// Whether struct `id` is a union of the language's own, an instance of
    /// one, or the list of a bound, which no item declares.
    fn is_builtin(&self, id: StructId) -> bool {
        let def = &self.ck.structs[id.0 as usize];
        let generic = def.instance.as_ref().map_or(id, |i| i.generic);
        self.ck.builtin_unions.contains(&generic) || self.ck.list == Some(generic)
    }

    /// What `local` is, as it would be declared.
    fn local_text(&self, src: &mut Sources, local: &Local) -> Option<String> {
        let name = local.name;
        Some(match local.kind {
            LocalKind::Param(param) => param_text(src, param),
            LocalKind::Let => format!("let {name}: {}", self.type_at(local.span)?),
            LocalKind::Var => format!("var {name}: {}", self.type_at(local.span)?),
            LocalKind::Bound => format!("{name}: {}", self.type_at(local.span)?),
        })
    }

    /// What `expr` is at `site`, and how much of it that describes: the
    /// declaration of what a name stands for, or else its type.
    fn expr_text(
        &self,
        src: &mut Sources,
        site: &Site,
        expr: &parse::Expr,
    ) -> Option<(Span, String)> {
        match &expr.kind {
            ExprKind::Name(name) => {
                if let Some(local) = site.local(name) {
                    return Some((expr.span, self.local_text(src, local)?));
                }
                if let Some(item) = self.item(site.file, name) {
                    return Some((expr.span, self.item_text(src, site, item, name)?));
                }
            }
            ExprKind::Field(inner, field) if field.span.start <= site.offset => {
                let text = match (self.named(site, expr), self.variant(site, inner, field)) {
                    (Some(item), _) => self.item_text(src, site, item, &field.name)?,
                    (None, Some((_, variant))) if variant.bare => variant.name.clone(),
                    (None, Some((_, variant))) => {
                        format!("{}: {}", variant.name, self.ck.ty_name(variant.ty))
                    }
                    (None, None) => format!("{}: {}", field.name, self.type_at(expr.span)?),
                };
                return Some((field.span, text));
            }
            _ => {}
        }
        Some((expr.span, self.type_at(expr.span)?))
    }

    /// The declaration of `item`, which `site` names `name`.
    fn item_text(&self, src: &mut Sources, site: &Site, item: Item, name: &str) -> Option<String> {
        match item {
            Item::Func(_) | Item::GenericFn(_) => {
                let (block, sig) = self.fn_decl(item)?;
                let sig = sig_text(src, sig);
                Some(match block {
                    Some(block) => {
                        let module = block.module.as_ref();
                        let module = module.map(|module| format!(" {module:?}"));
                        format!("extern{}:\n\t{sig}", module.unwrap_or_default())
                    }
                    None => sig,
                })
            }
            Item::Struct(id) if self.is_builtin(id) => Some(self.builtin_text(id)),
            Item::Struct(id) => {
                let index = self.ck.structs[id.0 as usize].item;
                match &self.program.items.get(index)?.kind {
                    ItemKind::Struct(decl) => {
                        let head = format!(
                            "struct{} {}",
                            type_params_text(&decl.params),
                            decl.name.name
                        );
                        Some(decl_text(head, &decl.entries, |field| {
                            field_text(src, field)
                        }))
                    }
                    ItemKind::Union(decl) => {
                        let head =
                            format!("union{} {}", type_params_text(&decl.params), decl.name.name);
                        let variant = |variant: &parse::Variant| match &variant.ty {
                            Some(ty) => format!("{}: {ty}", variant.name.name),
                            None => variant.name.name.clone(),
                        };
                        Some(decl_text(head, &decl.entries, variant))
                    }
                    _ => None,
                }
            }
            Item::Enum(id) => {
                let index = self.ck.enums[id.0 as usize].item;
                let ItemKind::Enum(decl) = &self.program.items.get(index)?.kind else {
                    return None;
                };
                let head = format!("enum({}) {}", decl.ty, decl.name.name);
                let member = |member: &parse::Member| match &member.value {
                    Some(value) => format!("{} = {}", member.name.name, src.text(value.span)),
                    None => member.name.name.clone(),
                };
                Some(decl_text(head, &decl.entries, member))
            }
            Item::Global(index) => {
                let item = *self.ck.global_items.get(index)?;
                let ItemKind::Binding(binding) = &self.program.items.get(item)?.kind else {
                    return None;
                };
                let global = self.ck.globals.get(index)?.as_ref()?;
                let keyword = match binding.mutability {
                    Mutability::Let => "let",
                    Mutability::Var => "var",
                };
                let declared = self.global_name(binding, index, item)?.name;
                let ty = self.ck.ty_name(global.ty);
                // The value of one that is bound alone is its initializer.
                let value = match binding.pattern.kind {
                    PatternKind::Name(_) => src.text(binding.value.span),
                    _ => String::new(),
                };
                Some(match value.is_empty() || value.len() > MAX_INITIALIZER {
                    true => format!("{keyword} {declared}: {ty}"),
                    false => format!("{keyword} {declared}: {ty} = {value}"),
                })
            }
            Item::Module(_) => {
                let mut uses = self.program.uses.iter();
                let used = uses.find(|used| used.module == site.file && used.name.name == name)?;
                Some(format!("use {}", used.target_path))
            }
        }
    }

    /// The name that `binding`, item `item` of the program, declares global
    /// `index` with, which a module that uses it may name otherwise.
    fn global_name(&self, binding: &Binding, index: usize, item: usize) -> Option<Ident> {
        let first = self.ck.global_items.iter().position(|of| *of == item)?;
        let mut names = super::pattern_names(&binding.pattern);
        let index = index.checked_sub(first).filter(|i| *i < names.len())?;
        Some(names.swap_remove(index))
    }

    /// The declaration that union `id` of the language's own would have.
    fn builtin_text(&self, id: StructId) -> String {
        let def = &self.ck.structs[id.0 as usize];
        let generic = def.instance.as_ref().map_or(id, |i| i.generic);
        let def = &self.ck.structs[generic.0 as usize];
        let params: Vec<_> = def.params.iter().map(|ty| self.ck.ty_name(*ty)).collect();
        let mut text = format!("union({}) {}:", params.join(", "), def.name);
        for variant in &def.fields {
            text += &match variant.bare {
                true => format!("\n\t{}", variant.name),
                false => format!("\n\t{}: {}", variant.name, self.ck.ty_name(variant.ty)),
            };
        }
        text
    }

    /// `item`, which is named `name`, as something to write.
    fn item_completion(&self, src: &mut Sources, name: &str, item: Item) -> Completion {
        let (kind, detail) = match item {
            Item::Func(_) | Item::GenericFn(_) => {
                let sig = self.fn_decl(item).map(|(_, sig)| sig_text(src, sig));
                (CompletionKind::Function, sig.unwrap_or_default())
            }
            Item::Struct(id) if self.ck.structs[id.0 as usize].union => {
                (CompletionKind::Union, String::new())
            }
            Item::Struct(_) => (CompletionKind::Struct, String::new()),
            Item::Enum(_) => (CompletionKind::Enum, String::new()),
            Item::Global(index) => {
                let global = self.ck.globals.get(index).and_then(Option::as_ref);
                let ty = global.map(|global| self.ck.ty_name(global.ty));
                (CompletionKind::Variable, ty.unwrap_or_default())
            }
            Item::Module(_) => (CompletionKind::Module, String::new()),
        };
        Completion {
            name: name.to_string(),
            kind,
            detail,
            import: None,
        }
    }

    /// What can follow the `.` after the type `ty`: the members of an enum
    /// or the variants of a union, and then the fields every type has.
    fn type_members(&self, ty: Ty) -> Vec<Completion> {
        let mut members = self.sum_members(ty);
        members.extend(TYPE_FIELDS.iter().map(|name| Completion {
            name: name.to_string(),
            kind: CompletionKind::Field,
            detail: Prim::Uint.name().to_string(),
            import: None,
        }));
        members
    }

    /// The members of `ty` if it is an enum, or its variants if it is a
    /// union, as things to write.
    fn sum_members(&self, ty: Ty) -> Vec<Completion> {
        let mut members = Vec::new();
        match ty {
            Ty::Enum(id) => {
                let def = &self.ck.enums[id.0 as usize];
                members.extend(def.members.iter().map(|member| Completion {
                    name: member.name.clone(),
                    kind: CompletionKind::Member,
                    detail: def.name.clone(),
                    import: None,
                }));
            }
            Ty::Struct(id) if self.ck.structs[id.0 as usize].union => {
                let def = &self.ck.structs[id.0 as usize];
                members.extend(def.fields.iter().map(|variant| Completion {
                    name: variant.name.clone(),
                    kind: CompletionKind::Variant,
                    detail: match variant.bare {
                        true => String::new(),
                        false => self.ck.ty_name(variant.ty),
                    },
                    import: None,
                }));
            }
            _ => {}
        }
        members
    }

    /// What can follow the `.` after a value of type `ty` in `file`: `*`
    /// for a pointer, and the fields of what it points to through any
    /// number of pointers, those of them that `file` sees.
    fn value_members(&self, file: FileId, mut ty: Ty) -> Vec<Completion> {
        let field = |name: &str, ty: Ty| Completion {
            name: name.to_string(),
            kind: CompletionKind::Field,
            detail: self.ck.ty_name(ty),
            import: None,
        };
        let mut members = Vec::new();
        while let Ty::Ptr(id) = ty {
            let pointee = self.ck.pointee(id);
            if members.is_empty() {
                members.push(field("*", pointee));
            }
            ty = pointee;
        }
        // A bounded type parameter has the fields of its bound.
        let ty = self.ck.known(ty);
        match ty {
            Ty::Struct(id) if !self.ck.structs[id.0 as usize].union => {
                let fields = self.ck.structs[id.0 as usize].fields.iter().enumerate();
                let seen = fields.filter(|(i, _)| self.ck.sees_field(id, *i, file));
                members.extend(seen.map(|(_, def)| field(&def.name, def.ty)));
            }
            Ty::Tuple(id) => {
                let elems = self.ck.tuples[id.0 as usize].iter().enumerate();
                members.extend(elems.map(|(i, elem)| field(&i.to_string(), *elem)));
            }
            Ty::Array(_) => {
                let fields = ARRAY_FIELDS.iter().zip(self.ck.members(ty));
                members.extend(fields.map(|(name, ty)| field(name, ty)));
            }
            _ => {}
        }
        members
    }

    /// What a call of the function declared with `sig` takes.
    fn fn_signature(&self, src: &mut Sources, sig: &FnSig) -> Signature {
        let head = format!("fn{} {}", type_params_text(&sig.type_params), sig.name.name);
        let param = |param: &Param| (Some(param.name.name.clone()), param_text(src, param));
        let params = sig.params.iter().map(param).collect();
        let tail = sig.ret.as_ref().map(|ret| format!(" -> {ret}"));
        signature(head, params, &tail.unwrap_or_default())
    }

    /// What a constructor of struct `id` takes: its fields, each as it is
    /// declared, but for one that a `use` makes a field, whose default
    /// isn't written there.
    fn struct_signature(&self, src: &mut Sources, id: StructId) -> Signature {
        let def = &self.ck.structs[id.0 as usize];
        let decl = match self.program.items.get(def.item).map(|item| &item.kind) {
            Some(ItemKind::Struct(decl)) if !self.is_builtin(id) => Some(decl),
            _ => None,
        };
        let own = |name: &str| {
            let mut own = decl?.entries.iter().filter_map(Entry::own);
            own.find(|field| field.name.name == name)
        };
        let field = |field: &super::FieldDef| {
            let text = match own(&field.name).filter(|_| field.used.is_none()) {
                // Whether other modules see it is nothing a call gives.
                Some(own) => param_like(src, &own.name.name, &own.ty, own.default.as_ref()),
                None => {
                    let ty = self.ck.ty_name(field.ty);
                    match field.default {
                        Some(_) => format!("{}: {ty} = {ELIDED}", field.name),
                        None => format!("{}: {ty}", field.name),
                    }
                }
            };
            (Some(field.name.clone()), text)
        };
        let name = decl.map_or(&def.name, |decl| &decl.name.name);
        signature(name.clone(), def.fields.iter().map(field).collect(), "")
    }
}

impl<'p> Site<'p> {
    /// The variable `name` names here, which is the innermost so named.
    fn local(&self, name: &str) -> Option<&Local<'p>> {
        self.locals.iter().rev().find(|local| local.name == name)
    }

    /// The type parameter `name` names here, where it is declared.
    fn type_param(&self, name: &str) -> Option<&'p Ident> {
        let mut params = self.type_params.iter();
        params.find(|param| param.name == name).copied()
    }
}

impl<'p> Walk<'p> {
    /// Whether the place is in `span`, or right after it, where what is
    /// written there has just been.
    fn holds(&self, span: Span) -> bool {
        let Site { file, offset, .. } = self.site;
        span.file == file && span.start <= offset && offset <= span.end
    }

    fn find(&mut self, found: Found<'p>) -> bool {
        self.site.found = Some(found);
        true
    }

    /// Looks for the place in `item`, which holds it. Whether it was found,
    /// as every method here returns: the walk then stops, and leaves the
    /// scope as it is there.
    fn item(&mut self, item: &'p parse::Item) -> bool {
        self.site.locals.clear();
        let bounds = |params: &'p [TypeParam]| params.iter().flat_map(|p| &p.bound);
        let names = |params: &'p [TypeParam]| params.iter().map(|p| &p.name);
        let index = self.item;
        match &item.kind {
            ItemKind::Fn(decl) => {
                self.site.type_params = type_param_names(&decl.sig);
                if self.sig(&decl.sig) {
                    return true;
                }
                // A type parameter is a type by its name, and no variable.
                let params = decl.sig.params.iter().filter(|param| !param.ty.is_type());
                self.site.locals.extend(params.map(|param| Local {
                    name: &param.name.name,
                    span: param.name.span,
                    kind: LocalKind::Param(param),
                }));
                self.block(&decl.body)
            }
            ItemKind::Extern(block) => {
                self.site.type_params.clear();
                block.fns.iter().any(|f| self.sig(&f.sig))
            }
            ItemKind::Struct(decl) => {
                self.site.type_params = names(&decl.params).collect();
                self.declared(&decl.name)
                    || self.type_params(&decl.params)
                    || bounds(&decl.params).any(|bound| self.ty(bound))
                    || decl.entries.iter().any(|entry| match entry {
                        Entry::Own(field) => {
                            self.named(Found::Entry(index, &field.name), &field.name)
                                || self.ty(&field.ty)
                                || field.default.as_ref().is_some_and(|d| self.expr(d))
                        }
                        Entry::Use(ty) => self.ty(ty),
                    })
            }
            ItemKind::Union(decl) => {
                self.site.type_params = names(&decl.params).collect();
                self.declared(&decl.name)
                    || self.type_params(&decl.params)
                    || bounds(&decl.params).any(|bound| self.ty(bound))
                    || decl.entries.iter().any(|entry| match entry {
                        Entry::Own(variant) => {
                            self.named(Found::Entry(index, &variant.name), &variant.name)
                                || variant.ty.as_ref().is_some_and(|ty| self.ty(ty))
                        }
                        Entry::Use(ty) => self.ty(ty),
                    })
            }
            ItemKind::Enum(decl) => {
                self.site.type_params.clear();
                self.declared(&decl.name)
                    || self.ty(&decl.ty)
                    || decl.entries.iter().any(|entry| match entry {
                        Entry::Own(member) => {
                            self.named(Found::Entry(index, &member.name), &member.name)
                                || member.value.as_ref().is_some_and(|v| self.expr(v))
                        }
                        Entry::Use(ty) => self.ty(ty),
                    })
            }
            ItemKind::Binding(binding) => {
                self.site.type_params.clear();
                // `let _ = value` is the statement of a module.
                let discards = matches!(binding.pattern.kind, PatternKind::Discard);
                if self.statement && discards && item.span.start == self.site.offset {
                    return self.find(Found::Statement(Some(&binding.value)));
                }
                self.binding(binding)
            }
            ItemKind::Use(_) => false,
        }
    }

    /// Whether the place is in `name`, which declares an item.
    fn declared(&mut self, name: &'p Ident) -> bool {
        self.named(Found::Declared(name), name)
    }

    /// Whether the place is in `name`, which is then `found`.
    fn named(&mut self, found: Found<'p>, name: &Ident) -> bool {
        !self.statement && self.holds(name.span) && self.find(found)
    }

    /// Whether the place is in the name of one of `params`.
    fn type_params(&mut self, params: &'p [TypeParam]) -> bool {
        let mut names = params.iter().map(|param| &param.name);
        names.any(|name| self.named(Found::TypeParam(name), name))
    }

    fn sig(&mut self, sig: &'p FnSig) -> bool {
        let mut bounds = sig.type_params.iter().flat_map(|p| &p.bound);
        if self.declared(&sig.name)
            || self.type_params(&sig.type_params)
            || bounds.any(|bound| self.ty(bound))
        {
            return true;
        }
        for param in &sig.params {
            if !self.statement && self.holds(param.name.span) {
                return self.find(Found::Local(Local {
                    name: &param.name.name,
                    span: param.name.span,
                    kind: LocalKind::Param(param),
                }));
            }
            if self.ty(&param.ty) || param.default.as_ref().is_some_and(|d| self.expr(d)) {
                return true;
            }
        }
        sig.ret.as_ref().is_some_and(|ret| self.ty(ret))
    }

    /// Looks in each statement of `block`, with the names that those before
    /// it bind in scope.
    fn block(&mut self, block: &'p [parse::Stmt]) -> bool {
        let depth = self.site.locals.len();
        for stmt in block {
            if self.stmt(stmt) {
                return true;
            }
            if let StmtKind::Binding(binding) = &stmt.kind {
                self.bind(&binding.pattern, binding_kind(binding));
            }
        }
        self.site.locals.truncate(depth);
        false
    }

    fn stmt(&mut self, stmt: &'p parse::Stmt) -> bool {
        if !self.holds(stmt.span) {
            return false;
        }
        if self.statement && stmt.span.start == self.site.offset {
            let expr = match &stmt.kind {
                StmtKind::Expr(expr) => Some(expr),
                _ => None,
            };
            return self.find(Found::Statement(expr));
        }
        match &stmt.kind {
            StmtKind::Binding(binding) => self.binding(binding),
            StmtKind::Expr(expr) => self.expr(expr),
            StmtKind::If {
                cond,
                then_body,
                else_body,
            } => {
                self.expr(cond)
                    || self.block(then_body)
                    || else_body.as_ref().is_some_and(|body| self.block(body))
            }
            StmtKind::While { cond, body } => self.expr(cond) || self.block(body),
            StmtKind::For { var, iter, body } => {
                if self.expr(iter) {
                    return true;
                }
                let local = Local {
                    name: &var.name,
                    span: var.span,
                    kind: LocalKind::Bound,
                };
                if !self.statement && self.holds(var.span) {
                    return self.find(Found::Local(local));
                }
                self.site.locals.push(local);
                let found = self.block(body);
                if !found {
                    self.site.locals.pop();
                }
                found
            }
            StmtKind::Match { value, arms } => {
                if self.expr(value) {
                    return true;
                }
                for arm in arms {
                    if self.pattern(&arm.pattern, LocalKind::Bound) {
                        return true;
                    }
                    let depth = self.site.locals.len();
                    self.bind(&arm.pattern, LocalKind::Bound);
                    if self.block(&arm.body) {
                        return true;
                    }
                    self.site.locals.truncate(depth);
                }
                false
            }
            StmtKind::Defer(body) => self.block(body),
            StmtKind::Pass => false,
        }
    }

    fn binding(&mut self, binding: &'p Binding) -> bool {
        self.pattern(&binding.pattern, binding_kind(binding))
            || binding.ty.as_ref().is_some_and(|ty| self.ty(ty))
            || self.expr(&binding.value)
    }

    /// Looks for the place in the names that `pattern` binds, each a
    /// variable of kind `kind`.
    fn pattern(&mut self, pattern: &'p Pattern, kind: LocalKind<'p>) -> bool {
        if self.statement || !self.holds(pattern.span) {
            return false;
        }
        match &pattern.kind {
            PatternKind::Name(name) => self.find(Found::Local(Local {
                name,
                span: pattern.span,
                kind,
            })),
            PatternKind::Tuple(elems) | PatternKind::Array(elems) => {
                elems.iter().any(|elem| self.pattern(elem, kind))
            }
            PatternKind::Variant(name, holds) => {
                if self.holds(name.span) {
                    return self.find(Found::Variant { pattern, name });
                }
                holds
                    .as_ref()
                    .is_some_and(|holds| self.pattern(holds, kind))
            }
            PatternKind::Discard | PatternKind::Literal(_) => false,
        }
    }

    /// Brings the names that `pattern` binds into scope.
    fn bind(&mut self, pattern: &'p Pattern, kind: LocalKind<'p>) {
        match &pattern.kind {
            PatternKind::Name(name) => self.site.locals.push(Local {
                name,
                span: pattern.span,
                kind,
            }),
            PatternKind::Tuple(elems) | PatternKind::Array(elems) => {
                for elem in elems {
                    self.bind(elem, kind);
                }
            }
            PatternKind::Variant(_, holds) => {
                if let Some(holds) = holds {
                    self.bind(holds, kind);
                }
            }
            PatternKind::Discard | PatternKind::Literal(_) => {}
        }
    }

    /// Looks for the innermost expression of `expr` that holds the place,
    /// which is `expr` itself if nothing in it does.
    fn expr(&mut self, expr: &'p parse::Expr) -> bool {
        if self.statement || !self.holds(expr.span) {
            return false;
        }
        let within = match &expr.kind {
            ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_)
            | ExprKind::Bool(_)
            | ExprKind::Unit
            | ExprKind::Name(_)
            | ExprKind::Module(_)
            | ExprKind::Placeholder
            | ExprKind::Dot(_)
            | ExprKind::Break
            | ExprKind::Continue => false,
            ExprKind::Tuple(elems) | ExprKind::List(elems) => {
                elems.iter().any(|elem| self.expr(elem))
            }
            ExprKind::Repeat(a, b)
            | ExprKind::Binary(_, a, b)
            | ExprKind::Index(a, b)
            | ExprKind::Pipe(a, b) => self.expr(a) || self.expr(b),
            ExprKind::Unary(_, inner)
            | ExprKind::Deref(inner)
            | ExprKind::AddrOf(_, inner)
            | ExprKind::Field(inner, _) => self.expr(inner),
            ExprKind::Call(callee, args) => {
                let mut labels = args.iter().filter_map(|arg| arg.label.as_ref());
                if let Some(label) = labels.find(|label| self.holds(label.span)) {
                    return self.find(Found::Label { callee, label });
                }
                // `.name(value)` has the type that `.name` alone would.
                let dot = matches!(callee.kind, ExprKind::Dot(_));
                !dot && self.expr(callee) || args.iter().any(|arg| self.expr(&arg.value))
            }
            ExprKind::Cast(inner, ty, _) => self.expr(inner) || self.ty(ty),
            ExprKind::FnType(ty) => self.ty(ty),
            ExprKind::Assign { target, value, .. } => self.expr(target) || self.expr(value),
            ExprKind::Return(value) => value.as_deref().is_some_and(|value| self.expr(value)),
        };
        within || self.find(Found::Expr(expr))
    }

    /// Looks for the name of a type that holds the place in `ty`.
    fn ty(&mut self, ty: &'p parse::Type) -> bool {
        if self.statement || !self.holds(ty.span) {
            return false;
        }
        let mut names = Vec::new();
        let mut last = ty;
        while let TypeKind::Qualified(module, inner) = &last.kind {
            names.push(module.name.as_str());
            if self.holds(module.span) {
                let span = module.span;
                return self.find(Found::Path { names, span });
            }
            last = inner;
        }
        match &last.kind {
            TypeKind::Named(name, args) => {
                if args.iter().flatten().any(|arg| self.ty(arg)) {
                    return true;
                }
                let span = Span {
                    end: last.span.start + name.len(),
                    ..last.span
                };
                names.push(name);
                self.holds(span) && self.find(Found::Path { names, span })
            }
            TypeKind::Pointer(_, pointee) => self.ty(pointee),
            TypeKind::Fn(params, ret) => {
                params.iter().any(|param| self.ty(param))
                    || ret.as_ref().is_some_and(|ret| self.ty(ret))
            }
            TypeKind::Qualified(..) => false,
        }
    }
}

impl<'f> Sources<'f> {
    fn new(read: &'f mut dyn FnMut(FileId) -> String) -> Self {
        Self {
            read,
            files: HashMap::new(),
        }
    }

    /// The source of `file`.
    fn file(&mut self, file: FileId) -> &str {
        let read = &mut self.read;
        self.files.entry(file).or_insert_with(|| read(file))
    }

    /// What is written at `span`, on one line.
    fn text(&mut self, span: Span) -> String {
        let text = self.file(span.file);
        let text = text.get(span.start..span.end).unwrap_or_default();
        text.split_whitespace().collect::<Vec<_>>().join(" ")
    }
}

/// The byte that the line of byte `at` of `text` starts at.
fn line_start(text: &str, at: usize) -> usize {
    text[..at.min(text.len())].rfind('\n').map_or(0, |i| i + 1)
}

/// What is declared on a line of its own at byte `at` of `text`, as it is
/// written: the line from there on, without the comment that ends it.
fn declaration(text: &str, at: usize) -> String {
    let rest = &text[at.min(text.len())..];
    let line = rest.lines().next().unwrap_or_default();
    line[..line.len() - comment(line).len()]
        .trim_end()
        .to_string()
}

/// The comment that ends `line`, from the `#` that starts it, which is the
/// first that isn't in a string. Empty if it has none.
fn comment(line: &str) -> &str {
    let (mut quoted, mut escaped) = (false, false);
    for (i, c) in line.char_indices() {
        match c {
            '#' if !quoted => return &line[i..],
            '"' if !escaped => quoted = !quoted,
            _ => {}
        }
        escaped = c == '\\' && !escaped;
    }
    ""
}

/// The comment on what is declared at byte `at` of `text`: the lines of
/// comment right above its line, or else the one that ends its line, each
/// without what marks it one.
fn docs(text: &str, at: usize) -> String {
    let said = |comment: &str| {
        let said = comment.trim_start().trim_start_matches('#');
        said.strip_prefix(' ')
            .unwrap_or(said)
            .trim_end()
            .to_string()
    };
    let mut start = line_start(text, at);
    let mut lines = Vec::new();
    while let Some(above) = start.checked_sub(1).map(|end| line_start(text, end))
        && text[above..start].trim_start().starts_with('#')
    {
        lines.push(said(&text[above..start]));
        start = above;
    }
    if !lines.is_empty() {
        lines.reverse();
        return lines.join("\n");
    }
    let rest = &text[at.min(text.len())..];
    said(comment(rest.lines().next().unwrap_or_default()))
}

/// Each run of what a name is written with in `text`, and the byte it
/// starts at, but for those that start as a number does.
fn names(text: &str) -> impl Iterator<Item = (usize, &str)> {
    let in_name = |c: char| c == '_' || c.is_alphanumeric();
    let mut rest = text.char_indices().peekable();
    std::iter::from_fn(move || {
        loop {
            let (start, first) = rest.find(|(_, c)| in_name(*c))?;
            let mut end = start + first.len_utf8();
            while let Some((at, c)) = rest.next_if(|(_, c)| in_name(*c)) {
                end = at + c.len_utf8();
            }
            if !first.is_numeric() {
                return Some((start, &text[start..end]));
            }
        }
    })
}

/// The names of the type parameters of `sig`: those a call infers, then its
/// parameters of type `type`.
fn type_param_names(sig: &FnSig) -> Vec<&Ident> {
    let inferred = sig.type_params.iter().map(|param| &param.name);
    let given = sig.params.iter().filter(|param| param.ty.is_type());
    inferred.chain(given.map(|param| &param.name)).collect()
}

fn binding_kind<'p>(binding: &Binding) -> LocalKind<'p> {
    match binding.mutability {
        Mutability::Let => LocalKind::Let,
        Mutability::Var => LocalKind::Var,
    }
}

/// `head(params)tail`, and where in it each of `params` is.
fn signature(head: String, params: Vec<(Option<String>, String)>, tail: &str) -> Signature {
    let mut label = head + "(";
    let mut placed = Vec::new();
    for (i, (name, text)) in params.into_iter().enumerate() {
        if i > 0 {
            label += ", ";
        }
        let start = label.len();
        label += &text;
        placed.push(Parameter {
            name,
            range: start..label.len(),
        });
    }
    label += ")";
    label += tail;
    Signature {
        label,
        params: placed,
    }
}

/// `sig` as it is written, on one line.
fn sig_text(src: &mut Sources, sig: &FnSig) -> String {
    let params: Vec<_> = sig.params.iter().map(|p| param_text(src, p)).collect();
    let ret = sig.ret.as_ref().map(|ret| format!(" -> {ret}"));
    format!(
        "fn{} {}({}){}",
        type_params_text(&sig.type_params),
        sig.name.name,
        params.join(", "),
        ret.unwrap_or_default()
    )
}

/// The `(A, B: Bound)` that declares `params`, if there are any.
fn type_params_text(params: &[TypeParam]) -> String {
    if params.is_empty() {
        return String::new();
    }
    let param = |param: &TypeParam| match &param.bound[..] {
        [] => param.name.name.clone(),
        [bound] => format!("{}: {bound}", param.name.name),
        bounds => {
            let bounds: Vec<_> = bounds.iter().map(|bound| bound.to_string()).collect();
            format!("{}: ({})", param.name.name, bounds.join(", "))
        }
    };
    let params: Vec<_> = params.iter().map(param).collect();
    format!("({})", params.join(", "))
}

fn param_text(src: &mut Sources, param: &Param) -> String {
    param_like(src, &param.name.name, &param.ty, param.default.as_ref())
}

fn field_text(src: &mut Sources, field: &parse::Field) -> String {
    let text = param_like(src, &field.name.name, &field.ty, field.default.as_ref());
    match field.is_pub {
        true => format!("pub {text}"),
        false => text,
    }
}

/// `name: ty`, or `name: ty = default`.
fn param_like(
    src: &mut Sources,
    name: &str,
    ty: &parse::Type,
    default: Option<&parse::Expr>,
) -> String {
    match default {
        Some(default) => format!("{name}: {ty} = {}", src.text(default.span)),
        None => format!("{name}: {ty}"),
    }
}

/// The declaration that starts with `head` and has `entries`, each of its
/// own being what `own` writes.
fn decl_text<T>(head: String, entries: &[Entry<T>], mut own: impl FnMut(&T) -> String) -> String {
    let mut text = head + ":";
    for entry in entries {
        text += "\n\t";
        text += &match entry {
            Entry::Own(entry) => own(entry),
            Entry::Use(ty) => format!("use {ty}"),
        };
    }
    if entries.is_empty() {
        text += "\n\tpass";
    }
    text
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::load;
    use std::ops::Range;

    /// Files named by the paths that use them. The first is the entry point.
    struct Memory(Vec<(&'static str, &'static str)>);

    impl Memory {
        /// The file named `name`, and where `text` first is in it.
        fn at(&self, name: &str, text: &str) -> (FileId, usize) {
            let index = self.0.iter().position(|file| file.0 == name).unwrap();
            let offset = self.0[index].1.find(text).unwrap();
            (Self::mint_file_id(index), offset)
        }

        fn index(&self, id: FileId) -> usize {
            let mut indices = 0..self.0.len();
            indices.find(|i| Self::mint_file_id(*i) == id).unwrap()
        }
    }

    impl FileManager for Memory {
        fn entry_point(&mut self) -> FileId {
            Self::mint_file_id(0)
        }

        fn display_name(&mut self, id: FileId) -> String {
            self.0[self.index(id)].0.to_string()
        }

        fn contents(&mut self, id: FileId) -> String {
            self.0[self.index(id)].1.to_string()
        }

        fn open(&mut self, _from: FileId, path: &[&str]) -> Option<FileId> {
            let name = path.join(".");
            let index = self.0.iter().position(|file| file.0 == name)?;
            Some(Self::mint_file_id(index))
        }

        fn open_package(&mut self, _from: FileId, _name: &str) -> Option<FileId> {
            None
        }

        fn settings(&mut self) -> Settings {
            Settings::default()
        }
    }

    const GEO: &str = "\
pub struct Point:
    pub x: f32
    pub y: f32 = 0.0
    id: i32 = 0
pub let origin = Point(x: 0.0)
pub fn len(p: &Point, scale: f32 = 1.0) -> f32:
    return p.x * scale
fn hidden():
    pass
";

    const MAIN: &str = "\
use geo
use geo.Point
extern \"js\":
    fn log(n: i32) = \"log_int\"
enum(u8) Color:
    red
    green = 5
union Shape:
    circle: f32
    empty
struct Head:
    id: i32
struct Named:
    use Head
    name: array(u8) = \"\"
struct(T) Box:
    value: T
pub let LIMIT = 100
let (low, high) = (1, 2.5)
fn(T) boxed(value: T, at: &var Box(T)) -> &var Box(T):
    at.value = value
    return at
fn(T: Head) id_of(x: &T) -> i32:
    x
    return x.id
fn demo(p: &var Point, s: Shape, f: fn(i32, u8) -> i32, t: tuple(i32, f64)) -> f32:
    let d = geo.len(p, scale: 2.0)
    var n = LIMIT + 1
    for c in Color:
        log(c as u8 as i32)
    match s:
        .circle(r):
            let inner = r
            inner
        else:
            pass
    p.y = d
    p
    t
    f
    geo
    Color
    Shape
    geo.origin
    Shape.circle
    Named
    Box(u8)
    log
    boxed
    geo.len
    pass
    return n as f32 + 1.5
fn strings(s: array(u8)) -> uint:
    s
    return s.len
fn bytes(T: type, count: uint) -> uint:
    T
    return T.size * count
";

    fn files() -> Memory {
        Memory(vec![("main", MAIN), ("geo", GEO)])
    }

    fn analysis(files: &mut Memory) -> Analysis {
        let (program, errors) = load::load_partial(files);
        assert_eq!(errors, []);
        analyze(program, &Settings::default())
    }

    /// What hovering the first `text` of file `name` gives: what is
    /// described, and how.
    fn hover(name: &str, text: &str) -> Option<(&'static str, String)> {
        let mut files = files();
        let analysis = analysis(&mut files);
        let (file, offset) = files.at(name, text);
        let hover = analysis.hover(&mut files, file, offset)?;
        let src = files.0[files.index(hover.span.file)].1;
        Some((&src[hover.span.start..hover.span.end], hover.text))
    }

    fn described(of: &'static str, text: &str) -> Option<(&'static str, String)> {
        Some((of, text.to_string()))
    }

    /// Each completion as `name` or `name: detail`.
    fn shown(completions: Vec<Completion>) -> Vec<String> {
        let show = |c: Completion| match c.detail.is_empty() {
            true => c.name,
            false => format!("{}: {}", c.name, c.detail),
        };
        completions.into_iter().map(show).collect()
    }

    /// What can follow a `.` after the statement that the line `line` of
    /// `main` is.
    fn members(line: &str) -> Vec<String> {
        let mut files = files();
        let analysis = analysis(&mut files);
        let (file, offset) = files.at("main", line);
        shown(analysis.members(
            &mut files,
            file,
            offset + line.len() - line.trim_start().len(),
        ))
    }

    /// What a call of the statement that the line `line` of `main` is
    /// takes, with each parameter in brackets.
    fn signature(line: &str) -> Option<String> {
        let mut files = files();
        let analysis = analysis(&mut files);
        let (file, offset) = files.at("main", line);
        let offset = offset + line.len() - line.trim_start().len();
        let Signature { mut label, params } = analysis.signature(&mut files, file, offset)?;
        for param in params.iter().rev() {
            label.insert(param.range.end, ']');
            label.insert(param.range.start, '[');
        }
        Some(label)
    }

    #[test]
    fn hovering_a_variable_gives_its_type() {
        assert_eq!(hover("main", "d = geo"), described("d", "let d: f32"));
        assert_eq!(hover("main", "d\n    p\n"), described("d", "let d: f32"));
        assert_eq!(hover("main", "n = LIMIT"), described("n", "var n: i32"));
        assert_eq!(hover("main", "n as f32"), described("n", "var n: i32"));
        // A parameter is as it is declared.
        assert_eq!(hover("main", "p, scale"), described("p", "p: &var Point"));
        assert_eq!(
            hover("geo", "scale\n"),
            described("scale", "scale: f32 = 1.0")
        );
        // What a `for` and an arm of a `match` bind.
        assert_eq!(hover("main", "c in"), described("c", "c: Color"));
        assert_eq!(hover("main", "c as u8"), described("c", "c: Color"));
        assert_eq!(hover("main", "r):"), described("r", "r: f32"));
        assert_eq!(hover("main", "r\n"), described("r", "r: f32"));
        // A target of an assignment is read as any other.
        assert_eq!(hover("main", "p.y = d"), described("p", "p: &var Point"));
        assert_eq!(hover("main", "y = d"), described("y", "y: f32"));
        // A generic function's are of the types it is declared with.
        assert_eq!(
            hover("main", "at.value"),
            described("at", "at: &var Box(T)")
        );
        assert_eq!(
            hover("main", "value = value"),
            described("value", "value: T")
        );
    }

    #[test]
    fn hovering_a_name_gives_its_declaration() {
        assert_eq!(
            hover("main", "len(p"),
            described("len", "fn len(p: &Point, scale: f32 = 1.0) -> f32")
        );
        assert_eq!(hover("main", "geo.len(p"), described("geo", "use geo"));
        assert_eq!(
            hover("main", "log(c"),
            described("log", "extern \"js\":\n\tfn log(n: i32)")
        );
        assert_eq!(
            hover("main", "LIMIT + 1"),
            described("LIMIT", "let LIMIT: i32 = 100")
        );
        // One of several that a pattern binds has no value of its own.
        assert_eq!(hover("main", "high)"), described("high", "let high: f64"));
        assert_eq!(
            hover("main", "Color:\n        log"),
            described("Color", "enum(u8) Color:\n\tred\n\tgreen = 5")
        );
        // A type where it is written as one.
        assert_eq!(
            hover("main", "Shape, f:"),
            described("Shape", "union Shape:\n\tcircle: f32\n\tempty")
        );
        let point = "struct Point:\n\tpub x: f32\n\tpub y: f32 = 0.0\n\tid: i32 = 0";
        assert_eq!(hover("main", "Point, s:"), described("Point", point));
        assert_eq!(
            hover("main", "Box(T)) ->"),
            described("Box", "struct(T) Box:\n\tvalue: T")
        );
        assert_eq!(
            hover("main", "Head) id_of"),
            described("Head", "struct Head:\n\tid: i32")
        );
        // Nothing declares a type of the language, or a type parameter.
        assert_eq!(hover("main", "i32, u8)"), None);
        assert_eq!(hover("main", "T, at:"), None);
    }

    #[test]
    fn hovering_an_expression_gives_its_type() {
        assert_eq!(hover("main", "1.5"), described("1.5", "f32"));
        assert_eq!(hover("main", "2.5"), described("2.5", "f64"));
        assert_eq!(
            hover("main", " scale: 2.0"),
            described("geo.len(p, scale: 2.0)", "f32")
        );
        assert_eq!(hover("main", "+ 1\n"), described("LIMIT + 1", "i32"));
        assert_eq!(hover("main", "id\n"), described("id", "id: i32"));
        assert_eq!(hover("main", "as u8 as"), described("c as u8", "u8"));
        // A variant is what it holds, and a label is nothing of its call's.
        assert_eq!(
            hover("main", "circle\n    Named"),
            described("circle", "circle: f32")
        );
        assert_eq!(
            hover("main", "size * count"),
            described("size", "size: uint")
        );
        // A label is the parameter it names.
        assert_eq!(
            hover("main", "scale: 2.0"),
            described("scale", "scale: f32 = 1.0")
        );
    }

    #[test]
    fn the_names_in_scope_are_nearest_first() {
        let mut files = files();
        let analysis = analysis(&mut files);
        let names = |files: &mut Memory, text: &str| {
            let (file, offset) = files.at("main", text);
            shown(analysis.names(files, file, offset))
        };
        let inner = names(&mut files, "inner\n        else");
        assert_eq!(
            inner[..8],
            [
                "inner: f32",
                "r: f32",
                "n: i32",
                "d: f32",
                "t: tuple(i32, f64)",
                "f: fn(i32, u8) -> i32",
                "s: Shape",
                "p: &var Point",
            ]
        );
        // Then the items of the module, by name, and the types.
        assert_eq!(inner[8..11], ["Box", "Color", "Head"]);
        assert!(inner.contains(&"LIMIT: i32".to_string()), "{inner:?}");
        assert!(inner.contains(&"geo".to_string()), "{inner:?}");
        assert!(inner.contains(&"uint".to_string()), "{inner:?}");
        let boxed = "boxed: fn(T) boxed(value: T, at: &var Box(T)) -> &var Box(T)";
        assert!(inner.contains(&boxed.to_string()), "{inner:?}");

        // What a block binds is out of scope after it, as what a later
        // statement binds is before it.
        let last = names(&mut files, "pass\n    return n");
        assert_eq!(last[..3], ["n: i32", "d: f32", "t: tuple(i32, f64)"]);
        let first = names(&mut files, "let d = geo");
        assert_eq!(first[..2], ["t: tuple(i32, f64)", "f: fn(i32, u8) -> i32"]);
        // A type parameter is in scope in its function.
        let generic = names(&mut files, "x\n    return x.id");
        assert_eq!(generic[..1], ["x: &T"]);
        assert!(generic.contains(&"T".to_string()), "{generic:?}");
        assert!(!last.contains(&"T".to_string()), "{last:?}");
        // One that a call gives is no variable.
        let given = names(&mut files, "T\n    return T.size");
        assert_eq!(given[..2], ["count: uint", "Box"]);
        assert!(given.contains(&"T".to_string()), "{given:?}");
    }

    #[test]
    fn the_body_of_a_defer_is_a_block_of_its_own() {
        let src = "\
extern:
    fn log(n: i32)
fn f(h: i32):
    defer log(h)
    defer:
        let held = h
        log(held)
    pass
";
        let mut files = Memory(vec![("main", src)]);
        let analysis = analysis(&mut files);
        let (file, offset) = files.at("main", "h)\n");
        let hover = analysis.hover(&mut files, file, offset).unwrap();
        assert_eq!(&src[hover.span.start..hover.span.end], "h");
        assert_eq!(hover.text, "h: i32");
        let mut names = |text: &str| {
            let (file, offset) = files.at("main", text);
            shown(analysis.names(&mut files, file, offset))
        };
        assert_eq!(names("log(held)")[..2], ["held: i32", "h: i32"]);
        // What the body binds is out of scope after it.
        assert_eq!(names("pass")[..2], ["h: i32", "f: fn f(h: i32)"]);
    }

    #[test]
    fn a_value_has_its_fields() {
        // Through any number of pointers, but for those another module
        // keeps to itself.
        assert_eq!(members("    p\n"), ["*: Point", "x: f32", "y: f32"]);
        assert_eq!(members("    t\n"), ["0: i32", "1: f64"]);
        assert_eq!(
            members("    s\n    return s.len"),
            ["ptr: &u8", "len: uint"]
        );
        assert_eq!(members("    geo.origin\n"), ["x: f32", "y: f32"]);
        // A bounded type parameter has those of its bound.
        assert_eq!(members("    x\n"), ["*: T", "id: i32"]);
        assert_eq!(members("    f\n"), [] as [&str; 0]);
    }

    #[test]
    fn a_type_has_its_members_and_a_module_its_items() {
        assert_eq!(
            members("    Color\n"),
            ["red: Color", "green: Color", "size: uint", "align: uint"]
        );
        assert_eq!(
            members("    Shape\n"),
            ["circle: f32", "empty", "size: uint", "align: uint"]
        );
        assert_eq!(members("    Named\n"), ["size: uint", "align: uint"]);
        assert_eq!(members("    T\n"), ["size: uint", "align: uint"]);
        assert_eq!(
            members("    geo\n"),
            [
                "Point",
                "len: fn len(p: &Point, scale: f32 = 1.0) -> f32",
                "origin: Point"
            ]
        );
        let module: Vec<_> = module_members().into_iter().map(|m| m.name).collect();
        assert!(module.contains(&"grow".to_string()), "{module:?}");
        assert!(module.contains(&"page_size".to_string()), "{module:?}");
        // Each constant is a `uint`.
        let consts = module_members()
            .into_iter()
            .filter(|m| MODULE_CONSTS.contains(&&*m.name));
        let consts: Vec<_> = consts
            .map(|m| format!("{}: {}", m.name, m.detail))
            .collect();
        assert_eq!(consts, ["page_size: uint", "max: uint"]);
    }

    #[test]
    fn a_call_takes_what_is_declared() {
        assert_eq!(
            signature("    geo.len\n").unwrap(),
            "fn len([p: &Point], [scale: f32 = 1.0]) -> f32"
        );
        assert_eq!(
            signature("    boxed\n").unwrap(),
            "fn(T) boxed([value: T], [at: &var Box(T)]) -> &var Box(T)"
        );
        assert_eq!(signature("    log\n").unwrap(), "fn log([n: i32])");
        // A constructor takes the fields, of which those a `use` gives
        // have their defaults elsewhere.
        assert_eq!(
            signature("    Named\n").unwrap(),
            "Named([id: i32], [name: array(u8) = \"\"])"
        );
        assert_eq!(signature("    Box(u8)\n").unwrap(), "Box([value: T])");
        assert_eq!(
            signature("    Shape.circle\n").unwrap(),
            "Shape.circle([f32])"
        );
        // A pointer to a function takes arguments without names.
        assert_eq!(signature("    f\n").unwrap(), "fn([i32], [u8]) -> i32");
        assert_eq!(signature("    t\n"), None);
        assert_eq!(signature("    Color\n"), None);
    }

    const PLACES: &str = "\
pub struct Point:
    pub x: f32
    pub y: f32 = 0.0
pub enum(u8) Color:
    red
    green = 5
pub let origin = Point(x: 0.0)
pub fn len(p: &Point, scale: f32 = 1.0) -> f32:
    return p.x * scale
";

    const NAMES: &str = "\
use places
use places.{Point, len as length}
extern:
    fn log(n: i32)
union Shape:
    circle: f32
    empty
union Wide:
    use Shape
    square: f32
struct Head:
    id: i32
struct Named:
    use Head
    name: array(u8)
struct(T) Box:
    value: T
struct(T) Pair:
    use Box(T)
    other: T
struct Tagged:
    value: i32
    tag: u8
enum(u8) Warm:
    red
enum(u8) Hot:
    use Warm
    white
let (low, high) = (1, 2)
fn(T: Head) id_of(x: &T, n: Named) -> i32:
    return x.id + n.id
fn pick(T: type, at: &T) -> &T:
    return at
fn demo(p: &Point, w: Wide, s: Shape) -> Shape:
    let d = length(p, scale: 2.0)
    let q = Point(x: d)
    log(high)
    match w:
        .circle(r):
            return .circle(r)
        .square(side):
            return Shape.circle(side)
        else:
            pass
    let c = places.Color.green
    let h = Hot.red
    return .empty
";

    fn names() -> Memory {
        Memory(vec![("main", NAMES), ("places", PLACES)])
    }

    /// Where `name` is in the first `text` of `main`.
    fn place(files: &Memory, text: &str, name: &str) -> (FileId, usize) {
        let (file, offset) = files.at("main", text);
        (file, offset + text.find(name).unwrap())
    }

    /// Where what `name` stands for is declared, in the first `text` of
    /// `main`: the file, and the line from there on.
    fn definition(text: &str, name: &str) -> Option<(&'static str, &'static str)> {
        let mut files = names();
        let analysis = analysis(&mut files);
        let (file, offset) = place(&files, text, name);
        let span = analysis.definition(file, offset)?;
        let (file, src) = files.0[files.index(span.file)];
        Some((file, src[span.start..].lines().next().unwrap_or_default()))
    }

    /// The names that declare the types given for one bounded by what
    /// `name` names, in the first `text` of `main`.
    fn implementations(text: &str, name: &str) -> Vec<&'static str> {
        let mut files = names();
        let analysis = analysis(&mut files);
        let (file, offset) = place(&files, text, name);
        let spans = analysis.implementations(file, offset);
        let text = |span: Span| &files.0[files.index(span.file)].1[span.start..span.end];
        spans.into_iter().map(text).collect()
    }

    #[test]
    fn a_name_is_defined_where_it_is_declared() {
        let main = |line: &'static str| Some(("main", line));
        let places = |line: &'static str| Some(("places", line));
        // A variable where it is bound, and an item by its name.
        assert_eq!(definition("d)\n", "d"), main("d = length(p, scale: 2.0)"));
        assert_eq!(
            definition("(p, scale", "p"),
            main("p: &Point, w: Wide, s: Shape) -> Shape:")
        );
        assert_eq!(definition("side)\n", "side"), main("side):"));
        assert_eq!(definition("log(high)", "log"), main("log(n: i32)"));
        assert_eq!(definition("log(high)", "high"), main("high) = (1, 2)"));
        assert_eq!(definition("w: Wide", "Wide"), main("Wide:"));
        assert_eq!(definition("-> Shape:", "Shape"), main("Shape:"));
        // One of another module, by whatever name it is used.
        let len = places("len(p: &Point, scale: f32 = 1.0) -> f32:");
        assert_eq!(definition("length(p", "length"), len);
        assert_eq!(definition("len as length", "len"), len);
        assert_eq!(definition("len as length", "length"), len);
        assert_eq!(definition("Point(x: d)", "Point"), places("Point:"));
        assert_eq!(definition("{Point, len", "Point"), places("Point:"));
        assert_eq!(definition("places.Color.green", "Color"), places("Color:"));
        // A module is its file.
        assert_eq!(
            definition("places.Color.green", "places"),
            places("pub struct Point:")
        );
        assert_eq!(
            definition("use places\n", "places"),
            places("pub struct Point:")
        );
        // Where it is declared, it is itself.
        assert_eq!(definition("Head:\n", "Head"), main("Head:"));
        assert_eq!(
            definition("demo(p", "demo"),
            main("demo(p: &Point, w: Wide, s: Shape) -> Shape:")
        );
        assert_eq!(definition("low, high", "low"), main("low, high) = (1, 2)"));
        // A type parameter, of either kind.
        assert_eq!(
            definition("x: &T, n", "T"),
            main("T: Head) id_of(x: &T, n: Named) -> i32:")
        );
        assert_eq!(definition("at: &T", "T"), main("T: type, at: &T) -> &T:"));
        // Nothing declares what the language does, or what is no name.
        assert_eq!(definition("n: i32", "i32"), None);
        assert_eq!(definition("scale: 2.0", "2.0"), None);
    }

    #[test]
    fn a_field_a_variant_and_a_member_are_defined_where_they_are_written() {
        let main = |line: &'static str| Some(("main", line));
        let places = |line: &'static str| Some(("places", line));
        assert_eq!(definition("Point(x: d)", "x"), places("x: f32"));
        assert_eq!(
            definition("scale: 2.0", "scale"),
            places("scale: f32 = 1.0) -> f32:")
        );
        assert_eq!(
            definition("places.Color.green", "green"),
            places("green = 5")
        );
        assert_eq!(
            definition("Shape.circle(side)", "circle"),
            main("circle: f32")
        );
        // Of the type of a value, through its pointers and its bound.
        assert_eq!(definition("x.id +", "id"), main("id: i32"));
        // Of the type expected, for a `.name` and for a pattern.
        assert_eq!(
            definition("return .circle(r)", "circle"),
            main("circle: f32")
        );
        assert_eq!(definition("return .empty", "empty"), main("empty"));
        assert_eq!(definition(".square(side):", "square"), main("square: f32"));
        // In the declaration that a `use` has it of.
        assert_eq!(definition(".circle(r):", "circle"), main("circle: f32"));
        assert_eq!(definition("n.id\n", "id"), main("id: i32"));
        assert_eq!(definition("Hot.red", "red"), main("red"));
        assert_eq!(definition("Hot.red", "Hot"), main("Hot:"));
    }

    #[test]
    fn a_type_is_implemented_by_those_it_bounds() {
        // The structs that start as a struct does, for some type arguments
        // of a generic one: not one that only has its fields.
        assert_eq!(implementations("Head:\n", "Head"), ["Named"]);
        assert_eq!(implementations("T: Head", "Head"), ["Named"]);
        assert_eq!(implementations("Box:\n", "Box"), ["Pair"]);
        assert_eq!(implementations("Named:\n", "Named"), [] as [&str; 0]);
        // The unions and enums that one is wider than.
        assert_eq!(implementations("w: Wide", "Wide"), ["Shape"]);
        assert_eq!(implementations("-> Shape:", "Shape"), [] as [&str; 0]);
        assert_eq!(implementations("Hot.red", "Hot"), ["Warm"]);
        assert_eq!(implementations("Warm:\n", "Warm"), [] as [&str; 0]);
        // Nothing but a type is.
        assert_eq!(implementations("demo(p", "demo"), [] as [&str; 0]);
        assert_eq!(implementations("log(high)", "high"), [] as [&str; 0]);
    }

    #[test]
    fn a_struct_that_uses_an_array_has_its_fields() {
        let src = "\
struct(T) Vec:
    use varray(T)
    cap: uint
fn f(v: &Vec(u8)) -> uint:
    let n = v.len
    let first = v[0]
    v
    return n
";
        let mut files = Memory(vec![("main", src)]);
        let analysis = analysis(&mut files);
        let at = |files: &Memory, text: &str, name: &str| {
            let (file, offset) = files.at("main", text);
            (file, offset + text.find(name).unwrap())
        };
        // The fields it has of the array are among its own.
        let (file, offset) = at(&files, "    v\n", "v");
        let members = analysis.members(&mut files, file, offset);
        let members: Vec<_> = members
            .iter()
            .map(|member| (member.name.as_str(), member.detail.as_str()))
            .collect();
        assert_eq!(
            members,
            [
                ("*", "Vec(u8)"),
                ("ptr", "&var u8"),
                ("len", "uint"),
                ("cap", "uint")
            ]
        );
        let (file, offset) = at(&files, "first = v[0]", "first");
        let hover = analysis.hover(&mut files, file, offset).unwrap();
        assert_eq!(hover.text, "let first: u8");
        // Nothing declares them, as nothing does those of an array.
        let (file, offset) = at(&files, "v.len", "len");
        assert_eq!(analysis.definition(file, offset), None);
        assert_eq!(analysis.rename(&mut files, file, offset), None);
        let (file, offset) = at(&files, "cap: uint", "cap");
        let cap = analysis.definition(file, offset).unwrap();
        assert_eq!(&src[cap.start..cap.end], "cap");
    }

    #[test]
    fn a_type_is_implemented_by_those_whose_first_use_leads_to_it() {
        let src = "\
struct Head:
    id: i32
struct Named:
    use Head
    name: u8
struct Deep:
    use Named
struct Other:
    o: u8
struct Late:
    use Other
    use Head
struct(T) Box:
    value: T
struct(T) Pair:
    use Box(&T)
struct Ints:
    use Pair(i32)
union Narrow:
    a
union Wide:
    use Narrow
    b
union Wider:
    use Wide
    c
";
        let implementations = |name: &str| -> Vec<&'static str> {
            let mut files = Memory(vec![("main", src)]);
            let analysis = analysis(&mut files);
            let (file, offset) = files.at("main", name);
            let spans = analysis.implementations(file, offset);
            spans.into_iter().map(|s| &src[s.start..s.end]).collect()
        };
        // Through each first `use`, and no other.
        assert_eq!(implementations("Head"), ["Named", "Deep"]);
        assert_eq!(implementations("Other"), ["Late"]);
        assert_eq!(implementations("Box"), ["Pair", "Ints"]);
        assert_eq!(implementations("Deep"), [] as [&str; 0]);
        // A union is wider than those that it starts as.
        assert_eq!(implementations("Wider"), ["Narrow", "Wide"]);
        assert_eq!(implementations("Wide"), ["Narrow"]);
        assert_eq!(implementations("Narrow"), [] as [&str; 0]);
    }

    #[test]
    fn a_type_parameter_has_the_fields_of_each_type_its_bound_lists() {
        let lib = "\
pub struct Meta:
    pub flag: u8
    hidden: u8
";
        let src = "\
use lib
struct Head:
    id: i32
fn(T, A: (lib.Meta, Head, array(T))) f(x: &A) -> u8:
    let n = x.flag
    x
    return n
";
        let mut files = Memory(vec![("main", src), ("lib", lib)]);
        let analysis = analysis(&mut files);
        let at = |files: &Memory, text: &str, name: &str| {
            let (file, offset) = files.at("main", text);
            (file, offset + text.find(name).unwrap())
        };
        // Those that it sees in the struct that has each.
        let (file, offset) = at(&files, "    x\n", "x");
        let members = analysis.members(&mut files, file, offset);
        let members: Vec<_> = members
            .iter()
            .map(|member| (member.name.as_str(), member.detail.as_str()))
            .collect();
        assert_eq!(
            members,
            [
                ("*", "A"),
                ("flag", "u8"),
                ("id", "i32"),
                ("ptr", "&T"),
                ("len", "uint")
            ]
        );
        // A field is declared where the struct that the list names has it.
        let (file, offset) = at(&files, "x.flag", "flag");
        let flag = analysis.definition(file, offset).unwrap();
        assert_eq!(&lib[flag.start..].lines().next().unwrap(), &"flag: u8");
        // Each type that it lists is named as any type is.
        let (file, offset) = at(&files, "Head, array", "Head");
        let head = analysis.definition(file, offset).unwrap();
        assert_eq!(&src[head.start..].lines().next().unwrap(), &"Head:");
        let hover = analysis.hover(&mut files, file, offset).unwrap();
        assert_eq!(hover.text, "struct Head:\n\tid: i32");
        let (file, offset) = at(&files, "f(x", "f");
        let hover = analysis.hover(&mut files, file, offset).unwrap();
        assert_eq!(
            hover.text,
            "fn(T, A: (lib.Meta, Head, array(T))) f(x: &A) -> u8"
        );
    }

    /// Where each name is written that stands for what `name` does, in the
    /// first `text` of `main`: the file, its line counted from 1, and the
    /// line from the name on.
    fn references(text: &str, name: &str, declared: bool) -> Vec<String> {
        let mut files = names();
        let analysis = analysis(&mut files);
        let (file, offset) = place(&files, text, name);
        let spans = analysis.references(&mut files, file, offset, declared);
        let show = |span: Span| {
            let (file, src) = files.0[files.index(span.file)];
            let line = src[..span.start].matches('\n').count() + 1;
            let rest = src[span.start..].lines().next().unwrap_or_default();
            format!("{file}:{line}: {rest}")
        };
        spans.into_iter().map(show).collect()
    }

    #[test]
    fn a_name_is_referred_to_wherever_it_stands_for_the_same() {
        // A type, where it is declared, used, bounds and is written.
        assert_eq!(
            references("Head:\n", "Head", true),
            [
                "main:11: Head:",
                "main:14: Head",
                "main:30: Head) id_of(x: &T, n: Named) -> i32:",
            ]
        );
        // A field, of every struct that has it by a `use`.
        let id = ["main:12: id: i32", "main:31: id + n.id", "main:31: id"];
        assert_eq!(references("id: i32", "id", true), id);
        assert_eq!(references("n.id\n", "id", true), id);
        assert_eq!(references("n.id\n", "id", false), id[1..]);
        // A variant, as a pattern and by the type expected too.
        assert_eq!(
            references("circle: f32", "circle", true),
            [
                "main:6: circle: f32",
                "main:39: circle(r):",
                "main:40: circle(r)",
                "main:42: circle(side)",
            ]
        );
        // An item of another module, by every name it is used as.
        assert_eq!(
            references("length(p", "length", true),
            [
                "main:2: len as length}",
                "main:2: length}",
                "main:35: length(p, scale: 2.0)",
                "places:8: len(p: &Point, scale: f32 = 1.0) -> f32:",
            ]
        );
        assert_eq!(
            references("Point(x: d)", "x", false),
            ["main:36: x: d)", "places:7: x: 0.0)", "places:9: x * scale"]
        );
        // A variable, a parameter by its label, and a type parameter.
        assert_eq!(
            references("d)\n", "d", true),
            ["main:35: d = length(p, scale: 2.0)", "main:36: d)"]
        );
        assert_eq!(references("d)\n", "d", false), ["main:36: d)"]);
        assert_eq!(
            references("scale: 2.0", "scale", true),
            [
                "main:35: scale: 2.0)",
                "places:8: scale: f32 = 1.0) -> f32:",
                "places:9: scale",
            ]
        );
        assert_eq!(
            references("x: &T, n", "T", true),
            [
                "main:30: T: Head) id_of(x: &T, n: Named) -> i32:",
                "main:30: T, n: Named) -> i32:",
            ]
        );
        // A module, by the names that stand for it.
        assert_eq!(
            references("places.Color.green", "places", true),
            [
                "main:1: places",
                "main:2: places.{Point, len as length}",
                "main:45: places.Color.green"
            ]
        );
        // Nothing refers to what the language declares.
        assert_eq!(references("n: i32", "i32", true), [] as [&str; 0]);
    }

    /// What writing another name for `name` changes, in the first `text`
    /// of `main`: each place as [`references`] shows one.
    fn renamed(text: &str, name: &str) -> Option<Vec<String>> {
        let mut files = names();
        let analysis = analysis(&mut files);
        let (file, offset) = place(&files, text, name);
        let (at, spans) = analysis.rename(&mut files, file, offset)?;
        assert_eq!((at.file, at.start), (file, offset));
        let show = |span: Span| {
            let (file, src) = files.0[files.index(span.file)];
            let line = src[..span.start].matches('\n').count() + 1;
            format!("{file}:{line}: {}", &src[span.start..span.end])
        };
        Some(spans.into_iter().map(show).collect())
    }

    #[test]
    fn a_name_is_renamed_wherever_it_is_written_so() {
        let places = |places: &[&str]| Some(places.iter().map(|p| p.to_string()).collect());
        assert_eq!(
            renamed("n.id\n", "id"),
            places(&["main:12: id", "main:31: id", "main:31: id"])
        );
        assert_eq!(
            renamed("w: Wide", "Wide"),
            places(&["main:8: Wide", "main:34: Wide"])
        );
        // What a `use` names otherwise keeps that name, which is itself
        // renamed where it is given.
        assert_eq!(
            renamed("len as length", "len"),
            places(&["main:2: len", "places:8: len"])
        );
        assert_eq!(
            renamed("length(p", "length"),
            places(&["main:2: length", "main:35: length"])
        );
        assert_eq!(
            renamed("{Point, len", "Point"),
            places(&[
                "main:2: Point",
                "main:34: Point",
                "main:36: Point",
                "places:1: Point",
                "places:7: Point",
                "places:8: Point",
            ])
        );
        // A module, wherever a path or what it binds names it.
        assert_eq!(
            renamed("places.Color.green", "places"),
            places(&["main:1: places", "main:2: places", "main:45: places"])
        );
        // Nothing declares what the language does.
        assert_eq!(renamed("n: i32", "i32"), None);
        assert_eq!(renamed("scale: 2.0", "2.0"), None);
    }

    const KIT: &str = "\
# A point in the plane.
pub struct Point:
    # Across.
    pub x: f32
    pub y: f32 = 0.0  # Up, \"#\" and all.
pub union Shape:
    circle: f32
    empty
pub enum(u8) Color:
    red
    green

# How far `p` is from the origin,
# times `scale`.
pub fn len(p: Point, scale: f32 = 1.0) -> f32:
    return p.x * scale
pub fn area(s: Shape) -> option(f32):
    return .none
";

    const USER: &str = "\
use kit
use kit.Point
use kit.Color
struct(T) Box:
    value: T
let spare = 1
fn idle():
    pass
fn pick(c: kit.Color, s: kit.Shape, wide: i64) -> i32:
    let p = Point(x: 1.0)
    let (a, b) = (kit.len(p, 2.0) + p.y, wide)
    for m in kit.Color:
        pass
    match s:
        .circle(r):
            pass
    match c:
        .red:
            return 1
    let n: i32 = wide + 1
    let o: option(i32) = .some(1)
    module.grow
    option(i32)
    Box(u8)
    pass
    return area(s)
";

    fn user() -> Memory {
        Memory(vec![("main", USER), ("kit", KIT)])
    }

    /// The analysis of [`USER`], which has the errors it is written with.
    fn used(files: &mut Memory) -> Analysis {
        let (program, errors) = load::load_partial(files);
        assert_eq!(errors, []);
        analyze(program, &Settings::default())
    }

    #[test]
    fn hovering_gives_what_a_declaration_is_said_to_be() {
        let mut files = user();
        let analysis = used(&mut files);
        let mut docs = |text: &str, name: &str| {
            let (file, offset) = place(&files, text, name);
            analysis.hover(&mut files, file, offset).unwrap().docs
        };
        assert_eq!(docs("Point(x: 1.0)", "Point"), "A point in the plane.");
        assert_eq!(docs("Point(x: 1.0)", "x"), "Across.");
        assert_eq!(
            docs("kit.len(p", "len"),
            "How far `p` is from the origin,\ntimes `scale`."
        );
        // The comment that ends its line, where none is above it.
        assert_eq!(docs("p.y,", "y"), "Up, \"#\" and all.");
        // Nothing is said of a module, a variable or what has no comment.
        assert_eq!(docs("kit.len(p", "kit"), "");
        assert_eq!(docs("kit.len(p", "p"), "");
        assert_eq!(docs("kit.Shape,", "Shape"), "");
        assert_eq!(docs("c: kit.Color", "Color"), "");
    }

    #[test]
    fn the_type_of_a_value_is_defined_where_it_is_declared() {
        let mut files = user();
        let analysis = used(&mut files);
        let defined = |text: &str, name: &str| {
            let (file, offset) = place(&files, text, name);
            let span = analysis.type_definition(file, offset)?;
            let (file, src) = files.0[files.index(span.file)];
            Some((file, src[span.start..].lines().next().unwrap_or_default()))
        };
        assert_eq!(defined("p = Point", "p"), Some(("kit", "Point:")));
        assert_eq!(defined("kit.len(p, 2.0)", "p"), Some(("kit", "Point:")));
        assert_eq!(defined("s: kit.Shape", "s"), Some(("kit", "Shape:")));
        assert_eq!(defined("m in kit", "m"), Some(("kit", "Color:")));
        assert_eq!(defined("match c:", "c:"), Some(("kit", "Color:")));
        // A number, a tuple and what has no type are declared nowhere.
        assert_eq!(defined("wide + 1", "wide"), None);
        assert_eq!(defined("p.y,", "y"), None);
        assert_eq!(defined("fn pick", "pick"), None);
    }

    #[test]
    fn a_file_has_the_symbols_it_declares() {
        let mut files = user();
        let analysis = used(&mut files);
        let show = |symbols: Vec<Symbol>| -> Vec<String> {
            let show = |symbol: &Symbol| {
                let children: Vec<_> = symbol.children.iter().map(|c| c.name.as_str()).collect();
                format!("{:?} {} {children:?}", symbol.kind, symbol.name)
            };
            symbols.iter().map(show).collect()
        };
        let (main, _) = files.at("main", "use");
        assert_eq!(
            show(analysis.symbols(main)),
            [
                "Struct Box [\"value\"]",
                "Variable spare []",
                "Function idle []",
                "Function pick []",
            ]
        );
        let (kit, _) = files.at("kit", "#");
        assert_eq!(
            show(analysis.symbols(kit)),
            [
                "Struct Point [\"x\", \"y\"]",
                "Union Shape [\"circle\", \"empty\"]",
                "Enum Color [\"red\", \"green\"]",
                "Function len []",
                "Function area []",
            ]
        );
        assert_eq!(analysis.files(), [main, kit]);
    }

    #[test]
    fn what_is_not_written_is_hinted() {
        let mut files = user();
        let analysis = used(&mut files);
        let (main, _) = files.at("main", "use");
        let hints = |within: Range<usize>| -> Vec<String> {
            let hints = analysis.hints(main, within);
            let show = |hint: &Hint| {
                let line = USER[..hint.offset].matches('\n').count() + 1;
                format!("{line}: {:?} {:?}", hint.kind, hint.label)
            };
            hints.iter().map(show).collect()
        };
        assert_eq!(
            hints(0..USER.len()),
            [
                "6: Type \": i32\"",
                "10: Type \": Point\"",
                "11: Type \": f32\"",
                "11: Type \": i64\"",
                "11: Parameter \"scale: \"",
                "12: Type \": Color\"",
            ]
        );
        // Only those in what is asked for.
        let line = USER.find("    let (a, b)").unwrap();
        assert_eq!(hints(line..line + 14).len(), 2);
    }

    #[test]
    fn what_nothing_uses_is_unused() {
        let mut files = user();
        let analysis = used(&mut files);
        let unused = analysis.unused(&mut files);
        let show = |unused: &Unused| {
            let (file, src) = files.0[files.index(unused.span.file)];
            assert_eq!(&src[unused.span.start..unused.span.end], unused.name);
            let line = src[..unused.span.start].matches('\n').count() + 1;
            format!("{file}:{line}: {:?} {}", unused.kind, unused.name)
        };
        assert_eq!(
            unused.iter().map(show).collect::<Vec<_>>(),
            [
                "main:3: Use Color",
                "main:6: Variable spare",
                "main:7: Function idle",
                "main:9: Function pick",
                "main:11: Variable a",
                "main:11: Variable b",
                "main:12: Variable m",
                "main:15: Variable r",
                "main:20: Variable n",
                "main:21: Variable o",
            ]
        );
    }

    #[test]
    fn an_error_is_mended_by_what_it_says_is_missing() {
        let mut files = user();
        let analysis = used(&mut files);
        let mut mended = |text: &str| -> Vec<(String, String)> {
            let (main, at) = files.at("main", text);
            let actions = analysis.actions(&mut files, main, at..at + text.len());
            let made = |action: Action| {
                let mut made = USER.to_string();
                for (span, text) in action.edits.iter().rev() {
                    made.replace_range(span.start..span.end, text);
                }
                // The lines that it changes.
                let changed = made
                    .lines()
                    .filter(|line| !USER.lines().any(|l| l == *line));
                (action.title, changed.collect::<Vec<_>>().join("|"))
            };
            actions.into_iter().map(made).collect()
        };
        let action = |title: &str, lines: &str| vec![(title.to_string(), lines.to_string())];
        assert_eq!(
            mended("match s"),
            action("Add an arm for `.empty`", "        .empty:")
        );
        assert_eq!(
            mended("match c"),
            action("Add an arm for `.green`", "        .green:")
        );
        assert_eq!(
            mended("wide + 1"),
            action(
                "Cast to `i32` with `as`",
                "    let n: i32 = (wide + 1) as i32"
            )
        );
        assert_eq!(
            mended("area(s)"),
            action("Add `use kit.area`", "use kit.area")
        );
        assert_eq!(mended("let p"), []);
        // The body of an arm is indented as that of the arm before it.
        let (main, at) = files.at("main", "match s");
        let arm = &analysis.actions(&mut files, main, at..at + 7)[0].edits[0];
        assert_eq!(arm.1, "\n        .empty:\n            pass");
        assert_eq!(&USER[arm.0.start - 5..arm.0.start], " pass");
    }

    #[test]
    fn what_is_expected_and_what_a_use_brings_can_be_written() {
        let mut files = user();
        let analysis = used(&mut files);
        let (main, some) = place(&files, ".some(1)", "some");
        assert_eq!(shown(analysis.expected(main, some)), ["none", "some: i32"]);
        let (_, circle) = place(&files, ".circle(r)", "circle");
        assert_eq!(
            shown(analysis.expected(main, circle)),
            ["circle: f32", "empty"]
        );
        let (_, red) = place(&files, ".red:", "red");
        assert_eq!(
            shown(analysis.expected(main, red)),
            ["red: Color", "green: Color"]
        );
        assert_eq!(shown(analysis.expected(main, 0)), [] as [&str; 0]);
        let signature = analysis.expected_signature(main, some).unwrap();
        assert_eq!(signature.label, "option(i32).some(i32)");
        assert_eq!(analysis.expected_signature(main, red), None);

        // The items of the module that a path names.
        let (_, kit) = place(&files, "use kit.Point", "kit");
        let items = shown(analysis.module_items(&mut files, main, kit));
        assert_eq!(items[..3], ["Color", "Point", "Shape"]);
        assert_eq!(items.len(), 5);

        // A type that is given its type arguments has what it is declared
        // with, and a function of `module` its own parameters.
        let line = |text: &str| USER.find(text).unwrap() + 4;
        let option = shown(analysis.members(&mut files, main, line("    option(i32)\n")));
        assert_eq!(option, ["none", "some: T", "size: uint", "align: uint"]);
        let boxed = shown(analysis.members(&mut files, main, line("    Box(u8)\n")));
        assert_eq!(boxed, ["size: uint", "align: uint"]);
        let grow = analysis.signature(&mut files, main, line("    module.grow\n"));
        assert_eq!(grow.unwrap().label, "module.grow(pages: uint) -> int");

        // Last of the names in scope are those that a `use` would bring,
        // each with the line that does, which goes before the others.
        let names = analysis.names(&mut files, main, line("    pass\n    return"));
        let imports: Vec<_> = names.iter().filter(|name| name.import.is_some()).collect();
        let imported: Vec<_> = imports.iter().map(|name| name.name.as_str()).collect();
        assert_eq!(imported, ["Shape", "area", "len"]);
        assert_eq!(imports[1].import, Some((0, "use kit.area\n".to_string())));
        assert_eq!(imports[1].detail, "use kit.area");
        assert_eq!(names.last().unwrap().name, "len");
    }

    #[test]
    fn a_name_collides_with_what_is_named_so_already() {
        let mut files = user();
        let analysis = used(&mut files);
        let mut collides = |text: &str, name: &str, new: &str| {
            let (file, offset) = place(&files, text, name);
            analysis.collides(&mut files, file, offset, new)
        };
        // An item, with one of its module or with a type of the language.
        assert!(collides("let spare", "spare", "idle"));
        assert!(collides("let spare", "spare", "Point"));
        assert!(collides("let spare", "spare", "u8"));
        assert!(!collides("let spare", "spare", "extra"));
        // And with what is named so wherever a `use` names it.
        assert!(collides("kit.len(p", "len", "area"));
        assert!(collides("use kit.Point", "Point", "Box"));
        assert!(!collides("kit.len(p", "len", "idle"));
        // A variable, with one in scope where it is bound or used.
        assert!(collides("(a, b)", "b", "p"));
        assert!(collides("p = Point", "p", "wide"));
        assert!(!collides("p = Point", "p", "q"));
        // A field, with another of its struct, and a type parameter with
        // an item, which is what its name would then stand for.
        assert!(collides("Point(x: 1.0)", "x", "y"));
        assert!(!collides("Point(x: 1.0)", "x", "z"));
        assert!(collides("value: T", "T", "Box"));
        assert!(!collides("value: T", "T", "U"));
    }

    #[test]
    fn what_loads_of_a_program_with_errors_is_answered_of() {
        let main = "\
use broken
fn f(a: i32) -> i32:
    let b = a +
    let c = (a, 1.5)
    if c.0 ==:
        pass
    c
    return broken.one
fn g(: i32):
    pass
let y = f(1)
";
        // A line that doesn't lex is left out, as one that doesn't parse is.
        let broken = "pub let one = 1\nlet s = \"\nfn h():\n    return (\n";
        let mut files = Memory(vec![("main", main), ("broken", broken)]);
        let (program, errors) = load::load_partial(&mut files);
        assert_eq!(errors.len(), 4, "{errors:?}");
        let analysis = analyze(program, &Settings::default());
        let (file, offset) = files.at("main", "c\n");
        assert_eq!(
            shown(analysis.members(&mut files, file, offset)),
            ["0: i32", "1: f64"]
        );
        assert_eq!(
            shown(analysis.names(&mut files, file, offset))[..3],
            ["c: tuple(i32, f64)", "a: i32", "broken"]
        );
        let (file, offset) = files.at("main", "y = f");
        let hover = analysis.hover(&mut files, file, offset).unwrap();
        assert_eq!(hover.text, "let y: i32");
        let (file, offset) = files.at("main", "one\n");
        let hover = analysis.hover(&mut files, file, offset).unwrap();
        assert_eq!(hover.text, "let one: i32 = 1");
    }
}

//! What can be written to mend an error or a warning, where it says enough
//! of what is wrong for that to be written for whoever made it, and what
//! can be written otherwise to the same end.

use std::ops::Range;
use std::ptr;

use crate::file::{FileId, FileManager};
use crate::lex::Span;
use crate::load::Use;
use crate::parse::{self, Arg, Arm, ExprKind, ItemKind, PatternKind, StmtKind};
use crate::visit::{self, Node};

use super::super::{Prim, Ty, TypeError, TypeErrorKind, convertible};
use super::{Analysis, Found, HintKind, Item, Sources, Target, Unused, UnusedKind, line_start};

/// A change to the source that is offered where it would help.
#[derive(Debug, Clone, PartialEq)]
pub struct Action {
    /// What it does, as it is offered.
    pub title: String,
    /// What it writes, each in place of what is at its span, which is none
    /// of the source where it only adds.
    pub edits: Vec<(Span, String)>,
    pub kind: ActionKind,
    /// The error or the warning that it mends, if it mends one: where that
    /// is, and what names its kind.
    pub mends: Option<(Span, &'static str)>,
    /// Whether it is the one change that what it mends asks for, rather
    /// than one of several that may be meant, or one that may hide what
    /// is wrong.
    pub preferred: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ActionKind {
    /// Mends an error or a warning.
    Fix,
    /// Writes what the source leaves unsaid, which means the same.
    Rewrite,
    /// Puts the `use` lines of a file in order, without those that nothing
    /// uses.
    Organize,
}

/// How the body of an arm is indented past its pattern where no arm of its
/// `match` says.
const INDENT: &str = "\t";

/// What stands for a value that is yet to be written.
const TODO: &str = "todo";

/// What a name starts with that is meant to go unused.
const UNUSED: &str = "_";

impl Action {
    /// A change that mends an error or a warning, which the caller says
    /// which it is.
    fn fix(title: String, edits: Vec<(Span, String)>, preferred: bool) -> Self {
        Self {
            title,
            edits,
            kind: ActionKind::Fix,
            mends: None,
            preferred,
        }
    }
}

impl Analysis {
    /// What can be changed in bytes `within` of `file`. What mends each
    /// error there: the arms that a `match` leaves out, the `use` of a
    /// name that another module has and this one doesn't, the name that
    /// one which names nothing was likely meant to be, the `as` that makes
    /// a number the kind of number expected of it, the fields that a
    /// constructor leaves out, and the `pub` that lets another module see
    /// what this one names. What mends each of `unused` there, which are
    /// what was found to be declared and never used. Then the type that a
    /// name there is bound without, and the `use` lines of the file in
    /// order, if they aren't.
    pub fn actions(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        within: Range<usize>,
        unused: &[Unused],
    ) -> Vec<Action> {
        let here =
            |span: &Span| span.file == file && span.start <= within.end && within.start <= span.end;
        // One in an instance of a generic function is mended where the
        // function is declared, which is elsewhere.
        let errors = self
            .ck
            .errors
            .iter()
            .filter(|error| error.instances.is_empty());
        let errors = errors.filter_map(|error| Some((error.span.filter(here)?, error)));
        let mut actions = Vec::new();
        // The calls whose missing fields are written, each once.
        let mut filled = Vec::new();
        for (span, error) in errors {
            let mut mending = Vec::new();
            match &error.kind {
                TypeErrorKind::NonExhaustive(witness) => {
                    mending.extend(self.missing_arms(files, span, witness));
                }
                TypeErrorKind::UnknownName(name) | TypeErrorKind::UnknownType(name) => {
                    mending.extend(self.missing_uses(files, file, name));
                }
                TypeErrorKind::Mismatch { expected, found } => {
                    mending.extend(self.cast(span, expected, found));
                }
                TypeErrorKind::MissingArg(_) if !filled.contains(&span) => {
                    filled.push(span);
                    mending.extend(self.missing_fields(files, span));
                }
                TypeErrorKind::Private(name) => {
                    mending.extend(self.made_pub(files, span, name));
                }
                TypeErrorKind::PrivateField { field, .. } => {
                    mending.extend(self.field_made_pub(files, span, field));
                }
                _ => {}
            }
            mending.extend(self.respelled(files, span, error));
            // One of several is no more what the error asks for than the
            // others are.
            let alone = mending.len() == 1;
            actions.extend(mending.into_iter().map(|action| Action {
                mends: Some((span, error.kind.code())),
                preferred: action.preferred && alone,
                ..action
            }));
        }
        for unused in unused.iter().filter(|unused| here(&unused.span)) {
            let mending = self.unused_fixes(files, unused);
            let alone = mending.len() == 1;
            actions.extend(mending.into_iter().map(|action| Action {
                mends: Some((unused.span, unused.kind.code())),
                preferred: action.preferred && alone,
                ..action
            }));
        }
        actions.extend(self.typed(files, file, within.clone()));
        // Where they are, which is not everywhere in the file.
        let organized = self.organized(files, file, unused);
        actions.extend(organized.filter(|organized| here(&organized.edits[0].0)));
        actions
    }

    /// Writes for the name at `span` the one that `error` says was likely
    /// meant, if it says one.
    fn respelled(
        &self,
        files: &mut impl FileManager,
        span: Span,
        error: &TypeError,
    ) -> Option<Action> {
        let similar = error.similar.as_ref()?;
        let name = match &error.kind {
            TypeErrorKind::UnknownName(name) | TypeErrorKind::UnknownType(name) => name,
            TypeErrorKind::NoField { field: name, .. }
            | TypeErrorKind::NoMember { member: name, .. }
            | TypeErrorKind::NoVariant { variant: name, .. }
            | TypeErrorKind::NoItem { item: name, .. } => name,
            _ => return None,
        };
        // A type is reported with its type arguments, which stay.
        let named = Span {
            end: span.start + name.len(),
            ..span
        };
        let mut read = |id| files.contents(id);
        let written = Sources::new(&mut read).text(named);
        (written == *name).then(|| {
            let title = format!("Write `{similar}` for `{name}`");
            Action::fix(title, vec![(named, similar.clone())], true)
        })
    }

    /// Gives the constructor at `span` each field that the errors at it
    /// say it leaves out, with `todo` for its value. Only a struct is built
    /// of fields by their names: a function may be given what it lacks by
    /// its place.
    fn missing_fields(&self, files: &mut impl FileManager, span: Span) -> Option<Action> {
        let errors = self.ck.errors.iter();
        let errors = errors.filter(|error| error.span == Some(span) && error.instances.is_empty());
        let fields: Vec<_> = errors
            .filter_map(|error| match &error.kind {
                TypeErrorKind::MissingArg(field) => Some(field.as_str()),
                _ => None,
            })
            .collect();
        let (callee, args) = self.call_at(span)?;
        let site = self.locate(span.file, callee.span.start, false);
        let built = match self.type_named(&site, self.generic(&site, callee))? {
            Ty::Struct(id) => !self.ck.structs[id.0 as usize].union,
            _ => false,
        };
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        let text = src.file(span.file);
        // After the last argument, or else between the brackets.
        let close = span.end.checked_sub(1)?;
        let (at, first) = match args.last() {
            Some(last) => (last.value.span.end, ", "),
            None => (close, ""),
        };
        if !built || text.get(close..span.end) != Some(")") {
            return None;
        }
        let written: Vec<_> = fields
            .iter()
            .map(|field| format!("{field}: {TODO}"))
            .collect();
        let at = Span {
            start: at,
            end: at,
            ..span
        };
        let title = match fields[..] {
            [field] => format!("Add the field `{field}`"),
            _ => "Add the fields that are left out".to_string(),
        };
        let edits = vec![(at, format!("{first}{}", written.join(", ")))];
        Some(Action::fix(title, edits, true))
    }

    /// The call that is written at `span`: what is called, and with what.
    fn call_at(&self, span: Span) -> Option<(&parse::Expr, &[Arg])> {
        match &self.expr_at(span)?.kind {
            ExprKind::Call(callee, args) => Some((callee, args)),
            _ => None,
        }
    }

    /// The outermost expression that is written at `span`.
    fn expr_at(&self, span: Span) -> Option<&parse::Expr> {
        let mut found = None;
        let items = self.program.items.iter();
        for item in items.filter(|item| item.span.file == span.file) {
            visit::each(item, &mut |node| {
                if let Node::Expr(expr) = node
                    && expr.span == span
                {
                    found = found.take().or(Some(expr));
                }
            });
        }
        found
    }

    /// Makes `pub` the item that `name` names at `span`, in a module that
    /// keeps it to itself.
    fn made_pub(&self, files: &mut impl FileManager, span: Span, name: &str) -> Option<Action> {
        let declared = self.declaration(self.reached(span)?)?;
        let at = Span {
            end: declared.start,
            ..declared
        };
        let mut read = |id| files.contents(id);
        let text = Sources::new(&mut read).text(declared);
        // What is seen already is kept from this module by something else.
        let edits = vec![(at, "pub ".to_string())];
        (!text.starts_with("pub "))
            .then(|| Action::fix(format!("Make `{name}` `pub`"), edits, true))
    }

    /// Makes `pub` the field `field` that is read at `span`, of a struct
    /// whose module keeps it to itself.
    fn field_made_pub(
        &self,
        files: &mut impl FileManager,
        span: Span,
        field: &str,
    ) -> Option<Action> {
        let site = self.locate(span.file, span.start, false);
        let Some(Target::Entry(index, name)) = self.target(&site) else {
            return None;
        };
        let declared = self.entry_span(index, name, super::MAX_USES)?;
        let mut read = |id| files.contents(id);
        let written = Sources::new(&mut read).text(declared);
        let at = Span {
            end: declared.start,
            ..declared
        };
        let edits = vec![(at, "pub ".to_string())];
        (written == field).then(|| Action::fix(format!("Make `{field}` `pub`"), edits, true))
    }

    /// The item that the name at `span` names in the module that the names
    /// before it lead to, whether or not its file sees it there.
    fn reached(&self, span: Span) -> Option<Item> {
        let file = span.file;
        // One of the path of a `use`, after the module that it leads into.
        for used in self.program.uses.iter().filter(|used| used.module == file) {
            let mut module = Some(used.target);
            for name in &used.members {
                let item = self.item(module?, &name.name);
                if name.span == span {
                    return item;
                }
                module = match item {
                    Some(Item::Module(next)) => Some(next),
                    _ => None,
                };
            }
        }
        let site = self.locate(file, span.start, false);
        match site.found.as_ref()? {
            Found::Expr(expr) => match &expr.kind {
                ExprKind::Field(inner, field) if field.span == span => {
                    match self.named(&site, inner)? {
                        Item::Module(module) => self.item(module, &field.name),
                        _ => None,
                    }
                }
                _ => None,
            },
            Found::Path { names, .. } => {
                let (first, rest) = names.split_first()?;
                let mut item = self.item(file, first)?;
                for name in rest {
                    let Item::Module(module) = item else {
                        return None;
                    };
                    item = self.item(module, name)?;
                }
                Some(item)
            }
            _ => None,
        }
    }

    /// The whole of what declares `item`, which `pub` is written before.
    /// `None` for what no item of the program declares: a module, and what
    /// is the language's own.
    fn declaration(&self, item: Item) -> Option<Span> {
        let items = &self.program.items;
        let index = match item {
            Item::Func(_) | Item::GenericFn(_) => {
                // One that is imported is declared in its block, by a line
                // of its own.
                let (block, sig) = self.fn_decl(item)?;
                if let Some(block) = block {
                    let mut imported = block.fns.iter();
                    return Some(imported.find(|imported| ptr::eq(&imported.sig, sig))?.span);
                }
                let declares = |item: &parse::Item| match &item.kind {
                    ItemKind::Fn(decl) => ptr::eq(&decl.sig, sig),
                    _ => false,
                };
                items.iter().position(declares)?
            }
            Item::Struct(id) if !self.is_builtin(id) => self.ck.structs[id.0 as usize].item,
            Item::Enum(id) => self.ck.enums[id.0 as usize].item,
            Item::Global(index) => *self.ck.global_items.get(index)?,
            Item::Alias(id) => self.ck.aliases[id].item,
            Item::Struct(_) | Item::Module(_) => return None,
        };
        Some(items.get(index)?.span)
    }

    /// What mends `unused`, which is declared and never used: a `use` is
    /// taken away, and anything else is named as what is meant to go
    /// unused, which is what stays of it either way.
    fn unused_fixes(&self, files: &mut impl FileManager, unused: &Unused) -> Vec<Action> {
        let name = &unused.name;
        // A function that is imported is the host's by its name.
        let imports = self
            .program
            .items
            .iter()
            .filter_map(|item| match &item.kind {
                ItemKind::Extern(block) => Some(block.fns.iter()),
                _ => None,
            });
        let mut imported = imports.flatten().map(|imported| imported.sig.name.span);
        if imported.any(|imported| imported == unused.span) {
            return Vec::new();
        }
        if unused.kind != UnusedKind::Use {
            let at = Span {
                end: unused.span.start,
                ..unused.span
            };
            let title = format!("Name it `{UNUSED}{name}`");
            return vec![Action::fix(title, vec![(at, UNUSED.to_string())], false)];
        }
        let mut uses = self.program.uses.iter();
        let Some(used) = uses.find(|used| used.name.span == unused.span) else {
            return Vec::new();
        };
        let mut read = |id| files.contents(id);
        let removed = self.use_removed(&mut Sources::new(&mut read), used);
        let title = format!("Remove the `use` of `{name}`");
        let removed =
            removed.map(|removed| Action::fix(title, vec![(removed, String::new())], true));
        removed.into_iter().collect()
    }

    /// What is taken from the source for it to no longer write `used`: the
    /// lines of its `use`, if that writes nothing else, or else its own
    /// names in the group it is one of, with the comma that sets them
    /// apart, and with a group within that one which holds nothing but
    /// them. `None` where it is alone in a group whose names others share,
    /// which would be left with nothing in it.
    fn use_removed(&self, src: &mut Sources, used: &Use) -> Option<Span> {
        let decl = used.decl;
        let together: Vec<_> = (self.program.uses.iter())
            .filter(|other| other.decl == decl && !ptr::eq(*other, used))
            .collect();
        let text = src.file(decl.file);
        let span = |start: usize, end: usize| Span { start, end, ..decl };
        let line_end = |at: usize| text[at..].find('\n').map_or(text.len(), |i| at + i + 1);
        if together.is_empty() {
            return Some(span(line_start(text, decl.start), line_end(decl.end)));
        }
        // Its own names are those that no other path of the group has.
        let names = |used: &Use| -> Vec<Span> {
            let names = used.path.iter().chain(&used.members);
            names.map(|name| name.span).collect()
        };
        let shared = |name: &Span| together.iter().any(|other| names(other).contains(name));
        let own = names(used);
        let start = own.iter().find(|name| !shared(name))?.start;
        let mut end = own.last()?.end.max(used.name.span.end);
        // A group that holds nothing else goes with them, to where it ends.
        for _ in text.get(start..end)?.matches('{') {
            let rest = text.get(end..decl.end)?;
            let close = rest.find('}')?;
            if !rest[..close].chars().all(|c| c == ',' || c.is_whitespace()) {
                return None;
            }
            end += close + 1;
        }
        let after = text.get(end..decl.end)?;
        let rest = after.trim_start();
        if rest.starts_with(',') {
            let comma = end + (after.len() - rest.len()) + 1;
            let spaces = text[comma..].len() - text[comma..].trim_start_matches([' ', '\t']).len();
            // A line that holds nothing else goes with it.
            let line = line_start(text, start);
            let own =
                text[line..start].trim().is_empty() && text[comma + spaces..].starts_with('\n');
            return Some(match own {
                true => span(line, comma + spaces + 1),
                false => span(start, comma + spaces),
            });
        }
        let before = text.get(decl.start..start)?.trim_end();
        let comma = decl.start + before.strip_suffix(',')?.len();
        Some(span(comma, end))
    }

    /// Writes the type of each name that is bound without one in bytes
    /// `within` of `file`, where the file has a way to write it.
    fn typed(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        within: Range<usize>,
    ) -> Vec<Action> {
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        let text = src.file(file);
        // A name is hinted where it ends, which is on the line it is on.
        let line = text[within.end.min(text.len())..].find('\n');
        let end = line.map_or(text.len(), |i| within.end + i);
        let hints = self.hints(file, within.start..end).into_iter();
        let typed = hints.filter_map(|hint| {
            let insert = hint.insert.filter(|_| hint.kind == HintKind::Type)?;
            let named = text.get(..hint.offset)?;
            let name = named.trim_end_matches(|c: char| c == '_' || c.is_alphanumeric());
            let name = &named[name.len()..];
            let at = Span {
                file,
                start: hint.offset,
                end: hint.offset,
            };
            (hint.offset - name.len() <= within.end).then(|| Action {
                title: format!("Write the type of `{name}`"),
                edits: vec![(at, insert)],
                kind: ActionKind::Rewrite,
                mends: None,
                preferred: false,
            })
        });
        typed.collect()
    }

    /// Puts in order the `use` lines that `file` starts with, each on a
    /// line of its own right after the one before, by the path that each
    /// names, without what `unused` says nothing uses: a `use` of that
    /// alone is left out, and a group with it is written without it.
    /// `None` if they are in order and all used. What is written between
    /// two of them is left where it is, with those after it.
    pub fn organized(
        &self,
        files: &mut impl FileManager,
        file: FileId,
        unused: &[Unused],
    ) -> Option<Action> {
        let uses = || self.program.uses.iter().filter(|used| used.module == file);
        let mut decls: Vec<Span> = uses().map(|used| used.decl).collect();
        decls.sort_by_key(|decl| decl.start);
        decls.dedup();
        let mut read = |id| files.contents(id);
        let mut src = Sources::new(&mut read);
        let text = src.file(file);
        let first = *decls.first()?;
        let start = line_start(text, first.start);
        // Those that follow one another, each from the start of its line.
        let mut lines = vec![first];
        for pair in decls.windows(2) {
            if text.get(pair[0].end..pair[1].start) != Some("\n") {
                break;
            }
            lines.push(pair[1]);
        }
        let end = lines.last()?.end;
        if start != first.start || !text[end..].starts_with('\n') {
            return None;
        }
        let is_unused = |used: &Use| unused.iter().any(|unused| unused.span == used.name.span);
        let mut kept: Vec<(String, String)> = Vec::new();
        for decl in lines {
            let written: Vec<_> = uses().filter(|used| used.decl == decl).collect();
            let used: Vec<_> = written.iter().filter(|used| !is_unused(used)).collect();
            let as_written = &text[decl.start..decl.end];
            let line = match used.len() == written.len() {
                true => as_written.to_string(),
                false if used.is_empty() => continue,
                // What is said of a group is said in it, and stays.
                false if as_written.contains('#') => as_written.to_string(),
                false => use_line(&used.into_iter().copied().collect::<Vec<_>>()),
            };
            // In the order of what is named, whether or not it is `pub`.
            let path = line.trim_start_matches("pub ").to_string();
            kept.push((path, line));
        }
        kept.sort();
        let organized: String = kept.iter().map(|(_, line)| format!("{line}\n")).collect();
        let lines = Span {
            file,
            start,
            end: end + 1,
        };
        (organized != text[start..end + 1]).then(|| Action {
            title: "Organize the `use` lines".to_string(),
            edits: vec![(lines, organized)],
            kind: ActionKind::Organize,
            mends: None,
            preferred: false,
        })
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
        let title = match patterns.len() {
            1 => format!("Add an arm for `{}`", patterns[0]),
            _ => "Add the arms that are left out".to_string(),
        };
        Some(Action::fix(title, vec![(at, arms.collect())], true))
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
        let action = |path: String| {
            let line = format!("use {path}.{name}");
            Action::fix(
                format!("Add `{line}`"),
                vec![(at, format!("{line}\n"))],
                true,
            )
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
        let cast = self.expr_at(span);
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
        // A number of another kind may be what is wrong, which a cast
        // would hide.
        let title = format!("Cast to `{expected}` with `as`");
        Some(Action::fix(title, edits, false))
    }
}

/// The `use` that writes `used` and nothing else, which are paths of one
/// `use`: one alone as it is, and several as a group after the names they
/// all start with.
fn use_line(used: &[&Use]) -> String {
    let names = |used: &Use| -> Vec<String> {
        let names = used.path.iter().chain(&used.members);
        names.map(|name| name.name.clone()).collect()
    };
    let path = |used: &Use, from: usize| {
        let names = names(used);
        let path = names[from..].join(".");
        match names.last() == Some(&used.name.name) {
            true => path,
            false => format!("{path} as {}", used.name.name),
        }
    };
    let start = match used.first().is_some_and(|used| used.is_pub) {
        true => "pub use",
        false => "use",
    };
    if let [only] = used {
        return format!("{start} {}", path(only, 0));
    }
    // As many names as all of them start with, short of the whole of one.
    let all: Vec<_> = used.iter().map(|used| names(used)).collect();
    let shortest = all.iter().map(Vec::len).min().unwrap_or(1);
    let mut shared = 0;
    while shared + 1 < shortest && all.iter().all(|names| names[shared] == all[0][shared]) {
        shared += 1;
    }
    let paths: Vec<_> = used.iter().map(|used| path(used, shared)).collect();
    format!(
        "{start} {}.{{{}}}",
        all[0][..shared].join("."),
        paths.join(", ")
    )
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

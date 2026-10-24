//! Gathers a program from its entry point and every module it uses.
//!
//! Every file is a module, named by its path from the root of its package:
//! `util/strings.duck` is `util.strings`. Its items are kept apart from those
//! of other modules, which it reaches through the names `use` gives them.
//!
//! A file of the test directory of the package is a module of it too, named
//! by its path from that directory, and loaded where the files have any:
//! after the entry point and every module it uses.

use std::fmt;
use std::mem;
use std::ops::Range;
use std::rc::Rc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::Error;
use crate::codec::DecodeError;
use crate::file::{self, FileId, FileManager, Includes, TestModule};
use crate::lex::{self, Span, Token};
use crate::parse::{self, Ident, Item, ItemKind, UsePath};
use crate::ty::Artifact;
use crate::visit::{self, Node};

#[derive(Debug, Clone, PartialEq)]
pub struct UseError {
    pub kind: UseErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum UseErrorKind {
    /// A path that no module of the package is along, and that doesn't
    /// start with a dependency.
    NotFound(String),
    /// A path starting with the name of both a module of the package and a
    /// dependency.
    Ambiguous(String),
    /// A dependency that is compiled already, whose files or dependencies
    /// are not as they were then.
    Stale(String),
}

/// The items of every module of a program, and the names modules give what
/// they use.
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    /// Every module's items, each module's after those of every module it
    /// uses that doesn't use it in turn, and each package's after those of
    /// every package it depends on, as [`Program::packages`] has them.
    pub items: Vec<Item>,
    /// The packages of the program, each after those it depends on, which
    /// leaves the package of the entry last: each with the items that are
    /// its own, which follow one another.
    pub packages: Vec<PackageItems>,
    /// Each after every `use` of the module it leads into, unless that
    /// module uses this one in turn.
    pub uses: Vec<Use>,
    /// The module whose `pub` items the program exports, with those it uses
    /// as `pub`.
    pub entry: FileId,
    /// What each `module.include` of a string literal includes.
    pub includes: Includes,
    /// The test modules of the package that `entry` is in, in the order
    /// they are tested in. None for a program that is built.
    pub tests: Vec<TestModule>,
    /// The modules of the package that `entry` is in, its test modules
    /// among them: those a test module sees all of, `pub` or not.
    pub package: FxHashSet<FileId>,
    /// Each package that a package uses, in the order the modules of the
    /// package first use them.
    pub depends: Vec<Depend>,
    /// The packages whose items are those of their artifacts' interfaces,
    /// as they are compiled already: nothing of them is lowered again.
    pub imported: Vec<Compiled>,
}

/// A package that a package uses.
#[derive(Debug, Clone, PartialEq)]
pub struct Depend {
    /// The root of the package that uses the other.
    pub from: FileId,
    /// The name it uses the other as.
    pub name: String,
    /// The library of the other, which is its root.
    pub library: FileId,
}

/// A package that is compiled already, whose items are those of its
/// artifact's interface.
#[derive(Debug, Clone, PartialEq)]
pub struct Compiled {
    /// Its library, which is its root.
    pub root: FileId,
    pub artifact: Rc<Artifact>,
}

/// The items of one package of a program.
#[derive(Debug, Clone, PartialEq)]
pub struct PackageItems {
    /// The module the package is reached by: the entry point, or the
    /// library of a dependency.
    pub root: FileId,
    /// What names the package wherever it is compiled, as
    /// [`FileManager::package_name`] gives it.
    pub name: String,
    /// Its items, in [`Program::items`].
    pub items: Range<usize>,
    /// Its modules, the root first, in the order they were loaded.
    pub files: Vec<FileId>,
    /// The path a `use` leads to each of them by from its root, as
    /// [`FileManager::module_path`] gives it.
    pub modules: Vec<Vec<String>>,
}

/// A name `module` gives a module, or something reached through one.
#[derive(Debug, Clone, PartialEq)]
pub struct Use {
    pub module: FileId,
    pub name: Ident,
    /// The module furthest along the path.
    pub target: FileId,
    /// `target`, as the path names it.
    pub target_path: String,
    /// The names of the path that lead to `target`, the last of which names
    /// it: its file, or the dependency whose library it is.
    pub path: Vec<Ident>,
    /// The rest of the path, each a member of what the one before names.
    /// Empty when the path names `target` itself.
    pub members: Vec<Ident>,
    /// Whether modules using `module` can reach `name` through it.
    pub is_pub: bool,
    /// The whole of the `use` that writes it, which writes every path of
    /// its group with it.
    pub decl: Span,
}

/// What each file of a program was when the program was last loaded, with
/// what it parsed to: a file that is as it was then isn't lexed and parsed
/// again.
#[derive(Default)]
pub struct Parsed {
    files: FxHashMap<FileId, Read>,
}

/// A file as it was read, and what was made of it.
#[derive(Clone)]
struct Read {
    src: String,
    /// What parsed of it, if anything lexed.
    module: Option<parse::Module>,
    /// Why it didn't lex or parse whole, if it didn't.
    errors: Vec<Error>,
}

struct Loader<'f, F> {
    files: &'f mut F,
    /// Whether what lexes and parses of a file with errors is loaded.
    partial: bool,
    /// What the files parsed to when they were last loaded, if that was
    /// kept.
    parsed: Option<&'f mut Parsed>,
    /// The modules loaded or being loaded, which are not loaded again.
    seen: FxHashSet<FileId>,
    /// Those, in the order they were first seen.
    loaded: Vec<FileId>,
    items: Vec<Item>,
    uses: Vec<Use>,
    includes: Includes,
    /// Each module that a path from the root of its package, or from its
    /// test directory, led to, after the module that uses it: the two are
    /// of one package.
    within: Vec<(FileId, FileId)>,
    /// The module that each module's package is reached by.
    roots: FxHashMap<FileId, FileId>,
    /// Each package that a package depends on, by those modules, in the
    /// order its modules first use them.
    depends: Vec<Depend>,
    /// The packages whose items were taken from their artifacts.
    imported: Vec<Compiled>,
    errors: Vec<Error>,
}

/// The most lines with an error that are blanked for the rest of a file to
/// lex.
const MAX_BLANKED_LINES: usize = 16;

impl UseErrorKind {
    /// What names the kind of error, as [`crate::Error::code`] gives it.
    pub fn code(&self) -> &'static str {
        match self {
            Self::NotFound(..) => "module-not-found",
            Self::Ambiguous(..) => "ambiguous-module",
            Self::Stale(..) => "stale-artifact",
        }
    }
}

impl fmt::Display for UseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFound(path) => write!(
                f,
                "cannot find `{path}` in this package or its dependencies"
            ),
            Self::Ambiguous(name) => write!(
                f,
                "`{name}` is both a module of this package and a dependency"
            ),
            Self::Stale(why) => write!(f, "the package is not as it was compiled: {why}"),
        }
    }
}

impl fmt::Display for UseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}..{}", self.kind, self.span.start, self.span.end)
    }
}

impl std::error::Error for UseError {}

impl Program {
    /// A program of one module, which uses nothing.
    pub fn single(entry: FileId, module: parse::Module) -> Self {
        let items = 0..module.items.len();
        Self {
            packages: vec![PackageItems {
                root: entry,
                name: String::new(),
                items,
                files: vec![entry],
                modules: vec![Vec::new()],
            }],
            items: module.items,
            uses: Vec::new(),
            entry,
            includes: FxHashMap::default(),
            tests: Vec::new(),
            package: FxHashSet::from_iter([entry]),
            depends: Vec::new(),
            imported: Vec::new(),
        }
    }
}

/// Lexes and parses the entry point of `files` and every module it uses,
/// recursively, then each test module that `files` have and every module
/// those use.
///
/// Each module is loaded once, however many modules use it, and modules may
/// use one another. Errors in one file don't stop the others from loading,
/// but the uses of a file that fails to lex or parse are not followed.
pub fn load(files: &mut impl FileManager) -> Result<Program, Vec<Error>> {
    match Loader::run(files, false, None) {
        (program, errors) if errors.is_empty() => Ok(program),
        (_, errors) => Err(errors),
    }
}

/// Loads as [`load`] does, and gives what loaded of a program with errors
/// along with them, for a caller that asks about what is there: of a file
/// with errors, the lines without one, whose uses are followed.
pub fn load_partial(files: &mut impl FileManager) -> (Program, Vec<Error>) {
    Loader::run(files, true, None)
}

/// Loads as [`load_partial`] does, without lexing and parsing again a file
/// that is as it was when `parsed` was last loaded with, which is then what
/// the files are now. A file is known by its id, so `parsed` is of files
/// that are given their ids as these are.
pub fn load_again(files: &mut impl FileManager, parsed: &mut Parsed) -> (Program, Vec<Error>) {
    Loader::run(files, true, Some(parsed))
}

impl<'f, F: FileManager> Loader<'f, F> {
    fn run(
        files: &'f mut F,
        partial: bool,
        parsed: Option<&'f mut Parsed>,
    ) -> (Program, Vec<Error>) {
        let entry = files.entry_point();
        let mut loader = Self {
            files,
            partial,
            parsed,
            seen: FxHashSet::default(),
            loaded: vec![entry],
            items: Vec::new(),
            uses: Vec::new(),
            includes: FxHashMap::default(),
            within: Vec::new(),
            roots: FxHashMap::from_iter([(entry, entry)]),
            depends: Vec::new(),
            imported: Vec::new(),
            errors: Vec::new(),
        };
        loader.seen.insert(entry);
        loader.items_of(entry);
        // A library is compiled whole, as a dependency is.
        if loader.files.settings().world.is_none() {
            loader.load_package(entry);
        }
        // A test module follows the modules of the package that it tests,
        // and those before it, but for one that it uses.
        let tests = loader.files.tests();
        for test in &tests {
            loader.roots.entry(test.file).or_insert(entry);
            if loader.seen.insert(test.file) {
                loader.loaded.push(test.file);
                loader.items_of(test.file);
            }
        }
        let package = loader.package(entry, &tests);
        let packages = loader.group(entry);
        // A file that the program no longer uses is no longer kept.
        if let Some(parsed) = &mut loader.parsed {
            parsed.files.retain(|id, _| loader.seen.contains(id));
        }
        let program = Program {
            items: loader.items,
            packages,
            uses: loader.uses,
            entry,
            includes: loader.includes,
            tests,
            package,
            depends: loader.depends,
            imported: loader.imported,
        };
        (program, loader.errors)
    }

    /// The modules of the package that `entry` is in: it, `tests`, and each
    /// that a path from the root of the package, or from its test
    /// directory, leads to from one of them. A dependency's are not.
    fn package(&self, entry: FileId, tests: &[TestModule]) -> FxHashSet<FileId> {
        let mut package = FxHashSet::from_iter([entry]);
        package.extend(tests.iter().map(|test| test.file));
        let mut found = true;
        while found {
            found = false;
            for (from, target) in &self.within {
                found |= package.contains(from) && package.insert(*target);
            }
        }
        package
    }

    /// Puts the items of each package after those of every package it
    /// depends on, each package's in the order they were loaded, which
    /// keeps those of a module after those of each module it uses. Returns
    /// the packages in that order: the dependencies of each first, in the
    /// order its modules first use them, and then it, and so on from the
    /// package of `entry`.
    fn group(&mut self, entry: FileId) -> Vec<PackageItems> {
        let mut order = Vec::new();
        let mut visited = FxHashSet::default();
        self.visit_package(entry, &mut visited, &mut order);
        let position: FxHashMap<_, _> = order
            .iter()
            .enumerate()
            .map(|(i, root)| (*root, i))
            .collect();
        let package = |item: &Item| {
            let root = self.roots.get(&item.span.file).unwrap_or(&entry);
            position.get(root).copied().unwrap_or(order.len() - 1)
        };
        let mut items: Vec<_> = mem::take(&mut self.items)
            .into_iter()
            .map(|item| (package(&item), item))
            .collect();
        items.sort_by_key(|(package, _)| *package);
        // Sorted, each package's are those up to where the next one's start.
        let mut packages = Vec::new();
        let mut start = 0;
        for (index, root) in order.iter().enumerate() {
            let end = start
                + items[start..]
                    .iter()
                    .take_while(|(p, _)| *p == index)
                    .count();
            let files: Vec<_> = (self.loaded.iter().copied())
                .filter(|file| file == root || self.roots.get(file) == Some(root))
                .collect();
            let modules = files
                .iter()
                .map(|file| self.files.module_path(*file))
                .collect();
            packages.push(PackageItems {
                root: *root,
                name: self.files.package_name(*root),
                items: start..end,
                files,
                modules,
            });
            start = end;
        }
        self.items = items.into_iter().map(|(_, item)| item).collect();
        packages
    }

    /// Adds the package that `root` reaches to `order`, after each it
    /// depends on that isn't there yet.
    fn visit_package(
        &self,
        root: FileId,
        visited: &mut FxHashSet<FileId>,
        order: &mut Vec<FileId>,
    ) {
        if !visited.insert(root) {
            return;
        }
        let depends = self.depends.iter().filter(|depend| depend.from == root);
        for depend in depends {
            self.visit_package(depend.library, visited, order);
        }
        order.push(root);
    }

    /// Records that the package of `root` uses the one whose library is
    /// `library` as `name`.
    fn depend(&mut self, root: FileId, name: &str, library: FileId) {
        self.roots.entry(library).or_insert(library);
        let known = self.depends.iter();
        if !known
            .clone()
            .any(|d| d.from == root && d.library == library)
        {
            self.depends.push(Depend {
                from: root,
                name: name.to_string(),
                library,
            });
        }
    }

    /// Loads the package that `library` enters, which is seen for the
    /// first time: whole, from its artifact if it is compiled already, and
    /// from its files otherwise.
    fn enter(&mut self, library: FileId) {
        match self.files.compiled(library) {
            Some(artifact) => {
                if let Err(e) = self.splice(library, artifact) {
                    self.errors.push(Error::Use(UseError {
                        kind: UseErrorKind::Stale(e.to_string()),
                        span: Span {
                            file: library,
                            start: 0,
                            end: 0,
                        },
                    }));
                }
            }
            None => {
                self.items_of(library);
                self.load_package(library);
            }
        }
    }

    /// Takes the items and uses of the package that `library` enters from
    /// `artifact`, which it is compiled to, in place of reading its files:
    /// each file is opened for its id and nothing more, and each package it
    /// uses is entered in turn. Nothing of it is taken if a file or a
    /// package it names isn't there.
    fn splice(&mut self, library: FileId, artifact: Rc<Artifact>) -> Result<(), DecodeError> {
        let interface = artifact.interface();
        let mut files = vec![library];
        for path in &interface.modules[1..] {
            let path: Vec<&str> = path.iter().map(String::as_str).collect();
            let Some(file) = self.files.open(library, &path) else {
                return Err(DecodeError::missing(&path.join(".")));
            };
            files.push(file);
        }
        let mut libraries = Vec::new();
        for name in &interface.depends {
            let Some(used) = self.files.open_package(library, name) else {
                return Err(DecodeError::missing(name));
            };
            libraries.push(used);
        }
        let declared = interface.declared(&files, &libraries)?;
        for file in &files[1..] {
            self.roots.entry(*file).or_insert(library);
            self.within.push((library, *file));
            if self.seen.insert(*file) {
                self.loaded.push(*file);
            }
        }
        for (name, used) in interface.depends.iter().zip(libraries) {
            self.depend(library, name, used);
            if self.seen.insert(used) {
                self.loaded.push(used);
                self.enter(used);
            }
        }
        self.items.extend(declared.items);
        self.uses.extend(declared.uses);
        for (file, path, bytes) in declared.includes {
            self.includes.insert((file, path), Ok(bytes.into()));
        }
        self.imported.push(Compiled {
            root: library,
            artifact,
        });
        Ok(())
    }

    /// Loads every source file of the package that `root` enters, after
    /// those that are used from it: a package that is used is compiled
    /// whole, so that what it is compiled to is the same whichever of its
    /// modules a program uses, and is kept once for all of them.
    fn load_package(&mut self, root: FileId) {
        for file in self.files.package_files(root) {
            self.roots.entry(file).or_insert(root);
            if self.seen.insert(file) {
                self.loaded.push(file);
                self.within.push((root, file));
                self.items_of(file);
            }
        }
    }

    fn items_of(&mut self, id: FileId) {
        let src = self.files.contents(id);
        let kept = self
            .parsed
            .as_ref()
            .and_then(|parsed| parsed.files.get(&id));
        let read = match kept.filter(|kept| kept.src == src) {
            Some(kept) => kept.clone(),
            None => {
                let read = self.read(id, src);
                if let Some(parsed) = &mut self.parsed {
                    parsed.files.insert(id, read.clone());
                }
                read
            }
        };
        let failed = !read.errors.is_empty();
        self.errors.extend(read.errors);
        let Some(module) = read.module.filter(|_| self.partial || !failed) else {
            return;
        };
        // Uses come first, so the modules they load precede these items,
        // but for one that is being loaded: it uses this module in turn.
        for item in module.items {
            match &item.kind {
                ItemKind::Use(decl) => {
                    for path in &decl.paths {
                        if let Err(kind) = self.use_path(id, &item, path) {
                            let span = path_span(path);
                            self.errors.push(Error::Use(UseError { kind, span }));
                        }
                    }
                }
                _ => {
                    self.include(id, &item);
                    self.items.push(item);
                }
            }
        }
    }

    /// Reads the file that each `module.include` in `item`, an item of the
    /// module `id`, names. One is read once for a module, however many
    /// times the module includes it, and none is kept from one load to the
    /// next, as nothing says whether it is as it was.
    fn include(&mut self, id: FileId, item: &Item) {
        let mut paths = Vec::new();
        visit::each(item, &mut |node| {
            if let Node::Expr(expr) = node {
                paths.extend(expr.included());
            }
        });
        for path in paths {
            let key = (id, path.to_string());
            if !self.includes.contains_key(&key) {
                let included =
                    file::include_path(path).and_then(|path| self.files.include(id, path));
                self.includes.insert(key, included);
            }
        }
    }

    /// Lexes and parses `src`, the contents of file `id`: what parsed of
    /// it, and why not all of it did.
    fn read(&self, id: FileId, src: String) -> Read {
        let (tokens, unlexed) = self.tokens_of(id, src.clone());
        let Some(tokens) = tokens else {
            return Read {
                src,
                module: None,
                errors: unlexed.into_iter().collect(),
            };
        };
        let (module, errors) = parse::parse_partial(&tokens);
        // What is left of a file that doesn't lex may not parse for what
        // was taken from it.
        let errors = match unlexed {
            Some(unlexed) => vec![unlexed],
            None => errors.into_iter().map(Error::Parse).collect(),
        };
        Read {
            src,
            module: Some(module),
            errors,
        }
    }

    /// The tokens of `src`, the contents of file `id`, and why it doesn't
    /// lex, if it doesn't. For one that doesn't they are those of what is
    /// left once each line with an error is blanked, if what loads of a
    /// file is wanted.
    fn tokens_of(&self, id: FileId, mut src: String) -> (Option<Vec<Token>>, Option<Error>) {
        let mut error = match lex::tokenize(id, &src) {
            Ok(tokens) => return (Some(tokens), None),
            Err(error) => error,
        };
        let unlexed = Some(Error::Lex(error.clone()));
        for _ in 0..MAX_BLANKED_LINES {
            if !self.partial || !blank_line(&mut src, error.span.start) {
                break;
            }
            error = match lex::tokenize(id, &src) {
                Ok(tokens) => return (Some(tokens), unlexed),
                Err(error) => error,
            };
        }
        (None, unlexed)
    }

    /// Loads the module `path` leads into, and gives what it names its name
    /// in the module `from`, whose `use` the item `decl` is.
    fn use_path(&mut self, from: FileId, decl: &Item, path: &UsePath) -> Result<(), UseErrorKind> {
        let names: Vec<_> = path.segments.iter().map(|s| s.name.as_str()).collect();
        // The module is the file furthest along the path, and the names
        // after it are found by the type checker.
        let local = (1..=names.len())
            .rev()
            .find_map(|len| Some((self.files.open(from, &names[..len])?, len)));
        // A test module shares what is in its test directory, which only a
        // path that no module of the package is along is looked for from:
        // one named as a module of the package is, as the module it tests,
        // names that module.
        let local = local.or_else(|| {
            let mut lens = (1..=names.len()).rev();
            lens.find_map(|len| Some((self.files.open_test(from, &names[..len])?, len)))
        });
        let dependency = self.files.open_package(from, names[0]);
        let root = self.roots.get(&from).copied().unwrap_or(from);
        let (target, len) = match (local, dependency) {
            (Some(_), Some(_)) => return Err(UseErrorKind::Ambiguous(names[0].to_string())),
            (Some(local), None) => {
                self.within.push((from, local.0));
                self.roots.entry(local.0).or_insert(root);
                local
            }
            // Only what its library makes `pub` is reached in a dependency.
            (None, Some(library)) => {
                self.depend(root, names[0], library);
                (library, 1)
            }
            (None, None) => return Err(UseErrorKind::NotFound(names.join("."))),
        };
        if self.seen.insert(target) {
            self.loaded.push(target);
            match local {
                Some(_) => self.items_of(target),
                None => self.enter(target),
            }
        }
        let name = path.alias.as_ref().or(path.segments.last()).unwrap();
        self.uses.push(Use {
            module: from,
            name: name.clone(),
            target,
            target_path: names[..len].join("."),
            path: path.segments[..len].to_vec(),
            members: path.segments[len..].to_vec(),
            is_pub: decl.is_pub,
            decl: decl.span,
        });
        Ok(())
    }
}

/// Replaces the line of `src` that byte `offset` is in with as many spaces,
/// so that every other line is where it was. Whether that changed it.
fn blank_line(src: &mut String, offset: usize) -> bool {
    let offset = offset.min(src.len());
    let start = src[..offset].rfind('\n').map_or(0, |i| i + 1);
    let end = src[offset..].find('\n').map_or(src.len(), |i| offset + i);
    if src[start..end].trim().is_empty() {
        return false;
    }
    src.replace_range(start..end, &" ".repeat(end - start));
    true
}

/// From the first name of `path` to its last.
fn path_span(path: &UsePath) -> Span {
    let (first, last) = (&path.segments[0], path.segments.last().unwrap());
    Span {
        end: last.span.end,
        ..first.span
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::{IncludeError, Included, Settings, TestModule};
    use crate::ir::{self, Const};
    use crate::lex::TokenKind;
    use crate::parse::{ParseErrorKind, PatternKind};
    use crate::ty::{self, TypeErrorKind};

    /// Files named by the paths that use them; the first is the entry
    /// point. A file named `@name` is the library of dependency `name`,
    /// one named `#path` is what a `module.include` of `path` includes,
    /// one named `~path` is the test module that `path` names from the
    /// test directory, and one named `entry/path` is a file of the package
    /// that `entry` enters that nothing uses.
    struct Memory(Vec<(&'static str, &'static str)>);

    impl Memory {
        fn index(&self, id: FileId) -> usize {
            (0..self.0.len())
                .find(|&i| Self::mint_file_id(i) == id)
                .unwrap()
        }

        fn id(&self, name: &str) -> FileId {
            Self::mint_file_id(self.0.iter().position(|f| f.0 == name).unwrap())
        }

        /// The source text that `span` covers.
        fn text(&self, span: Span) -> &'static str {
            &self.0[self.index(span.file)].1[span.start..span.end]
        }

        fn named(&self, name: &str) -> Option<FileId> {
            let index = self.0.iter().position(|f| f.0 == name);
            Some(Self::mint_file_id(index?))
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
            self.named(&path.join("."))
        }

        fn open_package(&mut self, _from: FileId, name: &str) -> Option<FileId> {
            self.named(&format!("@{name}"))
        }

        fn package_files(&mut self, library: FileId) -> Vec<FileId> {
            let prefix = format!("{}/", self.0[self.index(library)].0);
            let files = self.0.iter().enumerate();
            let files = files.filter(|(_, file)| file.0.starts_with(&prefix));
            files.map(|(index, _)| Self::mint_file_id(index)).collect()
        }

        fn tests(&mut self) -> Vec<TestModule> {
            let tests = self.0.iter().enumerate();
            let tests = tests.filter_map(|(index, file)| Some((index, file.0.strip_prefix('~')?)));
            let test = |(index, path): (usize, &str)| TestModule {
                file: Self::mint_file_id(index),
                path: path.split('.').map(str::to_string).collect(),
            };
            tests.map(test).collect()
        }

        fn open_test(&mut self, from: FileId, path: &[&str]) -> Option<FileId> {
            let tested = self.0[self.index(from)].0.starts_with('~');
            self.named(&format!("~{}", path.join(".")))
                .filter(|_| tested)
        }

        fn include(&mut self, _from: FileId, path: &str) -> Included {
            match self.0.iter().find(|f| f.0.strip_prefix('#') == Some(path)) {
                Some(file) => Ok(file.1.as_bytes().into()),
                None => Err(IncludeError::NotFound("no such file".to_string())),
            }
        }

        fn settings(&mut self) -> Settings {
            Settings::default()
        }
    }

    /// The name of each item, followed by the file it came from.
    fn items(files: &mut Memory) -> Vec<String> {
        let program = load(files).unwrap();
        let name = |item: &Item| match &item.kind {
            ItemKind::Fn(f) => f.sig.name.name.clone(),
            ItemKind::Binding(b) => match &b.pattern.kind {
                PatternKind::Name(name) => name.clone(),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        };
        program
            .items
            .iter()
            .map(|item| format!("{} {}", name(item), files.display_name(item.span.file)))
            .collect()
    }

    #[test]
    fn a_library_is_loaded_whole() {
        // The entry is a library, as it has no world: every file of its
        // package is loaded, and every file of each library it uses.
        let mut files = Memory(vec![
            ("main", "use geo\nlet a = geo.one\n"),
            ("@geo", "pub let one = 1\n"),
            ("@geo/extra", "let b = 2\n"),
            ("main/side", "let c = 3\n"),
        ]);
        assert_eq!(
            items(&mut files),
            ["one @geo", "b @geo/extra", "a main", "c main/side"]
        );
        let program = load(&mut files).unwrap();
        let roots: Vec<_> = program.packages.iter().map(|p| p.items.clone()).collect();
        assert_eq!(roots, [0..2, 2..4]);
        assert!(program.package.contains(&files.id("main/side")));
        assert!(!program.package.contains(&files.id("@geo/extra")));
    }

    #[test]
    fn what_loads_of_a_program_with_errors_is_what_lexes_and_parses() {
        let mut files = Memory(vec![
            ("main", "use a\nlet x =\nlet y = a.one\n"),
            (
                "a",
                "use b\npub let one = 1\nlet s = \"\nlet t = (\nlet u = 2\n",
            ),
            ("b", "let v = @\n"),
        ]);
        // The uses of a file with an error aren't followed, unless what
        // loads of it is wanted.
        let strict = load(&mut files).unwrap_err();
        assert_eq!(strict.len(), 1, "{strict:?}");
        let (program, errors) = load_partial(&mut files);
        assert_eq!(errors[..1], strict);
        let kinds: Vec<_> = errors[1..].iter().map(|error| error.to_string()).collect();
        // A file that doesn't lex has the one error, though more than the
        // one line is left out of it.
        assert_eq!(
            kinds,
            ["unterminated string literal", "unexpected character '@'"]
        );
        let names = program.items.iter().map(|item| match &item.kind {
            ItemKind::Binding(b) => match &b.pattern.kind {
                PatternKind::Name(name) => name.as_str(),
                _ => unreachable!(),
            },
            _ => unreachable!(),
        });
        assert_eq!(names.collect::<Vec<_>>(), ["one", "u", "y"]);
        assert_eq!(program.uses.len(), 2);
    }

    fn compile(files: &mut Memory) -> Result<ir::Module, Vec<Error>> {
        let program = load(files)?;
        ty::check(&program, &files.settings())
            .map_err(|errors| errors.into_iter().map(Error::Type).collect())
    }

    /// The name of each test of `files`, in the order they are run in.
    fn tests(files: &mut Memory) -> Vec<String> {
        let program = load(files).unwrap();
        let tested = ty::check_tests(&program, &files.settings()).unwrap();
        tested.tests.into_iter().map(|test| test.name).collect()
    }

    fn lower(files: &mut Memory) -> ir::Module {
        match compile(files) {
            Ok(module) => module,
            Err(errors) => panic!("unexpected errors: {errors:#?}"),
        }
    }

    /// Each error's message, and the file and text it points at.
    fn errors(files: &mut Memory) -> Vec<String> {
        compile(files)
            .unwrap_err()
            .iter()
            .map(|e| {
                let span = e.span().unwrap();
                let file = files.display_name(span.file);
                format!("{file} {:?}: {e}", files.text(span))
            })
            .collect()
    }

    fn type_errors(files: &mut Memory) -> Vec<TypeErrorKind> {
        compile(files)
            .unwrap_err()
            .into_iter()
            .map(|e| match e {
                Error::Type(e) => e.kind,
                e => panic!("{e:?}"),
            })
            .collect()
    }

    fn exports(module: &ir::Module) -> Vec<&str> {
        let funcs = module.funcs.iter().flat_map(|f| &f.exports);
        let globals = module.globals.iter().flat_map(|g| &g.exports);
        funcs.chain(globals).map(String::as_str).collect()
    }

    #[test]
    fn a_file_that_is_as_it_was_is_loaded_as_it_last_parsed() {
        let mut parsed = Parsed::default();
        let mut files = Memory(vec![
            ("main", "use a\nuse b\nlet x = a.y\n"),
            ("a", "pub let y = 1\n"),
            ("b", ""),
        ]);
        let first = load_again(&mut files, &mut parsed);
        assert_eq!(first, load_partial(&mut files));
        assert_eq!(first.1, []);
        assert_eq!(load_again(&mut files, &mut parsed), first);
        // One that changed is read as it is now, with what is wrong with
        // it, which is said again of it for as long as it is so.
        files.0[1].1 = "pub let y = @\npub let z = 2\n";
        let changed = load_again(&mut files, &mut parsed);
        assert_eq!(changed, load_partial(&mut files));
        assert_eq!(changed.0.items.len(), 2);
        assert_eq!(changed.1.len(), 1);
        assert_eq!(load_again(&mut files, &mut parsed), changed);
        files.0[1].1 = "pub let y = 1\n";
        assert_eq!(load_again(&mut files, &mut parsed), first);
        // One that the program uses no longer is kept no longer.
        assert_eq!(parsed.files.len(), 3);
        files.0[0].1 = "use a\nlet x = a.y\n";
        assert_eq!(
            load_again(&mut files, &mut parsed),
            load_partial(&mut files)
        );
        assert_eq!(parsed.files.len(), 2);
    }

    #[test]
    fn test_modules_follow_the_modules_of_the_package() {
        let mut files = Memory(vec![
            ("main", "use b\nlet a = 1\n"),
            ("b", "let b = 2\n"),
            // One that only a test uses is loaded for it.
            ("c", "let c = 3\n"),
            ("~late", "use support\nuse c\nlet late = 4\n"),
            ("~deep.early", "let early = 5\n"),
            ("~support", "let support = 6\n"),
        ]);
        // Each test module after those before it, but for one it uses.
        assert_eq!(
            items(&mut files),
            [
                "b b",
                "a main",
                "support ~support",
                "c c",
                "late ~late",
                "early ~deep.early"
            ]
        );
        let program = load(&mut files).unwrap();
        let tests: Vec<_> = program
            .tests
            .iter()
            .map(|test| test.path.join("."))
            .collect();
        assert_eq!(tests, ["late", "deep.early", "support"]);
        let files_of = |names: &[&str]| -> FxHashSet<FileId> {
            names.iter().map(|name| files.id(name)).collect()
        };
        assert_eq!(
            program.package,
            files_of(&["main", "b", "c", "~late", "~deep.early", "~support"])
        );

        // Files without a test directory have none, and nothing of one is
        // loaded.
        let mut files = Memory(vec![("main", "use b\nlet a = 1\n"), ("b", "let b = 2\n")]);
        let program = load(&mut files).unwrap();
        assert_eq!(program.tests, []);
        assert_eq!(program.package, files_of_all(&files, &["main", "b"]));
    }

    /// The ids of the files of `files` that `names` name.
    fn files_of_all(files: &Memory, names: &[&str]) -> FxHashSet<FileId> {
        names.iter().map(|name| files.id(name)).collect()
    }

    #[test]
    fn a_dependency_is_no_module_of_the_package() {
        let mut files = Memory(vec![
            ("main", "use json\nuse inner\n"),
            ("inner", ""),
            ("@json", "use deep\nuse text\n"),
            ("deep", ""),
            ("@text", ""),
            ("~checks", "use json\n"),
        ]);
        let program = load(&mut files).unwrap();
        // What a dependency reaches from its own root is the dependency's.
        assert_eq!(
            program.package,
            files_of_all(&files, &["main", "inner", "~checks"])
        );
    }

    #[test]
    fn a_test_module_uses_the_package_and_then_its_test_directory() {
        let mut files = Memory(vec![
            ("main", "use geo\npub let one = geo.unit\n"),
            ("geo", "pub let unit = 1\n"),
            ("geo.shapes", "pub let sides = 4\n"),
            (
                "~geometry",
                "use geo\nuse geo.shapes.sides\nuse support\nuse support.deep.two\nuse json\nlet x = geo.unit + sides + support.one + two + json.three\n",
            ),
            ("~support", "pub let one = 1\n"),
            ("~support.deep", "pub let two = 2\n"),
            ("@json", "pub let three = 3\n"),
        ]);
        lower(&mut files);
        let program = load(&mut files).unwrap();
        let uses = program
            .uses
            .iter()
            .filter(|u| u.module == files.id("~geometry"));
        let targets: Vec<_> = uses.map(|u| files.0[files.index(u.target)].0).collect();
        assert_eq!(
            targets,
            ["geo", "geo.shapes", "~support", "~support.deep", "@json"]
        );

        // Only a test module is led into the test directory.
        let mut files = Memory(vec![
            ("main", "use support\nuse json\n"),
            ("@json", "use support\n"),
            ("~support", ""),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"support\": cannot find `support` in this package or its dependencies",
                "@json \"support\": cannot find `support` in this package or its dependencies",
            ]
        );
    }

    #[test]
    fn a_test_module_is_named_as_the_module_it_tests() {
        // As `tests/geo.duck` is beside `src/geo.duck`: the name is that of
        // the module of the package, to the test module too.
        let mut files = Memory(vec![
            ("main", "use geo\n"),
            ("geo", "let unit = 1\n"),
            (
                "~geo",
                "use geo\nuse geo.unit as one\npub fn has_a_unit():\n    geo.unit == one or module.unreachable()\n",
            ),
        ]);
        lower(&mut files);
        assert_eq!(tests(&mut files), ["geo.has_a_unit"]);
        let program = load(&mut files).unwrap();
        let uses = program.uses.iter().filter(|u| u.module == files.id("~geo"));
        let targets: Vec<_> = uses.map(|u| u.target).collect();
        assert_eq!(targets, [files.id("geo"), files.id("geo")]);
    }

    #[test]
    fn a_module_of_the_package_hides_one_of_the_test_directory() {
        let checks = "\
use support
use support.limit
use util.text
use util.numbers
let x = support.limit + limit + text.len + numbers.count
";
        let package = |checks: &'static str| {
            vec![
                ("main", "use support\n"),
                ("support", "pub let limit = 1\n"),
                ("util.text", "pub let len = 4\n"),
                ("geo", ""),
                ("~checks", checks),
                // What a test module shares, which the package has a module
                // named as.
                ("~support", "pub let limit = 2\nlet only = 3\n"),
                // A directory holds modules of both without being one.
                ("~util.numbers", "pub let count = 5\n"),
                ("~geo.shapes", ""),
                ("~json", ""),
                ("@json", ""),
            ]
        };
        let mut files = Memory(package(checks));
        lower(&mut files);
        let program = load(&mut files).unwrap();
        let uses = program
            .uses
            .iter()
            .filter(|u| u.module == files.id("~checks"));
        let targets: Vec<_> = uses.map(|u| files.0[files.index(u.target)].0).collect();
        assert_eq!(
            targets,
            ["support", "support", "util.text", "~util.numbers"]
        );

        // The test directory is looked in only for a path that no module of
        // the package is along, however far along it one of its own is.
        let mut files = Memory(package("use support.only\nuse geo.shapes\n"));
        assert_eq!(
            errors(&mut files),
            [
                "~checks \"only\": `support` has no item `only`",
                "~checks \"shapes\": `geo` has no item `shapes`",
            ]
        );
        // A dependency is still named as no module is, of either.
        let mut files = Memory(package("use json\nuse missing\n"));
        assert_eq!(
            errors(&mut files),
            [
                "~checks \"json\": `json` is both a module of this package and a dependency",
                "~checks \"missing\": cannot find `missing` in this package or its dependencies",
            ]
        );
    }

    #[test]
    fn a_test_module_sees_all_of_its_package() {
        let geo = "\
use inner as hidden
let unit = 1
var count = 0
struct Point:
    x: i32
    pub y: i32 = 2
enum(u8) Color:
    red
let Step: type = fn(i32) -> i32
fn double(n: i32) -> i32:
    return n * 2
fn(T) id(x: T) -> T:
    return x
fn make() -> opaque(Point):
    return Point(x: 1)
extern \"wasi:cli/exit@0.3.0\":
    fn exit_with_code(status: u8)
";
        let checks = "\
use geo
use geo.{Point, Color, double, id, unit, Step, hidden}
use support
fn area(p: Point, c: Color, step: Step) -> i32:
    geo.count += 1
    geo.exit_with_code(geo.count as u8)
    let made = geo.make()
    var q = Point(x: 3, y: 4)
    q.x = 5
    return p.x + q.x + double(unit) + id(c as u8) as i32 + hidden.kept + (made as Point).x
struct Corner:
    use Point
    pub z: i32
pub struct Shown:
    pub at: Point
pub let origin = Point(x: 0)
pub fn passes():
    support.check(area(origin, .red, double) == Corner(x: 1, z: 3).x + support.limit)
";
        let support = "let limit = 9\nfn check(ok: bool):\n    ok or module.unreachable()\n";
        let package = |main: &'static str| {
            vec![
                ("main", main),
                ("geo", geo),
                ("inner", "let kept = 7\n"),
                ("~checks", checks),
                ("~support", support),
            ]
        };
        let mut files = Memory(package("use geo\n"));
        lower(&mut files);
        assert_eq!(tests(&mut files), ["checks.passes"]);

        // A module of the package sees of another only what any does.
        let main = "use geo\nlet a = geo.unit\nfn f(p: geo.Point) -> i32:\n    return p.x\n";
        let mut files = Memory(package(main));
        assert_eq!(
            errors(&mut files),
            [
                "main \"Point\": `Point` is private",
                "main \"unit\": `unit` is private",
            ]
        );
    }

    #[test]
    fn a_test_module_sees_of_a_dependency_what_any_module_does() {
        let json = "\
use text
pub struct Value:
    pub open: i32
    kept: i32 = 1
pub struct Sealed:
    key: i32
struct Hidden:
    x: i32
pub struct Holder:
    pub held: &Hidden
let secret = 1
fn parse() -> Value:
    return Value(open: text.zero)
pub fn new() -> Value:
    return parse()
";
        let checks = "\
use json
use json.secret
struct Mine:
    use json.Holder
pub fn reads():
    let v = json.new()
    let _ = v.kept + json.parse().open
    let _ = json.Value(open: 1, kept: 2)
    let _ = json.Sealed(key: 1)
    let _: json.Hidden = json.Hidden(x: 1)
";
        let mut files = Memory(vec![
            ("main", "use json\n"),
            ("@json", json),
            // What a dependency reaches from its root is the dependency's.
            ("text", "pub let zero = 0\n"),
            ("~checks", checks),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "~checks \"secret\": `secret` is private",
                "@json \"&Hidden\": private type `Hidden` in the type of `pub` item `held`",
                "~checks \"json.Holder\": `use` of `held`, whose type holds the private `Hidden`",
                "~checks \"kept\": field `kept` of `Value` is private",
                "~checks \"parse\": `parse` is private",
                "~checks \"kept\": field `kept` of `Value` is private",
                "~checks \"json.Sealed(key: 1)\": field `key` of `Sealed` is private",
                "~checks \"Hidden\": `Hidden` is private",
                "~checks \"Hidden\": `Hidden` is private",
            ]
        );
    }

    #[test]
    fn a_pub_fn_of_a_test_module_is_a_test() {
        let mut files = Memory(vec![
            (
                "main",
                "pub fn main():\n    pass\npub fn takes(n: i32) -> i32:\n    return n\n",
            ),
            (
                "~b.checks",
                "pub fn second():\n    pass\nfn helper(n: i32) -> i32:\n    return n\npub fn third():\n    todo\n",
            ),
            ("~a", "use b.checks\npub fn first():\n    pass\n"),
        ]);
        // Those of a module as it declares them, and the modules as the
        // files have them, whichever is loaded first.
        assert_eq!(
            tests(&mut files),
            ["b.checks.second", "b.checks.third", "a.first"]
        );
        let program = load(&mut files).unwrap();
        let tested = ty::check_tests(&program, &files.settings()).unwrap();
        assert_eq!(
            files.text(tested.tests[2].span),
            "pub fn first():\n    pass"
        );
        assert_eq!(tested.tests[2].span.file, files.id("~a"));

        let checks = "\
pub fn takes(n: i32):
    pass
pub fn defaults(n: i32 = 1):
    pass
pub fn gives() -> i32:
    return 1
pub fn stops() -> never:
    todo
pub fn pending() -> todo:
    todo
pub fn(T) infers(x: T):
    pass
pub fn typed(T: type):
    pass
pub fn unit() -> tuple():
    return ()
pub fn unknown() -> Nope:
    pass
extern:
    pub fn log(n: i32)
pub struct Fixture:
    pub n: i32
pub let limit = 1
";
        let mut files = Memory(vec![("main", ""), ("~checks", checks)]);
        let no_test = |name: &str| {
            format!(
                "~checks {name:?}: a `pub fn` of a test module is a test, which takes nothing and \
                 returns nothing: `{name}` is a helper without its `pub`"
            )
        };
        assert_eq!(
            errors(&mut files),
            [
                "~checks \"Nope\": unknown type `Nope`".to_string(),
                no_test("takes"),
                no_test("defaults"),
                no_test("gives"),
                // A test passes by returning, which neither ever does.
                no_test("stops"),
                no_test("pending"),
                no_test("infers"),
                no_test("typed"),
            ]
        );
        let code = compile(&mut files).unwrap_err()[1].code();
        assert_eq!(code, "invalid-test");
    }

    #[test]
    fn a_pub_item_of_a_test_module_is_given_to_no_one() {
        // So its type holds what the package keeps to itself.
        let geo = "struct Point:\n    x: i32 = 0\nenum(u8) Color:\n    red\n";
        let checks = "\
use geo.{Point, Color}
struct Own:
    x: i32 = 0
pub struct Fixture:
    pub at: Point
    pub own: Own
pub union Either:
    point: Point
pub let origin = Point()
pub let Tint: type = Color
extern:
    pub fn log(at: Point)
";
        let mut files = Memory(vec![
            ("main", "use geo\n"),
            ("geo", geo),
            ("~checks", checks),
        ]);
        lower(&mut files);
        // A module of the package gives another package what is `pub`.
        let mut files = Memory(vec![
            ("main", "use geo\n"),
            (
                "geo",
                "struct Point:\n    x: i32 = 0\npub let origin = Point()\n",
            ),
            ("~checks", ""),
        ]);
        assert_eq!(
            errors(&mut files),
            ["geo \"origin\": private type `Point` in the type of `pub` item `origin`"]
        );
    }

    #[test]
    fn modules_follow_the_modules_they_use() {
        let mut files = Memory(vec![
            ("main", "use b\nuse e\nlet a = 1\nlet d = 4\n"),
            ("b", "use c\nlet b = 2\n"),
            ("c", "let c = 3\n"),
            ("e", "fn e():\n    pass\n"),
        ]);
        assert_eq!(items(&mut files), ["c c", "b b", "e e", "a main", "d main"]);
        let program = load(&mut files).unwrap();
        assert_eq!(program.items[0].span.file, files.id("c"));
        assert_eq!(files.text(program.items[0].span), "let c = 3");
    }

    #[test]
    fn a_module_used_twice_is_loaded_once() {
        let mut files = Memory(vec![
            ("main", "use a\nuse b\nuse a.a as one\nlet m = 0\n"),
            ("a", "pub let a = 1\n"),
            ("b", "use a\nlet b = 2\n"),
        ]);
        assert_eq!(items(&mut files), ["a a", "b b", "m main"]);
    }

    #[test]
    fn globals_are_initialized_after_those_they_use() {
        let mut files = Memory(vec![
            ("main", "use b\npub let c = b.b + 1\n"),
            ("b", "use a.a\npub let b = a + 1\n"),
            ("a", "pub let a = 1\n"),
        ]);
        let module = lower(&mut files);
        let inits: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        // Only the entry module's are exported, so only they are wasm globals.
        assert_eq!(inits, [Const::I32(3)]);
    }

    #[test]
    fn constants_run_in_the_order_modules_are_used() {
        // Those of `b` run before those of `main`, which uses it, and so
        // call `next` first.
        let mut files = Memory(vec![
            (
                "main",
                "use b\nuse a\npub let last = a.next() * 10 + b.first\n",
            ),
            (
                "a",
                "var count = 0\npub fn next() -> i32:\n    count += 1\n    return count\n",
            ),
            ("b", "use a\npub let first = a.next()\n"),
        ]);
        let module = lower(&mut files);
        let inits: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        // `count`, as the calls left it, and `last`.
        assert_eq!(inits, [Const::I32(2), Const::I32(21)]);
    }

    #[test]
    fn modules_use_each_other() {
        let mut files = Memory(vec![
            (
                "main",
                "use a\nuse b\npub let x = a.y + 1\npub let v = b.w\npub fn f() -> i32:\n    return a.g()\n",
            ),
            (
                "a",
                "use b\npub let y = b.z * 2\npub fn g() -> i32:\n    return b.h(b.P(n: y))\n",
            ),
            (
                "b",
                "use main.x\nuse a\nuse b\npub let z = 3\npub let w = x + a.y + b.z\npub struct P:\n    pub n: i32 = w\npub fn h(p: P) -> i32:\n    return p.n + P().n + a.g()\n",
            ),
        ]);
        let program = load(&mut files).unwrap();
        let modules: Vec<_> = program.items.iter().map(|item| item.span.file).collect();
        // Each is loaded once, after those it uses that aren't being loaded.
        let (main, a, b) = (files.id("main"), files.id("a"), files.id("b"));
        assert_eq!(modules, [b, b, b, b, a, a, main, main, main]);
        let module = lower(&mut files);
        let inits: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        // `w` is first to use `x`, which is first to use `y`.
        assert_eq!(inits, [Const::I32(7), Const::I32(16)]);
    }

    #[test]
    fn uses_reach_names_through_uses_that_follow_them() {
        let mut files = Memory(vec![
            ("main", "use a\npub let n = a.b.m\n"),
            ("a", "pub use b\npub use b.T\npub let one = 1\n"),
            (
                "b",
                "use a\nuse a.T as U\nuse a.b.T as V\npub struct T:\n    pub n: i32 = 2\npub let m = U().n + V().n + a.one\n",
            ),
        ]);
        let module = lower(&mut files);
        assert_eq!(module.globals[0].init, Const::I32(5));
    }

    #[test]
    fn uses_do_not_lead_back_to_themselves() {
        let mut files = Memory(vec![
            ("main", "use a.{x, y}\nuse main.me\nlet z = x + y + me\n"),
            ("a", "use b\npub use b.x\npub use b.y\n"),
            ("b", "pub use a.x\npub use b.c.y\nuse b as c\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "a \"x\": `use` of `b.x` leads back to itself",
                "b \"y\": `use` of `b.c.y` leads back to itself",
                "main \"me\": `use` of `main.me` leads back to itself",
            ]
        );
    }

    #[test]
    fn missing_modules() {
        let mut files = Memory(vec![
            ("main", "use nope\nuse util\nuse util.nope.x\nlet a = 1\n"),
            // A directory holds modules without being one.
            ("util.strings", ""),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"nope\": cannot find `nope` in this package or its dependencies",
                "main \"util\": cannot find `util` in this package or its dependencies",
                "main \"util.nope.x\": cannot find `util.nope.x` in this package or its dependencies",
            ]
        );

        // Past the module, the path names its items.
        let mut files = Memory(vec![("main", "use a.{b, nope.c}\n"), ("a", "")]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"b\": `a` has no item `b`",
                "main \"nope\": `a` has no item `nope`",
            ]
        );

        // One that the module has a name near is likely that, if this
        // module sees it.
        let mut files = Memory(vec![
            (
                "main",
                "use geo.lenght\nuse geo\nlet a: geo.Piont = geo.orgin\nlet b = geo.hiden\n",
            ),
            (
                "geo",
                "pub struct Point:\n    x: i32 = 0\npub let origin = Point()\npub fn length() -> i32:\n    return 0\nlet hidden = 1\n",
            ),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"lenght\": `geo` has no item `lenght`; did you mean `length`?",
                "main \"Piont\": `geo` has no item `Piont`; did you mean `Point`?",
                "main \"orgin\": `geo` has no item `orgin`; did you mean `origin`?",
                "main \"hiden\": `geo` has no item `hiden`",
            ]
        );
    }

    #[test]
    fn modules_are_named_by_their_last_name_unless_renamed() {
        let mut files = Memory(vec![
            (
                "main",
                "use util.strings\nuse util.strings as text\nuse json as j\nuse json.c\nlet x = strings.a + text.a + j.c + c\n",
            ),
            ("util.strings", "pub let a = 1\n"),
            ("@json", "pub let c = 3\n"),
        ]);
        lower(&mut files);
    }

    #[test]
    fn the_module_is_the_file_furthest_along_the_path() {
        let mut files = Memory(vec![
            (
                "main",
                "use a.b\nuse a.b.c\nuse a.d\nuse a.{b as inner, b.c as two}\nlet x = b.c + c + d + inner.c + two\n",
            ),
            // The item `b` is hidden by the file of that name.
            ("a", "pub let b = 1\npub let d = 4\n"),
            ("a.b", "pub let c = 2\n"),
        ]);
        lower(&mut files);
        let program = load(&mut files).unwrap();
        let uses: Vec<_> = (program.uses.iter())
            .map(|u| {
                (
                    u.name.name.as_str(),
                    u.target_path.as_str(),
                    u.members.len(),
                )
            })
            .collect();
        assert_eq!(
            uses,
            [
                ("b", "a.b", 0),
                ("c", "a.b", 1),
                ("d", "a", 1),
                ("inner", "a.b", 0),
                ("two", "a.b", 1),
            ]
        );
    }

    #[test]
    fn a_name_is_a_module_or_a_dependency_not_both() {
        let mut files = Memory(vec![
            ("main", "use json\nuse text.Value\nuse text.inner.x\n"),
            ("json", ""),
            ("@json", ""),
            ("text.inner", ""),
            ("@text", "pub let Value = 1\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"json\": `json` is both a module of this package and a dependency",
                "main \"text.inner.x\": `text` is both a module of this package and a dependency",
            ]
        );
    }

    #[test]
    fn errors_point_into_the_file_they_are_in() {
        let mut files = Memory(vec![
            ("main", "use a\nuse b\nlet x = 1\n"),
            ("a", "let x = 1\nlet y = @\n"),
            ("b", "fn f(: i32):\n    pass\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "a \"@\": unexpected character '@'",
                "b \":\": expected identifier, found `:`",
            ]
        );

        let mut files = Memory(vec![
            ("main", "use a\nlet x = 1\nlet x = 2\n"),
            ("a", "\nlet x = 2\nlet y: Nope = 3\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"x\": `x` is already defined",
                "a \"Nope\": unknown type `Nope`",
            ]
        );
    }

    #[test]
    fn use_syntax() {
        let mut files = Memory(vec![("main", "use a as\nfn f():\n    use a\n"), ("a", "")]);
        let kinds: Vec<_> = load(&mut files)
            .unwrap_err()
            .into_iter()
            .map(|e| match e {
                Error::Parse(e) => e.kind,
                e => panic!("{e:?}"),
            })
            .collect();
        assert_eq!(
            kinds,
            [
                ParseErrorKind::Expected {
                    expected: "identifier".into(),
                    found: TokenKind::Newline,
                },
                ParseErrorKind::Expected {
                    expected: "expression".into(),
                    found: TokenKind::Use,
                },
            ]
        );
    }

    #[test]
    fn items_of_other_modules_are_reached_through_their_name() {
        let mut files = Memory(vec![
            (
                "main",
                "use geo\nfn f() -> f32:\n    let p = geo.Point(x: 1.0, y: geo.origin.y)\n    return geo.len(p) + geo.unit.x\n",
            ),
            (
                "geo",
                "pub struct Point:\n    pub x: f32\n    pub y: f32\npub let origin = Point(x: 0.0, y: 0.0)\npub var unit = Point(x: 1.0, y: 1.0)\npub fn len(p: Point) -> f32:\n    return p.x + p.y\n",
            ),
        ]);
        lower(&mut files);
    }

    #[test]
    fn used_items_are_named_alone() {
        let geo = "pub struct Point:\n    pub x: f32\n    pub y: f32\npub let origin = Point(x: 0.0, y: 0.0)\npub var unit = Point(x: 1.0, y: 1.0)\npub fn len(p: Point) -> f32:\n    return p.x + p.y\n";
        let main = "\
use geo.{Point, origin, unit, len as length}
fn f(q: &Point) -> f32:
    let p: Point = Point(x: 1.0, y: origin.y)
    unit.x = q.x
    return length(p) + unit.x
";
        let mut files = Memory(vec![("main", main), ("geo", geo)]);
        lower(&mut files);

        // Only the name it is used by is declared.
        let main = "use geo.len as length\nfn f(p: geo.Point) -> f32:\n    return len(p)\n";
        let mut files = Memory(vec![("main", main), ("geo", geo)]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"geo\": unknown name `geo`",
                "main \"len\": unknown name `len`",
            ]
        );
    }

    #[test]
    fn names_are_local_to_their_module() {
        let mut files = Memory(vec![
            ("main", "use a\nlet x = 1\nfn f():\n    g()\n"),
            ("a", "let x = 2\nfn g():\n    pass\n"),
        ]);
        assert_eq!(
            type_errors(&mut files),
            [TypeErrorKind::UnknownName("g".to_string())]
        );
    }

    #[test]
    fn private_items_are_unreachable_from_other_modules() {
        let a = "let x = 2\nfn g():\n    pass\nstruct P:\n    pub y: i32\npub let p = 0\n";
        let mut files = Memory(vec![
            (
                "main",
                "use a\nfn f():\n    a.g()\n    let x = a.x\n    let p: a.P = a.p\n    a.nope()\n",
            ),
            ("a", a),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"g\": `g` is private",
                "main \"x\": `x` is private",
                "main \"P\": `P` is private",
                "main \"nope\": `a` has no item `nope`",
            ]
        );

        // A name that can't be used is an error once, where it is used.
        let mut files = Memory(vec![
            (
                "main",
                "use a.{g, x, P, p, nope}\nfn f():\n    g()\n    let y = x\n    let q: P = p\n    nope()\n",
            ),
            ("a", a),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"g\": `g` is private",
                "main \"x\": `x` is private",
                "main \"P\": `P` is private",
                "main \"nope\": `a` has no item `nope`",
            ]
        );
    }

    #[test]
    fn pub_uses_are_reachable_through_the_using_module() {
        let value = "pub struct Value:\n    pub n: i32\npub let one = 1\n";
        let mut files = Memory(vec![
            (
                "main",
                "use lib\nlet x: lib.value.Value = lib.value.Value(n: lib.value.one)\nlet y = lib.inner.one\n",
            ),
            ("lib", "pub use value\nuse value as inner\n"),
            ("value", value),
        ]);
        assert_eq!(errors(&mut files), ["main \"inner\": `inner` is private"]);

        // A path goes on through them, and they name items as well.
        let mut files = Memory(vec![
            (
                "main",
                "use lib.{value.one, Value, uno, inner.one as hidden, two}\nlet x: Value = Value(n: one + uno)\n",
            ),
            (
                "lib",
                "pub use value\npub use value.{Value, one as uno}\nuse value as inner\nuse value.one as two\n",
            ),
            ("value", value),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"inner\": `inner` is private",
                "main \"two\": `two` is private",
            ]
        );
    }

    #[test]
    fn use_paths_go_on_through_modules_only() {
        let mut files = Memory(vec![
            (
                "main",
                "use lib.Color.Red\nuse lib.one.two\nuse lib.Color\nlet c = Color.Red\n",
            ),
            (
                "lib",
                "pub enum(u8) Color:\n    Red\n    Green\npub let one = 1\n",
            ),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"Red\": `lib.Color` is not a module",
                "main \"two\": `lib.one` is not a module",
            ]
        );
    }

    #[test]
    fn qualified_generics_and_enums() {
        let lib = "pub struct(T) Box:\n    pub v: T\npub enum(u8) Color:\n    Red\n    Green\npub fn(T) id(x: T) -> T:\n    return x\n";
        let mut files = Memory(vec![
            (
                "main",
                "use lib\nfn f() -> i32:\n    let b: lib.Box(lib.Color) = lib.Box(lib.Color)(v: lib.Color.Red)\n    let size = lib.Box(i64).size\n    var n = lib.id(b.v) as i32\n    for c in lib.Color:\n        n += c as i32\n    return n + lib.id(size as i32)\n",
            ),
            ("lib", lib),
        ]);
        lower(&mut files);

        let mut files = Memory(vec![
            (
                "main",
                "use lib.{Box, Color, id}\nfn f() -> i32:\n    let b: Box(Color) = Box(Color)(v: Color.Red)\n    let size = Box(i64).size\n    var n = id(b.v) as i32\n    for c in Color:\n        n += c as i32\n    return n + id(size as i32)\n",
            ),
            ("lib", lib),
        ]);
        lower(&mut files);
    }

    #[test]
    fn bounds_read_fields_whether_or_not_they_are_pub() {
        let lib = "\
pub struct Head:
    pub id: i32
    tag: u8
pub fn(T: Head) id(x: &T) -> i32:
    return x.id + x.tag as i32
";
        let main = "\
use lib
struct Mine:
    use lib.Head
    rest: i64
fn(T: lib.Head) peek(x: &T) -> i32:
    return x.id
fn f(m: &Mine) -> i32:
    return lib.id(m) + peek(m)
";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        lower(&mut files);

        // What reads a field of the bound must see it in the bound.
        let main = "\
use lib
fn(T: lib.Head) peek(x: &T) -> u8:
    return x.tag
";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        assert_eq!(
            errors(&mut files),
            ["main \"tag\": field `tag` of `Head` is private"]
        );

        // A list has each field as the struct that it lists does.
        let main = "\
use lib
struct Meta:
    flag: u8
struct Mine:
    use lib.Head
    use Meta
fn(T: (lib.Head, Meta)) peek(x: &T) -> u8:
    return x.flag + x.tag
fn f(m: &Mine) -> u8:
    return peek(m)
";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        assert_eq!(
            errors(&mut files),
            ["main \"tag\": field `tag` of `(Head, Meta)` is private"]
        );
    }

    #[test]
    fn a_function_of_another_module_is_named_as_a_type() {
        let lib = "\
pub struct(T, R: fn(uint) -> &var T) Pool:
    pub make: R
pub fn bump(size: uint) -> &var u8:
    return 8
fn secret(size: uint) -> &var u8:
    return 8
";
        let main = "\
use lib
use lib.Pool
fn f(pool: &Pool(u8, lib.bump)) -> &var u8:
    return pool.make(1)
";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        let module = lower(&mut files);
        assert_eq!(module.table, None);
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        let bump = module.funcs.iter().position(|f| f.name == "bump").unwrap();
        let called = format!("Call(FuncId({bump})");
        assert!(format!("{:?}", f.body).contains(&called), "{:?}", f.body);

        // One that its module keeps to itself is no type outside it.
        let main = "use lib\nfn f(make: lib.secret):\n    pass\n";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        assert_eq!(errors(&mut files), ["main \"secret\": `secret` is private"]);
    }

    #[test]
    fn a_name_of_a_type_is_used_as_any_item_is() {
        let lib = "\
pub let Make: type = fn(uint) -> &var u8
let Kept: type = i32
pub fn bump(size: uint) -> &var u8:
    return 8
";
        let main = "\
use lib
use lib.Make as Maker
fn(R: lib.Make) take(make: R) -> &var u8:
    return make(1)
fn f(make: Maker) -> &var u8:
    return take(lib.bump)
";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        let module = lower(&mut files);
        let names: Vec<_> = module.funcs.iter().map(|f| f.name.as_str()).collect();
        assert!(names.contains(&"take(bump)"), "{names:?}");
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        assert_eq!(f.params.len(), 1);

        let main = "use lib\nfn f(n: lib.Kept):\n    pass\n";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        assert_eq!(errors(&mut files), ["main \"Kept\": `Kept` is private"]);
    }

    #[test]
    fn functions_of_other_modules_are_pointed_to() {
        let lib = "\
pub fn inc(x: i32) -> i32:
    return x + 1
pub fn(T) id(x: T) -> T:
    return x
pub fn hidden() -> fn(i32) -> i32:
    return secret
fn secret(x: i32) -> i32:
    return x
";
        let main = "\
use lib
use lib.id
fn f() -> i32:
    let a: fn(i32) -> i32 = lib.inc
    let b: fn(u8) -> u8 = id
    return lib.hidden()(1) + lib.inc(2) + a(3)
";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        let module = lower(&mut files);
        let table = module.table.unwrap().funcs;
        let names: Vec<_> = table
            .iter()
            .map(|id| module.funcs[id.0 as usize].name.as_str())
            .collect();
        // Used modules are lowered first.
        assert_eq!(names, ["secret", "inc", "id(u8)"]);

        // Function types belong to no module.
        let main = "use lib\nlet a: lib.fn(i32) = lib.inc\n";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        let message = "main \"fn\": expected type name, found `fn`";
        assert_eq!(errors(&mut files), [message]);

        let main = "use lib\nfn f():\n    let a = lib.secret\n";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        assert_eq!(errors(&mut files), ["main \"secret\": `secret` is private"]);
    }

    #[test]
    fn modules_are_not_values() {
        let mut files = Memory(vec![
            (
                "main",
                "use a\nfn f():\n    let x = a\n    a()\n    a = 1\n",
            ),
            ("a", ""),
        ]);
        assert_eq!(
            type_errors(&mut files),
            [
                TypeErrorKind::NotAValue("a".to_string()),
                TypeErrorKind::NotCallable("a".to_string()),
                TypeErrorKind::NotAssignable,
            ]
        );
    }

    #[test]
    fn used_names_collide_with_items_but_locals_shadow_them() {
        let mut files = Memory(vec![
            (
                "main",
                "use a as b\nuse a.g\nfn b():\n    pass\nlet g = 1\nfn f(b: i32, g: i32) -> i32:\n    return b + g\n",
            ),
            ("a", "pub fn g():\n    pass\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"b\": `b` is already defined",
                "main \"g\": `g` is already defined",
            ]
        );
    }

    #[test]
    fn only_the_entry_module_exports() {
        let mut files = Memory(vec![
            (
                "main",
                "use a\nuse a.h\npub fn f():\n    a.g()\npub let x = a.y\nfn hidden():\n    pass\npub fn(T) id(x: T) -> T:\n    return x\n",
            ),
            (
                "a",
                "pub use b.k\npub fn g():\n    pass\npub fn h():\n    pass\npub let y = 1\npub let memory = 2\n",
            ),
            ("b", "pub fn k():\n    pass\n"),
        ]);
        let module = lower(&mut files);
        assert_eq!(exports(&module), ["f", "x"]);
    }

    #[test]
    fn the_entry_module_exports_what_it_uses_as_pub() {
        // Each function and global, as each name it is given, whichever
        // module defines it. No module, type, generic function or import is.
        let mut files = Memory(vec![
            (
                "main",
                "use a.h\npub use a.{g, g as again, y, v as w, pos, P, id, ext}\npub use a as lib\npub use main.hidden as shown\npub fn f():\n    pass\nfn hidden():\n    pass\n",
            ),
            (
                "a",
                "extern:\n    pub fn ext()\npub struct P:\n    x: i32\npub fn g():\n    pass\npub fn h():\n    pass\npub let y = 1\npub var v = 2\npub let pos = (0, 1.5)\nlet z = 3\npub fn(T) id(x: T) -> T:\n    return x\n",
            ),
        ]);
        let module = lower(&mut files);
        assert_eq!(
            exports(&module),
            ["g", "again", "f", "shown", "y", "w", "pos.0", "pos.1"]
        );
        // A `let` that only another module uses is no wasm global.
        let globals: Vec<_> = module.globals.iter().map(|g| g.name.as_str()).collect();
        assert_eq!(globals, ["y", "v", "pos.0", "pos.1"]);
    }

    #[test]
    fn a_use_exports_nothing_as_the_memory_is_named() {
        // The module of a library exports its memory by that name, so what
        // a `pub use` binds as it is only a name. A module is no export.
        let mut files = Memory(vec![
            (
                "main",
                "pub use a.g as memory\npub use a.g as other\npub use a.table\n",
            ),
            ("a", "pub fn g():\n    pass\n"),
            ("a.table", "pub let one = 1\n"),
        ]);
        assert_eq!(exports(&lower(&mut files)), ["other"]);
    }

    #[test]
    fn private_fields_are_unreachable_from_other_modules() {
        let mut files = Memory(vec![
            (
                "main",
                "use a\nuse a.P\nfn f(p: a.P, q: &P):\n    let x = p.x + p.y\n    q.x = 1\n    let r = P(x: 1, y: 2)\n",
            ),
            (
                "a",
                "pub struct P:\n    x: i32\n    pub y: i32\npub fn new() -> P:\n    let p = P(x: 1, y: 2)\n    return P(x: p.x, y: 2)\n",
            ),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"x\": field `x` of `P` is private",
                "main \"x\": field `x` of `P` is private",
                "main \"P(x: 1, y: 2)\": field `x` of `P` is private",
            ]
        );
    }

    #[test]
    fn private_fields_with_defaults_are_constructed_from_other_modules() {
        let lib = "pub struct Counter:\n    pub step: i32 = 1\n    count: i32 = 5\npub struct Sealed:\n    pub open: i32\n    key: i32\n    pad: i32 = 0\npub fn new() -> Counter:\n    return Counter(count: 3)\n";
        let main = "use a\npub fn f() -> a.Counter:\n    return a.Counter(step: 2)\n";
        let mut files = Memory(vec![("main", main), ("a", lib)]);
        let module = lower(&mut files);
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        let ir::Stmt::Return(values) = &f.body[0] else {
            panic!("{:?}", f.body)
        };
        let consts = [2, 5].map(|x| ir::Expr::Const(Const::I32(x)));
        assert_eq!(values, &consts);

        // A default can't be replaced where its field can't be named, and a
        // private field without one still seals its struct.
        let main = "use a\nfn f():\n    let c = a.Counter(count: 1)\n    let s = a.Sealed(open: 1, key: 2, pad: 3)\n";
        let mut files = Memory(vec![("main", main), ("a", lib)]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"count\": field `count` of `Counter` is private",
                "main \"a.Sealed(open: 1, key: 2, pad: 3)\": field `key` of `Sealed` is private",
            ]
        );
    }

    #[test]
    fn used_fields_are_private_to_the_module_that_uses_them() {
        let a = "let BASE = 3\nstruct Hidden:\n    x: i32\npub struct Point:\n    pub x: f32\n    secret: i32 = BASE\npub struct Sealed:\n    pub open: i32\n    key: &Hidden\npub enum(u8) Level:\n    low = BASE as u8\n    high\n";
        let b = "use a\nlet BASE = 9\npub struct P3:\n    use a.Point\n    pub z: f32\npub enum(u8) More:\n    use a.Level\n    none\npub fn secrets() -> tuple(i32, i32):\n    return (P3(x: 1.0, z: 2.0).secret, P3(x: 1.0, secret: BASE, z: 2.0).secret)\n";
        let main = "use b\npub fn f() -> tuple(u8, u8, f32):\n    return (b.More.low as u8, b.More.high as u8, b.P3(x: 1.0, z: 2.0).z)\n";
        let mut files = Memory(vec![("main", main), ("a", a), ("b", b)]);
        let module = lower(&mut files);
        let returned = |name: &str| {
            let func = module.funcs.iter().find(|f| f.name == name).unwrap();
            match &func.body[..] {
                [ir::Stmt::Return(values)] => values.clone(),
                body => panic!("{body:?}"),
            }
        };
        let consts = |xs: [i32; 2]| xs.map(|x| ir::Expr::Const(Const::I32(x))).to_vec();
        // A default and a member's value are folded where they are declared,
        // with the private `BASE` of that module.
        assert_eq!(returned("secrets"), consts([3, 9]));
        assert_eq!(returned("f")[..2], consts([3, 4]));

        // A field that was private where it was declared is private to the
        // module that uses it, and to no other.
        let main = "use b\nfn f() -> i32:\n    let p = b.P3(x: 1.0, secret: 1, z: 2.0)\n    return p.secret\n";
        let mut files = Memory(vec![("main", main), ("a", a), ("b", b)]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"secret\": field `secret` of `P3` is private",
                "main \"secret\": field `secret` of `P3` is private",
            ]
        );

        // A module can name the type of every field it has.
        let main = "use a\nstruct S:\n    use a.Sealed\nstruct T:\n    use a.Hidden\n";
        let mut files = Memory(vec![("main", main), ("a", a)]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"a.Sealed\": `use` of `key`, whose type holds the private `Hidden`",
                "main \"Hidden\": `Hidden` is private",
            ]
        );
    }

    #[test]
    fn a_union_that_uses_a_variant_it_cannot_name_is_widened_to() {
        // The variant holds nothing where it is used, so the wider union
        // lacks the leaf that the narrower one has for it.
        let lib = "\
struct Hidden:
    x: i32
pub union Read:
    closed
    at: &Hidden
";
        let main = "\
use lib
union Io:
    use lib.Read
    denied
fn f(r: lib.Read) -> Io:
    return r as Io
";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        assert_eq!(
            errors(&mut files),
            [
                "lib \"&Hidden\": private type `Hidden` in the type of `pub` item `at`",
                "main \"lib.Read\": `use` of `at`, whose type holds the private `Hidden`",
            ]
        );
    }

    #[test]
    fn parameter_defaults_are_folded_where_they_are_declared() {
        let lib = "let STEP = 4\nfn twice(x: i32) -> i32:\n    return x * 2\npub fn step(n: i32, by: i32 = STEP, with: fn(i32) -> i32 = twice) -> i32:\n    return with(n) + by\n";
        let main = "use a\nuse a.{step as advance}\nlet STEP = 9\npub fn f() -> i32:\n    return advance(1) + a.step(2, by: STEP)\n";
        let mut files = Memory(vec![("main", main), ("a", lib)]);
        let module = lower(&mut files);
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        let ir::Stmt::Return(values) = &f.body[0] else {
            panic!("{:?}", f.body)
        };
        let ir::Expr::Binary(_, _, first, second) = &values[0] else {
            panic!("{values:?}")
        };
        let args = |call: &ir::Expr| match call {
            ir::Expr::Call(_, args) => args.clone(),
            other => panic!("{other:?}"),
        };
        let consts = |xs: [i32; 3]| xs.map(|x| ir::Expr::Const(Const::I32(x))).to_vec();
        // The private `STEP` and `twice` of the module that declares `step`.
        assert_eq!(args(first), consts([1, 4, 1]));
        assert_eq!(args(second), consts([2, 9, 1]));
    }

    #[test]
    fn private_types_cannot_be_in_pub_signatures() {
        let mut files = Memory(vec![(
            "main",
            "struct S:\n    x: i32\nenum(u8) E:\n    A\npub struct T:\n    pub s: array(S)\n    t: S\npub fn f(s: &S) -> E:\n    return E.A\nfn g(s: S):\n    pass\npub let e = E.A\nextern:\n    pub fn h(s: tuple(E, i32))\n",
        )]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"array(S)\": private type `S` in the type of `pub` item `s`",
                "main \"tuple(E, i32)\": private type `E` in the type of `pub` item `h`",
                "main \"&S\": private type `S` in the type of `pub` item `f`",
                "main \"E\": private type `E` in the type of `pub` item `f`",
                "main \"e\": private type `E` in the type of `pub` item `e`",
            ]
        );
    }

    #[test]
    fn pub_extern_fns_are_callable_from_other_modules() {
        let mut files = Memory(vec![
            (
                "main",
                "use host\nuse host.log\nfn f():\n    host.log(1)\n    log(2)\n    host.secret()\n",
            ),
            ("host", "extern:\n    pub fn log(n: i32)\n    fn secret()\n"),
        ]);
        assert_eq!(errors(&mut files), ["main \"secret\": `secret` is private"]);
    }

    #[test]
    fn generic_instances_resolve_names_where_they_are_declared() {
        let a = "fn helper() -> i32:\n    return 2\npub fn(T) twice(x: T) -> i32:\n    return helper()\n";
        let mains = [
            "use a\nfn helper() -> i32:\n    return 0\nfn f() -> i32:\n    return a.twice(1) + helper()\n",
            "use a.twice\nfn helper() -> i32:\n    return 0\nfn f() -> i32:\n    return twice(1) + helper()\n",
        ];
        for main in mains {
            let mut files = Memory(vec![("main", main), ("a", a)]);
            let module = lower(&mut files);
            let instance = module
                .funcs
                .iter()
                .find(|f| f.name == "twice(i32)")
                .unwrap();
            let ir::Stmt::Return(values) = &instance.body[0] else {
                panic!("{:?}", instance.body)
            };
            let [ir::Expr::Call(id, _)] = &values[..] else {
                panic!("{values:?}")
            };
            let callee = &module.funcs[id.0 as usize - module.imports.len()];
            let ir::Stmt::Return(values) = &callee.body[0] else {
                panic!()
            };
            assert_eq!(values, &[ir::Expr::Const(Const::I32(2))]);
        }
    }

    /// What the function `name` of `module` returns, which is the last
    /// that it does.
    fn returned(module: &ir::Module, name: &str) -> Vec<ir::Expr> {
        let func = module.funcs.iter().find(|f| f.name == name).unwrap();
        match &func.body[..] {
            [.., ir::Stmt::Return(values)] => values.clone(),
            body => panic!("{body:?}"),
        }
    }

    #[test]
    fn an_included_file_is_an_array_of_its_bytes() {
        let mut files = Memory(vec![
            (
                "main",
                "fn f() -> array(u8):\n    return module.include(\"assets/logo.bin\")\n",
            ),
            ("#assets/logo.bin", "\u{1}duck"),
        ]);
        let module = lower(&mut files);
        let data = ir::Data {
            offset: 0,
            bytes: b"\x01duck".to_vec(),
        };
        assert_eq!(module.data, [data]);
        let consts = [0, 5].map(|x| ir::Expr::Const(Const::I32(x)));
        assert_eq!(returned(&module, "f"), consts);
    }

    #[test]
    fn an_include_is_a_literal_wherever_one_is() {
        let main = "\
let logo = module.include(\"logo.bin\")
let seed: varray(u8) = module.include(path: \"logo.bin\")
pub let len = logo.len
fn f(tail: array(u8) = module.include(\"logo.bin\")) -> array(u8):
    seed[0] = 7
    return logo
fn g() -> array(array(u8)):
    return [module.include(\"logo.bin\"), \"duck\"]
";
        let mut files = Memory(vec![("main", main), ("#logo.bin", "duck")]);
        let module = lower(&mut files);
        // Each global has its own, as it has of any literal, and so has the
        // default. Those that functions only read are one, which the string
        // that holds the same shares.
        let placed: Vec<_> = module.data.iter().map(|data| data.offset).collect();
        assert_eq!(placed, [0, 4, 8, 12, 16]);
        assert!(module.data[..4].iter().all(|data| data.bytes == b"duck"));
        let shared = [12, 0, 0, 0, 4, 0, 0, 0].repeat(2);
        assert_eq!(module.data[4].bytes, shared);
        assert_eq!(module.globals[0].init, Const::I32(4));
        let consts = [0, 4].map(|x| ir::Expr::Const(Const::I32(x)));
        assert_eq!(returned(&module, "f")[..], consts);

        // One that is written to is a global's.
        let main = "fn f():\n    let seed: varray(u8) = module.include(\"logo.bin\")\n";
        let mut files = Memory(vec![("main", main), ("#logo.bin", "duck")]);
        assert_eq!(type_errors(&mut files), [TypeErrorKind::WritableFnLiteral]);

        // A file that is empty is an array that is.
        let main = "pub let len = module.include(\"empty\").len\n";
        let mut files = Memory(vec![("main", main), ("#empty", "")]);
        let module = lower(&mut files);
        assert_eq!(module.globals[0].init, Const::I32(0));
        assert_eq!(module.data, []);
    }

    #[test]
    fn a_constant_reads_what_is_included() {
        let main = "\
fn sum(bytes: array(u8)) -> i32:
    var total = 0
    for byte in bytes:
        total += byte as i32
    return total
pub let total = sum(module.include(\"table.bin\"))
";
        let mut files = Memory(vec![("main", main), ("#table.bin", "\u{1}\u{2}\u{3}")]);
        let module = lower(&mut files);
        assert_eq!(module.globals[0].init, Const::I32(6));
    }

    #[test]
    fn an_include_that_includes_nothing_is_an_error_at_its_path() {
        let main = "\
use lib
let name = \"logo.bin\"
let a = module.include(\"missing.bin\")
let b = module.include(name)
let c = module.include(\"../secret\")
let d = module.include(\"/etc/passwd\")
let e = module.include(\"assets\\\\logo.bin\")
let f = module.include(\"assets//logo.bin\")
let g = module.include(\"./logo.bin\")
let h = module.include(\"assets/\")
let i = module.include(\"\")
let j = module.include()
let k = module.include
let l = module.include(\"other.bin\", \"other.bin\")
let m = module.include(file: \"logo.bin\")
";
        let mut files = Memory(vec![
            ("main", main),
            ("lib", "pub let a = module.include(\"missing.bin\")\n"),
            ("#logo.bin", "duck"),
        ]);
        let outside = |path: &str| {
            format!(
                "main {path:?}: cannot include `{}`: a path is the names from the directory of \
                 `Duck.toml` down to a file of the package, with a `/` between them",
                &path[1..path.len() - 1]
            )
        };
        assert_eq!(
            errors(&mut files),
            [
                "lib \"\\\"missing.bin\\\"\": cannot include `missing.bin`: no such file".to_string(),
                "main \"\\\"missing.bin\\\"\": cannot include `missing.bin`: no such file".to_string(),
                "main \"name\": `module.include` takes a string literal for its path".to_string(),
                outside("\"../secret\""),
                outside("\"/etc/passwd\""),
                "main \"\\\"assets\\\\\\\\logo.bin\\\"\": cannot include `assets\\logo.bin`: a path is \
                 the names from the directory of `Duck.toml` down to a file of the package, with \
                 a `/` between them"
                    .to_string(),
                outside("\"assets//logo.bin\""),
                outside("\"./logo.bin\""),
                outside("\"assets/\""),
                outside("\"\""),
                "main \"module.include()\": missing argument `path`".to_string(),
                "main \"include\": `module.include` is not a value".to_string(),
                // What is wrong with a call is all that is wrong with one.
                "main \"\\\"other.bin\\\"\": expected 1 arguments, found 2".to_string(),
                "main \"\\\"logo.bin\\\"\": no parameter named `file`".to_string(),
                "main \"module.include(file: \\\"logo.bin\\\")\": missing argument `path`".to_string(),
            ]
        );
        let codes: Vec<_> = compile(&mut files)
            .unwrap_err()
            .iter()
            .map(Error::code)
            .collect();
        assert_eq!(
            codes[1..4],
            [
                "include-not-found",
                "include-not-literal",
                "include-outside-package"
            ]
        );
    }
}

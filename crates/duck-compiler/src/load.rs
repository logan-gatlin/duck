//! Gathers a program from its entry point and every module it uses.
//!
//! Every file is a module, named by its path from the root of its package:
//! `util/strings.duck` is `util.strings`. Its items are kept apart from those
//! of other modules, which it reaches through the names `use` gives them.

use std::collections::HashSet;
use std::fmt;

use crate::Error;
use crate::file::{FileId, FileManager};
use crate::lex::{self, Span, Token};
use crate::parse::{self, Ident, Item, ItemKind, UsePath};

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
}

/// The items of every module of a program, and the names modules give what
/// they use.
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    /// Every module's items, each module's after those of every module it
    /// uses that doesn't use it in turn.
    pub items: Vec<Item>,
    /// Each after every `use` of the module it leads into, unless that
    /// module uses this one in turn.
    pub uses: Vec<Use>,
    /// The module whose `pub` items the program exports.
    pub entry: FileId,
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
}

struct Loader<'f, F> {
    files: &'f mut F,
    /// Whether what lexes and parses of a file with errors is loaded.
    partial: bool,
    /// The modules loaded or being loaded, which are not loaded again.
    seen: HashSet<FileId>,
    items: Vec<Item>,
    uses: Vec<Use>,
    errors: Vec<Error>,
}

/// The most lines with an error that are blanked for the rest of a file to
/// lex.
const MAX_BLANKED_LINES: usize = 16;

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
        Self {
            items: module.items,
            uses: Vec::new(),
            entry,
        }
    }
}

/// Lexes and parses the entry point of `files` and every module it uses,
/// recursively.
///
/// Each module is loaded once, however many modules use it, and modules may
/// use one another. Errors in one file don't stop the others from loading,
/// but the uses of a file that fails to lex or parse are not followed.
pub fn load(files: &mut impl FileManager) -> Result<Program, Vec<Error>> {
    match Loader::run(files, false) {
        (program, errors) if errors.is_empty() => Ok(program),
        (_, errors) => Err(errors),
    }
}

/// Loads as [`load`] does, and gives what loaded of a program with errors
/// along with them, for a caller that asks about what is there: of a file
/// with errors, the lines without one, whose uses are followed.
pub fn load_partial(files: &mut impl FileManager) -> (Program, Vec<Error>) {
    Loader::run(files, true)
}

impl<'f, F: FileManager> Loader<'f, F> {
    fn run(files: &'f mut F, partial: bool) -> (Program, Vec<Error>) {
        let entry = files.entry_point();
        let mut loader = Self {
            files,
            partial,
            seen: HashSet::new(),
            items: Vec::new(),
            uses: Vec::new(),
            errors: Vec::new(),
        };
        loader.seen.insert(entry);
        loader.items_of(entry);
        let program = Program {
            items: loader.items,
            uses: loader.uses,
            entry,
        };
        (program, loader.errors)
    }

    fn items_of(&mut self, id: FileId) {
        let src = self.files.contents(id);
        let lexed = self.errors.len();
        let Some(tokens) = self.tokens_of(id, src) else {
            return;
        };
        let (module, errors) = parse::parse_partial(&tokens);
        let failed = !errors.is_empty();
        // What is left of a file that doesn't lex may not parse for what
        // was taken from it.
        if self.errors.len() == lexed {
            self.errors.extend(errors.into_iter().map(Error::Parse));
        }
        if failed && !self.partial {
            return;
        }
        // Uses come first, so the modules they load precede these items,
        // but for one that is being loaded: it uses this module in turn.
        for item in module.items {
            match &item.kind {
                ItemKind::Use(decl) => {
                    for path in &decl.paths {
                        if let Err(kind) = self.use_path(id, item.is_pub, path) {
                            let span = path_span(path);
                            self.errors.push(Error::Use(UseError { kind, span }));
                        }
                    }
                }
                _ => self.items.push(item),
            }
        }
    }

    /// The tokens of `src`, the contents of file `id`. For one that doesn't
    /// lex they are those of what is left once each line with an error is
    /// blanked, if what loads of a file is wanted.
    fn tokens_of(&mut self, id: FileId, mut src: String) -> Option<Vec<Token>> {
        let mut error = match lex::tokenize(id, &src) {
            Ok(tokens) => return Some(tokens),
            Err(error) => error,
        };
        self.errors.push(Error::Lex(error.clone()));
        for _ in 0..MAX_BLANKED_LINES {
            if !self.partial || !blank_line(&mut src, error.span.start) {
                break;
            }
            error = match lex::tokenize(id, &src) {
                Ok(tokens) => return Some(tokens),
                Err(error) => error,
            };
        }
        None
    }

    /// Loads the module `path` leads into, and gives what it names its name
    /// in the module `from`.
    fn use_path(&mut self, from: FileId, is_pub: bool, path: &UsePath) -> Result<(), UseErrorKind> {
        let names: Vec<_> = path.segments.iter().map(|s| s.name.as_str()).collect();
        // The module is the file furthest along the path, and the names
        // after it are found by the type checker.
        let local = (1..=names.len())
            .rev()
            .find_map(|len| Some((self.files.open(from, &names[..len])?, len)));
        let dependency = self.files.open_package(from, names[0]);
        let (target, len) = match (local, dependency) {
            (Some(_), Some(_)) => return Err(UseErrorKind::Ambiguous(names[0].to_string())),
            (Some(local), None) => local,
            // Only what its library makes `pub` is reached in a dependency.
            (None, Some(library)) => (library, 1),
            (None, None) => return Err(UseErrorKind::NotFound(names.join("."))),
        };
        if self.seen.insert(target) {
            self.items_of(target);
        }
        let name = path.alias.as_ref().or(path.segments.last()).unwrap();
        self.uses.push(Use {
            module: from,
            name: name.clone(),
            target,
            target_path: names[..len].join("."),
            path: path.segments[..len].to_vec(),
            members: path.segments[len..].to_vec(),
            is_pub,
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
    use crate::file::Settings;
    use crate::ir::{self, Const};
    use crate::lex::TokenKind;
    use crate::parse::{ParseErrorKind, PatternKind};
    use crate::ty::{self, TypeErrorKind};

    /// Files named by the paths that use them; the first is the entry
    /// point. A file named `@name` is the library of dependency `name`.
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
        let funcs = module.funcs.iter().filter_map(|f| f.export.as_deref());
        let globals = module.globals.iter().filter_map(|g| g.export.as_deref());
        funcs.chain(globals).collect()
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
    let a = lib.inc
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
                "use a\npub use a.h\npub fn f():\n    a.g()\npub let x = a.y\nfn hidden():\n    pass\npub fn(T) id(x: T) -> T:\n    return x\n",
            ),
            (
                "a",
                "pub fn g():\n    pass\npub fn h():\n    pass\npub let y = 1\npub let memory = 2\n",
            ),
        ]);
        let module = lower(&mut files);
        assert_eq!(exports(&module), ["f", "x"]);
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
}

//! Gathers a program from its entry point and every module it imports.
//!
//! Every file is a module. Its items are kept apart from those of other
//! modules, which it reaches through the names it imports them by.

use std::collections::HashMap;
use std::fmt;
use std::path::Path;

use crate::Error;
use crate::file::{FileId, FileManager, OpenError};
use crate::lex::{self, Span};
use crate::parse::{self, Ident, ImportTarget, Item, ItemKind};

#[derive(Debug, Clone, PartialEq)]
pub struct ImportError {
    pub kind: ImportErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImportErrorKind {
    /// No file was found at the path.
    NotFound(String),
    /// A path to a file of another package.
    OutsidePackage(String),
    /// The importing package has no dependency by this name.
    NoDependency(String),
    /// A module that imports itself, through the modules named in order,
    /// starting and ending with itself.
    Cycle(Vec<String>),
    /// A file whose stem isn't a name, imported without `as`.
    Unnamed(String),
}

/// The items of every module of a program, and the names modules give the
/// modules they import.
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    /// Every module's items, each module's after those of every module it
    /// imports, which is the order globals are initialized in.
    pub items: Vec<Item>,
    pub imports: Vec<Import>,
    /// The module whose `pub` items the program exports.
    pub entry: FileId,
}

/// A module that `module` imports, by the name it gives it.
#[derive(Debug, Clone, PartialEq)]
pub struct Import {
    pub module: FileId,
    pub name: Ident,
    pub target: FileId,
    /// Whether modules importing `module` can reach `target` through it.
    pub is_pub: bool,
}

/// How far a module has been loaded.
#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    /// Loading it or a module it imports.
    Loading,
    Loaded,
}

struct Loader<'f, F> {
    files: &'f mut F,
    states: HashMap<FileId, State>,
    /// The modules being loaded, each imported by the one before.
    stack: Vec<FileId>,
    items: Vec<Item>,
    imports: Vec<Import>,
    errors: Vec<Error>,
}

impl fmt::Display for ImportErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFound(path) => write!(f, "cannot find `{path}`"),
            Self::OutsidePackage(path) => write!(
                f,
                "`{path}` is outside this package; import its package by name"
            ),
            Self::NoDependency(name) => write!(f, "no dependency is named `{name}`"),
            Self::Cycle(modules) => write!(f, "import cycle: {}", modules.join(" -> ")),
            Self::Unnamed(path) => write!(
                f,
                "the name of `{path}` is not an identifier; import it `as` one"
            ),
        }
    }
}

impl fmt::Display for ImportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}..{}", self.kind, self.span.start, self.span.end)
    }
}

impl std::error::Error for ImportError {}

impl Program {
    /// A program of one module, which imports nothing.
    pub fn single(entry: FileId, module: parse::Module) -> Self {
        Self {
            items: module.items,
            imports: Vec::new(),
            entry,
        }
    }
}

/// Lexes and parses the entry point of `files` and every module it imports,
/// recursively.
///
/// Each module is loaded once, however many modules import it. Errors in one
/// file don't stop the others from loading, but the imports of a file that
/// fails to lex or parse are not followed.
pub fn load(files: &mut impl FileManager) -> Result<Program, Vec<Error>> {
    let entry = files.entry_point();
    let mut loader = Loader {
        files,
        states: HashMap::new(),
        stack: Vec::new(),
        items: Vec::new(),
        imports: Vec::new(),
        errors: Vec::new(),
    };
    loader.file(entry);
    if loader.errors.is_empty() {
        Ok(Program {
            items: loader.items,
            imports: loader.imports,
            entry,
        })
    } else {
        Err(loader.errors)
    }
}

impl<F: FileManager> Loader<'_, F> {
    fn file(&mut self, id: FileId) {
        self.states.insert(id, State::Loading);
        self.stack.push(id);
        self.items_of(id);
        self.stack.pop();
        self.states.insert(id, State::Loaded);
    }

    fn items_of(&mut self, id: FileId) {
        let src = self.files.contents(id);
        let tokens = match lex::tokenize(id, &src) {
            Ok(tokens) => tokens,
            Err(e) => return self.errors.push(Error::Lex(e)),
        };
        let module = match parse::parse(&tokens) {
            Ok(module) => module,
            Err(errors) => return self.errors.extend(errors.into_iter().map(Error::Parse)),
        };
        // Imports come first, so the modules they load precede these items.
        for item in module.items {
            match &item.kind {
                ItemKind::Import(import) => {
                    if let Err(kind) = self.import(id, &item, import) {
                        let span = item.span;
                        self.errors.push(Error::Import(ImportError { kind, span }));
                    }
                }
                _ => self.items.push(item),
            }
        }
    }

    fn import(
        &mut self,
        from: FileId,
        item: &Item,
        import: &parse::Import,
    ) -> Result<(), ImportErrorKind> {
        let (target, name) = match &import.target {
            ImportTarget::File(path) => {
                let target = self.files.open(from, path).map_err(|e| match e {
                    OpenError::NotFound => ImportErrorKind::NotFound(path.clone()),
                    OpenError::OutsidePackage => ImportErrorKind::OutsidePackage(path.clone()),
                })?;
                let stem = Path::new(path).file_stem().and_then(|stem| stem.to_str());
                let name = stem
                    .filter(|stem| lex::is_identifier(stem))
                    .map(|stem| Ident {
                        name: stem.to_string(),
                        span: item.span,
                    });
                (
                    target,
                    name.ok_or_else(|| ImportErrorKind::Unnamed(path.clone())),
                )
            }
            ImportTarget::Package(name) => {
                let target = self.files.open_package(from, &name.name);
                let target =
                    target.ok_or_else(|| ImportErrorKind::NoDependency(name.name.clone()))?;
                (target, Ok(name.clone()))
            }
        };
        let name = match &import.alias {
            Some(alias) => alias.clone(),
            None => name?,
        };
        match self.states.get(&target) {
            None => self.file(target),
            Some(State::Loaded) => {}
            Some(State::Loading) => {
                let start = self.stack.iter().position(|id| *id == target).unwrap();
                let cycle = self.stack[start..].iter().chain([&target]);
                let names = cycle.map(|id| self.files.display_name(*id)).collect();
                return Err(ImportErrorKind::Cycle(names));
            }
        }
        self.imports.push(Import {
            module: from,
            name,
            target,
            is_pub: item.is_pub,
        });
        Ok(())
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

    /// Files named by the paths that import them; the first is the entry
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

        fn open(&mut self, _from: FileId, path: &str) -> Result<FileId, OpenError> {
            let index = self.0.iter().position(|f| f.0 == path);
            Ok(Self::mint_file_id(index.ok_or(OpenError::NotFound)?))
        }

        fn open_package(&mut self, from: FileId, name: &str) -> Option<FileId> {
            self.open(from, &format!("@{name}")).ok()
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
    fn modules_follow_the_modules_they_import() {
        let mut files = Memory(vec![
            ("main", "import \"b\"\nimport \"e\"\nlet a = 1\nlet d = 4\n"),
            ("b", "import \"c\"\nlet b = 2\n"),
            ("c", "let c = 3\n"),
            ("e", "fn e():\n    pass\n"),
        ]);
        assert_eq!(items(&mut files), ["c c", "b b", "e e", "a main", "d main"]);
        let program = load(&mut files).unwrap();
        assert_eq!(program.items[0].span.file, files.id("c"));
        assert_eq!(files.text(program.items[0].span), "let c = 3");
    }

    #[test]
    fn a_module_imported_twice_is_loaded_once() {
        let mut files = Memory(vec![
            ("main", "import \"a\"\nimport \"b\"\nlet m = 0\n"),
            ("a", "let a = 1\n"),
            ("b", "import \"a\"\nlet b = 2\n"),
        ]);
        assert_eq!(items(&mut files), ["a a", "b b", "m main"]);
    }

    #[test]
    fn globals_are_initialized_after_those_they_import() {
        let mut files = Memory(vec![
            ("main", "import \"b\"\npub let c = b.b + 1\n"),
            ("b", "import \"a\"\npub let b = a.a + 1\n"),
            ("a", "pub let a = 1\n"),
        ]);
        let module = lower(&mut files);
        let inits: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        // Only the entry module's are exported, so only they are wasm globals.
        assert_eq!(inits, [Const::I32(3)]);
    }

    #[test]
    fn import_cycles_are_errors_at_the_import_that_closes_them() {
        let mut files = Memory(vec![
            ("main", "import \"a\"\n"),
            ("a", "import \"b\"\n"),
            ("b", "import \"main\"\nimport \"b\"\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "b \"import \\\"main\\\"\": import cycle: main -> a -> b -> main",
                "b \"import \\\"b\\\"\": import cycle: b -> b",
            ]
        );
    }

    #[test]
    fn missing_files() {
        let mut files = Memory(vec![("main", "import \"nope\"\nlet a = 1\n")]);
        assert_eq!(
            errors(&mut files),
            ["main \"import \\\"nope\\\"\": cannot find `nope`"]
        );
        let mut files = Memory(vec![("main", "import nope\n")]);
        assert_eq!(
            errors(&mut files),
            ["main \"import nope\": no dependency is named `nope`"]
        );
    }

    #[test]
    fn modules_are_named_by_their_stem_unless_renamed() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"util/strings.duck\"\nimport \"my-file.duck\" as other\nimport json as j\nlet x = strings.a + other.b + j.c\n",
            ),
            ("util/strings.duck", "pub let a = 1\n"),
            ("my-file.duck", "pub let b = 2\n"),
            ("@json", "pub let c = 3\n"),
        ]);
        lower(&mut files);

        let mut files = Memory(vec![
            ("main", "import \"my-file.duck\"\nimport \"fn.duck\"\n"),
            ("my-file.duck", ""),
            ("fn.duck", ""),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"import \\\"my-file.duck\\\"\": the name of `my-file.duck` is not an identifier; import it `as` one",
                "main \"import \\\"fn.duck\\\"\": the name of `fn.duck` is not an identifier; import it `as` one",
            ]
        );
    }

    #[test]
    fn errors_point_into_the_file_they_are_in() {
        let mut files = Memory(vec![
            ("main", "import \"a\"\nimport \"b\"\nlet x = 1\n"),
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
            ("main", "import \"a\"\nlet x = 1\nlet x = 2\n"),
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
    fn import_syntax() {
        let mut files = Memory(vec![
            ("main", "import \"a\" as\nfn f():\n    import \"a\"\n"),
            ("a", ""),
        ]);
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
                    found: TokenKind::Import,
                },
            ]
        );
    }

    #[test]
    fn items_of_other_modules_are_reached_through_their_name() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"geo\"\nfn f() -> f32:\n    let p = geo.Point(x: 1.0, y: geo.origin.y)\n    return geo.len(p) + geo.unit.x\n",
            ),
            (
                "geo",
                "pub struct Point:\n    pub x: f32\n    pub y: f32\npub let origin = Point(x: 0.0, y: 0.0)\npub var unit = Point(x: 1.0, y: 1.0)\npub fn len(p: Point) -> f32:\n    return p.x + p.y\n",
            ),
        ]);
        lower(&mut files);
    }

    #[test]
    fn names_are_local_to_their_module() {
        let mut files = Memory(vec![
            ("main", "import \"a\"\nlet x = 1\nfn f():\n    g()\n"),
            ("a", "let x = 2\nfn g():\n    pass\n"),
        ]);
        assert_eq!(
            type_errors(&mut files),
            [TypeErrorKind::UnknownName("g".to_string())]
        );
    }

    #[test]
    fn private_items_are_unreachable_from_other_modules() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"a\"\nfn f():\n    a.g()\n    let x = a.x\n    let p: a.P = a.p\n    a.nope()\n",
            ),
            (
                "a",
                "let x = 2\nfn g():\n    pass\nstruct P:\n    pub y: i32\npub let p = 0\n",
            ),
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
    fn pub_imports_are_reachable_through_the_importing_module() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"lib\"\nlet x: lib.value.Value = lib.value.Value(n: lib.value.one)\nlet y = lib.inner.one\n",
            ),
            ("lib", "pub import \"value\"\nimport \"value\" as inner\n"),
            (
                "value",
                "pub struct Value:\n    pub n: i32\npub let one = 1\n",
            ),
        ]);
        assert_eq!(errors(&mut files), ["main \"inner\": `inner` is private"]);
    }

    #[test]
    fn qualified_generics_and_enums() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"lib\"\nfn f() -> i32:\n    let b: lib.Box(lib.Color) = lib.Box(lib.Color)(v: lib.Color.Red)\n    let size = lib.Box(i64).size\n    var n = lib.id(b.v) as i32\n    for c in lib.Color:\n        n += c as i32\n    return n + lib.id(i32)(size as i32)\n",
            ),
            (
                "lib",
                "pub struct(T) Box:\n    pub v: T\npub enum(u8) Color:\n    Red\n    Green\npub fn(T) id(x: T) -> T:\n    return x\n",
            ),
        ]);
        lower(&mut files);
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
import \"lib\"
fn f() -> i32:
    let a = lib.inc
    let b: fn(u8) -> u8 = lib.id
    return lib.hidden()(1) + lib.inc(2) + a(3)
";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        let module = lower(&mut files);
        let table = module.table.unwrap().funcs;
        let names: Vec<_> = table
            .iter()
            .map(|id| module.funcs[id.0 as usize].name.as_str())
            .collect();
        // Imported modules are lowered first.
        assert_eq!(names, ["secret", "inc", "id(u8)"]);

        // Function types belong to no module.
        let main = "import \"lib\"\nlet a: lib.fn(i32) = lib.inc\n";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        let message = "main \"fn\": expected type name, found `fn`";
        assert_eq!(errors(&mut files), [message]);

        let main = "import \"lib\"\nfn f():\n    let a = lib.secret\n";
        let mut files = Memory(vec![("main", main), ("lib", lib)]);
        assert_eq!(errors(&mut files), ["main \"secret\": `secret` is private"]);
    }

    #[test]
    fn modules_are_not_values() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"a\"\nfn f():\n    let x = a\n    a()\n    a = 1\n",
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
    fn import_names_collide_with_items_but_locals_shadow_them() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"a\"\nfn a():\n    pass\nfn f(a: i32) -> i32:\n    return a\n",
            ),
            ("a", ""),
        ]);
        assert_eq!(errors(&mut files), ["main \"a\": `a` is already defined"]);
    }

    #[test]
    fn only_the_entry_module_exports() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"a\"\npub fn f():\n    a.g()\npub let x = a.y\nfn hidden():\n    pass\npub fn(T) id(x: T) -> T:\n    return x\n",
            ),
            (
                "a",
                "pub fn g():\n    pass\npub let y = 1\npub let memory = 2\n",
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
                "import \"a\"\nfn f(p: a.P, q: &a.P):\n    let x = p.x + p.y\n    q.x = 1\n    let r = a.P(x: 1, y: 2)\n",
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
                "main \"a.P(x: 1, y: 2)\": field `x` of `P` is private",
            ]
        );
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
                "import \"host\"\nfn f():\n    host.log(1)\n    host.secret()\n",
            ),
            ("host", "extern:\n    pub fn log(n: i32)\n    fn secret()\n"),
        ]);
        assert_eq!(errors(&mut files), ["main \"secret\": `secret` is private"]);
    }

    #[test]
    fn generic_instances_resolve_names_where_they_are_declared() {
        let mut files = Memory(vec![
            (
                "main",
                "import \"a\"\nfn helper() -> i32:\n    return 0\nfn f() -> i32:\n    return a.twice(1) + helper()\n",
            ),
            (
                "a",
                "fn helper() -> i32:\n    return 2\npub fn(T) twice(x: T) -> i32:\n    return helper()\n",
            ),
        ]);
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

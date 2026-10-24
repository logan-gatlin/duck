//! The tests of a package: each `pub fn` of its test modules that takes
//! nothing, and the module that runs them.
//!
//! A test module is a file of the test directory of the package. It is a
//! module of the package, and sees all of it, `pub` or not, as it sees of a
//! dependency only what any module does. A `pub fn` of one is a test, and
//! any other function of one is a helper.
//!
//! The module of the tests is that of the program with one more function,
//! which is all that it exports: it takes the index of a test, and calls
//! it. A host runs each test in an instance of its own, so each starts with
//! the memory and the globals that the constants of the program left.

use crate::file::{FileId, Settings};
use crate::ir::{self, BinOp, Const, Expr, FuncId, Stmt, ValType};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::ItemKind;
use crate::world::{TEST_EXPORT, World};

use super::{Checker, Ty, TypeError, TypeErrorKind, lower_program};

/// A test: a `pub fn` of a test module, which takes nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Test {
    /// The path of its module from the test directory and then its own
    /// name, with a `.` between them: `util.geo.adds` for `adds` of
    /// `util/geo.duck`.
    pub name: String,
    /// The whole of its declaration, in the file of its module.
    pub span: Span,
}

/// The tests of a program, and what runs them.
#[derive(Debug, Clone)]
pub struct Tested {
    /// The module of the program, which exports the function
    /// [`TEST_EXPORT`]: it calls the test at the index it is given, which
    /// is its place in `tests`, and traps at an index that none has.
    pub module: ir::Module,
    /// Each test, in the order they are run in: the test modules in the
    /// order the program has them, and those of one as they are declared.
    pub tests: Vec<Test>,
    /// The world that `module` is a component of.
    pub world: World,
}

/// Resolves names in, type checks, and lowers a loaded program to the wasm
/// module of its tests, as [`super::check`] lowers it to that of the
/// program: with the same memory and globals, which are as its constants
/// left them, and without what calls its start function.
pub fn check_tests(program: &Program, settings: &Settings) -> Result<Tested, Vec<TypeError>> {
    let (mut ck, imports, funcs, _) = lower_program(program, settings, false, true);
    if !ck.errors.is_empty() {
        return Err(ck.errors);
    }
    let found = std::mem::take(&mut ck.tests);
    let world = ck.world.clone();
    Ok(Tested {
        module: ck.module(imports, funcs, settings),
        tests: found.into_iter().map(|(test, _)| test).collect(),
        world,
    })
}

impl Checker {
    /// Whether the module `module` sees what the module `owner` keeps to
    /// itself: it is that module, or it is a test module of the package
    /// that `owner` is of.
    pub(super) fn sees_private(&self, module: FileId, owner: FileId) -> bool {
        module == owner || self.test_modules.contains(&module) && self.package.contains(&owner)
    }

    /// The tests of `program`, in the order they are run in, each with the
    /// function it is: every `pub fn` of a test module, but for one of a
    /// block of an interface, which is reported as that. Reports one that
    /// is no test, as it takes arguments or type parameters, or returns
    /// something, which `never` is too.
    pub(super) fn find_tests(&mut self, program: &Program) -> Vec<(Test, FuncId)> {
        let mut found = Vec::new();
        let mut next = self.import_count;
        for item in &program.items {
            let ItemKind::Fn(decl) = &item.kind else {
                continue;
            };
            // Only one that isn't generic is a function of the module.
            let id = FuncId(next);
            let generic = decl.sig.is_generic();
            next += u32::from(!generic);
            let tests = program.tests.iter();
            let module = tests
                .enumerate()
                .find(|(_, test)| test.file == item.span.file);
            let Some((order, module)) = module.filter(|_| item.is_pub) else {
                continue;
            };
            if decl.interface.is_some() {
                continue;
            }
            let name = &decl.sig.name;
            let ret = match generic {
                true => Ty::Error,
                false => self.funcs[id.0 as usize].ret,
            };
            let returns = !matches!(ret, Ty::Unit | Ty::Error);
            if generic || !decl.sig.params.is_empty() || returns {
                self.error(TypeErrorKind::InvalidTest(name.name.clone()), name.span);
                continue;
            }
            let test = Test {
                name: format!("{}.{}", module.path.join("."), name.name),
                span: item.span,
            };
            found.push((order, test, id));
        }
        // A module is loaded before one that uses it, wherever it is tested.
        found.sort_by_key(|(order, ..)| *order);
        found.into_iter().map(|(_, test, id)| (test, id)).collect()
    }
}

/// The function that the module of `tests` exports as [`TEST_EXPORT`]: it
/// calls the test whose place in `tests` it is given, and returns once that
/// has. It traps at an index that no test has.
pub(super) fn test_export(tests: &[(Test, FuncId)]) -> ir::Func {
    let index = Expr::Local(ir::LocalId(0));
    let call = |(place, (_, func)): (usize, &(Test, FuncId))| {
        let place = Expr::Const(Const::I32(place as i32));
        let called = Stmt::Call {
            func: *func,
            args: Vec::new(),
            dests: Vec::new(),
        };
        Stmt::If {
            cond: Expr::Binary(
                ValType::I32,
                BinOp::Eq,
                Box::new(index.clone()),
                Box::new(place),
            ),
            then_body: vec![called, Stmt::Return(Vec::new())],
            else_body: Vec::new(),
        }
    };
    let mut body: Vec<_> = tests.iter().enumerate().map(call).collect();
    body.push(Stmt::Unreachable);
    ir::Func {
        name: TEST_EXPORT.to_string(),
        exports: vec![TEST_EXPORT.to_string()],
        params: vec![ValType::I32],
        results: Vec::new(),
        locals: vec![ir::Local {
            name: "index".to_string(),
            ty: ValType::I32,
        }],
        body,
    }
}

#[cfg(test)]
mod tests {
    use crate::file::{FileId, FileManager, Settings, TestModule};
    use crate::world::{COMMAND, REALLOC, RUN_EXPORT, TEST_EXPORT};
    use crate::{Error, Tests, compile, compile_tests, emit, load};

    use super::*;

    /// What allocates for a host that passes a list.
    const ALLOCATOR: &str = "\
var heap: uint = 0
pub fn cabi_realloc(old: &var u8, old_size: uint, align: uint, new_size: uint) -> &var u8:
    if heap == 0:
        heap = module.grow(1) as uint * module.page_size
    heap += new_size
    return (heap - new_size) as! &var u8
";

    /// An entry point and the test modules of its package, each named by
    /// its path from the test directory. Neither uses another file.
    struct Package {
        entry: &'static str,
        tests: Vec<(&'static str, &'static str)>,
        settings: Settings,
    }

    impl FileManager for Package {
        fn entry_point(&mut self) -> FileId {
            Self::mint_file_id(0)
        }

        fn display_name(&mut self, id: FileId) -> String {
            let test = (0..self.tests.len()).find(|test| Self::mint_file_id(test + 1) == id);
            test.map_or("main", |test| self.tests[test].0).to_string()
        }

        fn contents(&mut self, id: FileId) -> String {
            let test = (0..self.tests.len()).find(|test| Self::mint_file_id(test + 1) == id);
            test.map_or(self.entry, |test| self.tests[test].1)
                .to_string()
        }

        fn open(&mut self, _from: FileId, path: &[&str]) -> Option<FileId> {
            (path == ["main"]).then(|| Self::mint_file_id(0))
        }

        fn open_package(&mut self, _from: FileId, _name: &str) -> Option<FileId> {
            None
        }

        fn tests(&mut self) -> Vec<TestModule> {
            let tests = self.tests.iter().enumerate();
            let test = |(index, (name, _)): (usize, &(&str, &str))| TestModule {
                file: Self::mint_file_id(index + 1),
                path: vec![name.to_string()],
            };
            tests.map(test).collect()
        }

        fn settings(&mut self) -> Settings {
            self.settings.clone()
        }
    }

    /// A program, which `duck run` runs by calling `main`.
    fn program(entry: &'static str, tests: Vec<(&'static str, &'static str)>) -> Package {
        let settings = Settings {
            start: Some("main".to_string()),
            world: Some(COMMAND.to_string()),
            ..Settings::default()
        };
        Package {
            entry,
            tests,
            settings,
        }
    }

    /// A library, which has no world.
    fn library(entry: &'static str, tests: Vec<(&'static str, &'static str)>) -> Package {
        Package {
            entry,
            tests,
            settings: Settings::default(),
        }
    }

    fn tested(files: &mut Package) -> Result<Tested, Vec<String>> {
        let program = load::load(files).unwrap();
        let tested = check_tests(&program, &files.settings());
        tested.map_err(|errors| errors.iter().map(|e| e.kind.to_string()).collect())
    }

    /// Each function of `module` that is exported, with what it is exported
    /// as.
    fn exported(module: &ir::Module) -> Vec<(&str, &str)> {
        let funcs = module.funcs.iter();
        let named = funcs.flat_map(|f| f.exports.iter().map(|e| (f.name.as_str(), e.as_str())));
        named.collect()
    }

    #[test]
    fn the_module_of_the_tests_exports_what_calls_them() {
        let checks = "\
use main
pub fn first():
    main.count += 1
fn helper():
    pass
pub fn second():
    todo
";
        let entry = "var count = 0\nlet cells: varray(u8) = [7; 3]\nfn main():\n    count = 9\n";
        let mut files = program(
            entry,
            vec![("checks", checks), ("more", "pub fn third():\n    pass\n")],
        );
        let tested = tested(&mut files).unwrap();
        let names: Vec<_> = tested.tests.iter().map(|test| test.name.as_str()).collect();
        assert_eq!(names, ["checks.first", "checks.second", "more.third"]);
        // Nothing calls the start function, and no host the `run` of a
        // program.
        let module = &tested.module;
        assert_eq!(exported(module), [(TEST_EXPORT, TEST_EXPORT)]);
        assert!(module.funcs.iter().all(|f| f.name != RUN_EXPORT));
        // It starts as the program does: with the memory and the globals
        // that the constants left.
        let built = ty_check(&mut files);
        assert_eq!(
            (&module.data, &module.globals),
            (&built.data, &built.globals)
        );
        assert_eq!(module.memory, built.memory);

        // A test is called where its index is given, and no other is.
        let wat = wasmprinter::print_bytes(emit::emit(module)).unwrap();
        let start = wat.find(&format!("(func ${TEST_EXPORT} ")).unwrap();
        let end = wat[start..].find("\n  )").unwrap();
        let lines: Vec<_> = wat[start..start + end].lines().map(str::trim).collect();
        let calls = |test: usize, name: &str| {
            let index = format!("i32.const {test}");
            let call = format!("call ${name}");
            let at = lines.iter().position(|line| *line == index).unwrap();
            assert_eq!(
                lines[at - 1..at + 6],
                [
                    "local.get $index",
                    &index,
                    "i32.eq",
                    "if ;; label = @1",
                    &call,
                    "return",
                    "end"
                ]
            );
        };
        assert!(lines[0].contains("(param $index i32)"), "{}", lines[0]);
        calls(0, "first");
        calls(1, "second");
        calls(2, "third");
        // An index that no test has traps.
        assert_eq!(lines.last(), Some(&"unreachable"));
    }

    /// The module that is built of `files`, which has no errors.
    fn ty_check(files: &mut Package) -> ir::Module {
        let program = load::load(files).unwrap();
        super::super::check(&program, &files.settings()).unwrap()
    }

    #[test]
    fn the_tests_define_nothing_that_the_world_exports() {
        // A program without its `run`, which nothing is to call.
        let checks = ("checks", "pub fn passes():\n    pass\n");
        let mut files = program("fn idle():\n    pass\n", vec![checks]);
        files.settings.start = None;
        assert!(tested(&mut files).is_ok());
        let built = compile(&mut files).unwrap_err();
        assert!(
            built[0].to_string().contains("nothing defines `run`"),
            "{built:?}"
        );
        // Nor is a start function looked for.
        files.settings.start = Some("missing".to_string());
        assert!(tested(&mut files).is_ok());

        // What a file says of its exports is still what it may say.
        let entry = "fn idle() = \"idle\":\n    pass\n";
        let mut files = program(entry, vec![checks]);
        assert_eq!(
            tested(&mut files).unwrap_err(),
            ["only a function that is exported has a name to be exported as"]
        );
        let block = "pub \"wasi:cli/run@0.3.0\":\n    fn run() -> result(tuple(), tuple()):\n        return .ok(())\n";
        let mut files = program("fn main():\n    pass\n", vec![("checks", block)]);
        assert_eq!(
            tested(&mut files).unwrap_err(),
            ["only the entry file of a component exports an interface"]
        );
    }

    #[test]
    fn what_allocates_for_the_host_is_found_as_it_is_in_a_build() {
        let checks = "\
extern \"wasi:cli/environment@0.3.0\":
    fn get_arguments() -> array(string)
pub fn has_a_name():
    get_arguments().len == 1 or module.unreachable()
";
        let mut files = program("fn main():\n    pass\n", vec![("checks", checks)]);
        let errors = tested(&mut files).unwrap_err();
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].starts_with("the host passes a `list<string>` in memory"),
            "{errors:?}"
        );

        // In the entry file, and in no test module.
        let entry: &str = Box::leak(format!("{ALLOCATOR}fn main():\n    pass\n").into_boxed_str());
        let mut files = program(entry, vec![("checks", checks)]);
        let tested = tested(&mut files).unwrap();
        assert_eq!(
            exported(&tested.module),
            [(REALLOC, REALLOC), (TEST_EXPORT, TEST_EXPORT)]
        );
    }

    #[test]
    fn the_tests_of_a_library_import_what_its_files_name() {
        let entry = "\
extern \"wasi:cli/exit@0.3.0\":
    pub fn exit_with_code(status: u8) -> never
pub let limit = 3
pub fn double(n: i32) -> i32:
    return n * 2
fn pointed() -> fn(i32) -> i32:
    return double
";
        let checks = "\
use main
extern \"wasi:clocks/monotonic-clock@0.3.0\":
    fn now() -> u64
pub fn doubles():
    main.pointed()(main.limit) == 6 or main.exit_with_code(1)
pub fn tells_the_time():
    let _ = now()
";
        let mut files = library(entry, vec![("checks", checks)]);
        let tested = tested(&mut files).unwrap();
        // Nothing is exported by its own name, as it is of a library that
        // is only checked.
        assert_eq!(exported(&tested.module), [(TEST_EXPORT, TEST_EXPORT)]);
        assert!(tested.module.globals.iter().all(|g| g.exports.is_empty()));
        assert_eq!(tested.module.table.as_ref().unwrap().export, None);
        let imports: Vec<_> = tested
            .module
            .imports
            .iter()
            .map(|i| i.module.as_str())
            .collect();
        assert_eq!(
            imports,
            ["wasi:cli/exit@0.3.0", "wasi:clocks/monotonic-clock@0.3.0"]
        );
        let Tests { component, tests } = compile_tests(&mut files).unwrap();
        assert_eq!(tests, tested.tests);
        let wat = wasmprinter::print_bytes(&component).unwrap();
        assert!(
            wat.contains(&format!("(export \"{TEST_EXPORT}\" (func")),
            "{wat}"
        );
        assert!(wat.contains("(import \"wasi:cli/exit@0.3.0\""), "{wat}");
        // A library is still no component to build.
        let built = compile(&mut files).unwrap_err();
        assert_eq!(
            built[0].to_string(),
            "a library is no component: it has no world"
        );

        // An interface that the WIT lacks is named where it is, and what
        // the world itself would give has nothing to say what it is.
        let checks = "\
extern \"my:pkg/missing\":
    fn idle()
extern:
    fn log(n: i32)
pub fn passes():
    pass
";
        let mut files = library("", vec![("checks", checks)]);
        let errors: Vec<_> = compile_tests(&mut files).unwrap_err();
        let shown: Vec<_> = errors.iter().map(Error::to_string).collect();
        assert_eq!(shown.len(), 2, "{shown:?}");
        assert!(
            shown[0].starts_with("no interface `my:pkg/missing` is there to import: "),
            "{shown:?}"
        );
        assert!(shown[0].contains("`wasi:cli/"), "{shown:?}");
        assert_eq!(shown[1], "the world imports no function `log`");
    }

    #[test]
    fn the_tests_of_a_program_are_a_component_of_their_own() {
        let checks = "\
extern \"wasi:cli/environment@0.3.0\":
    fn get_arguments() -> array(string)
pub fn has_a_name():
    get_arguments().len == 1 or module.unreachable()
";
        let entry: &str = Box::leak(format!("{ALLOCATOR}fn main():\n    pass\n").into_boxed_str());
        let mut files = program(entry, vec![("checks", checks)]);
        let Tests { component, tests } = compile_tests(&mut files).unwrap();
        assert_eq!(tests.len(), 1);
        wasmparser::Validator::new_with_features(wasmparser::WasmFeatures::all())
            .validate_all(&component)
            .unwrap();
        let wat = wasmprinter::print_bytes(&component).unwrap();
        assert!(
            wat.contains(&format!("(export \"{TEST_EXPORT}\" (func")),
            "{wat}"
        );
        // Nothing of the program is exported.
        assert!(!wat.contains("(export \"wasi:cli/run@0.3.0\""), "{wat}");
    }
}

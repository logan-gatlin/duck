//! `duck new`: the files of a fresh component or library.

use std::fs;
use std::io;
use std::path::Path;

use duck::manifest::{DEFAULT_TEST_DIR, MANIFEST};

const DEFAULT_MANIFEST: &str = r#"# Build using the `duck` cli

[component]
entry = "src/main.duck"
output = "build/out.wasm"
# A function taking and returning nothing, which is the program: the `run` of
# `wasi:cli/run` calls it, as `duck run` does.
start = "main"
# The world the component is one of: of WASI 0.3, or of the WIT in the `wit`
# directory beside this file. If not given, it is that of a program.
# world = "wasi:cli/command@0.3.0"

# Sizes are B, KiB, MiB, GiB, TiB, or pgs (64KiB wasm pages).
# [memory]
# What memory may grow to. It starts with the pages its literals take, and
# those its constants grow it by.
# max = "16MiB"
# The address literals are placed from. If not given, it is 0.
# static = { start = "1KiB" }
# The bytes of the return area, which holds what a function passes the host
# in memory. If not given, it is as many as the most that one passes, and
# if it is, a function that passes more is an error.
# return = "256B"

# [const]
# How long the code that a constant runs may take, counted in wasm
# instructions: the constants of one item share it. If not given, it is about
# a second's worth.
# fuel = 300000000

# The directory whose source files are the tests of the package, which
# `duck test` runs: each `pub fn` of one that takes nothing. If not given, it
# is `tests`.
# [test]
# dir = "tests"

# Packages to `use` by name, each with a [library].
# [dependencies]
# json = { path = "../json" }
# xml = { git = "https://example.com/xml.git", tag = "v1.0" }
"#;

const DEFAULT_MAIN: &str = "pub fn main():\n\tpass\n";

/// The test module of a new component.
const DEFAULT_TEST: &str = "\
use main

# A test, as it is `pub` and takes nothing: it passes if it returns, and
# fails if it traps.
pub fn main_returns():
\tmain.main()
";

const LIBRARY_MANIFEST: &str = r#"# Build using the `duck` cli

[library]
# The file other packages reach when they `use` this one.
entry = "src/lib.duck"

# The directory whose source files are the tests of the package, which
# `duck test` runs: each `pub fn` of one that takes nothing. If not given, it
# is `tests`.
# [test]
# dir = "tests"

# Packages to `use` by name, each with a [library].
# [dependencies]
# json = { path = "../json" }
# xml = { git = "https://example.com/xml.git", tag = "v1.0" }
"#;

const LIBRARY_ENTRY: &str = "pub fn add(a: i32, b: i32) -> i32:\n\treturn a + b\n";

/// The test module of a new library.
const LIBRARY_TEST: &str = "\
use lib

# A test, as it is `pub` and takes nothing: it passes if it returns, and
# fails if it traps.
pub fn adds():
\tlib.add(1, 2) == 3 or module.unreachable()
";

/// The file of the test directory that a new package has its test in.
const TEST_FILE: &str = "example.duck";

const DEFAULT_GITIGNORE: &str = "/build\n";

/// What kind of package `duck new` creates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A package that builds a wasm component.
    Component,
    /// A package that other packages use, which builds nothing.
    Library,
}

/// Creates a package of kind `kind` in the new directory `path`, with a test
/// in its test directory. Fails with [`io::ErrorKind::AlreadyExists`] if
/// anything is already at `path`.
pub fn new(path: &Path, kind: Kind) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::create_dir(path)?;
    fs::create_dir(path.join("src"))?;
    let tests = path.join(DEFAULT_TEST_DIR);
    fs::create_dir(&tests)?;
    match kind {
        Kind::Component => {
            fs::write(path.join(MANIFEST), DEFAULT_MANIFEST)?;
            fs::write(path.join("src/main.duck"), DEFAULT_MAIN)?;
            fs::write(tests.join(TEST_FILE), DEFAULT_TEST)?;
        }
        Kind::Library => {
            fs::write(path.join(MANIFEST), LIBRARY_MANIFEST)?;
            fs::write(path.join("src/lib.duck"), LIBRARY_ENTRY)?;
            fs::write(tests.join(TEST_FILE), LIBRARY_TEST)?;
        }
    }
    fs::write(path.join(".gitignore"), DEFAULT_GITIGNORE)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::run::test::{Console, Summary, list, run};
    use duck::files::Files;
    use duck::manifest::{Component, Library};
    use duck::package;

    /// The names of the tests of the new package in `package`, whose
    /// files are `files`, a line each, and how many did what when run.
    fn tested(files: Files, package: &Path) -> (String, Summary) {
        let mut files = files.with_tests(package.join(DEFAULT_TEST_DIR)).unwrap();
        let tests = duck_compiler::compile_tests(&mut files).unwrap();
        let mut names = Vec::new();
        list(&tests.tests, &[], &[], &mut names).unwrap();
        let console = Console::new(io::sink(), io::sink(), [false; 2]);
        let summary = run(&tests, &[], &[], "out.wasm", &console).unwrap();
        (String::from_utf8(names).unwrap(), summary)
    }

    #[test]
    fn what_a_new_package_has_is_formatted() {
        for source in [DEFAULT_MAIN, DEFAULT_TEST, LIBRARY_ENTRY, LIBRARY_TEST] {
            assert_eq!(duck_compiler::format::format(source).as_deref(), Ok(source));
        }
    }

    #[test]
    fn new_component_builds() {
        let dir = std::env::temp_dir().join(format!("duck-new-{}", std::process::id()));
        let module = dir.join("component");
        new(&module, Kind::Component).unwrap();
        let again = new(&module, Kind::Component).unwrap_err();

        let packages = package::resolve(&module, &duck::git::Cache::new(dir.join("cache")));
        let manifest = packages
            .as_ref()
            .map(|packages| packages.root().manifest.clone());
        let files = packages.as_ref().ok().map(|packages| {
            let component = packages.root().manifest.component.as_ref().unwrap();
            let entry = module.join(&component.entry);
            let settings = component.settings(duck::files::wit(packages).unwrap());
            let mut files = Files::new(packages, entry, settings).unwrap();
            let built = duck_compiler::compile(&mut files).map(|_| ());
            (built, tested(files, &module))
        });
        let gitignore = fs::read_to_string(module.join(".gitignore")).unwrap();
        fs::remove_dir_all(&dir).unwrap();

        assert_eq!(again.kind(), io::ErrorKind::AlreadyExists);
        let manifest = manifest.unwrap();
        assert_eq!(
            manifest.component,
            Some(Component {
                entry: "src/main.duck".into(),
                output: "build/out.wasm".into(),
                start: Some("main".to_string()),
                world: "wasi:cli/command@0.3.0".to_string(),
                max_pages: None,
                static_start: 0,
                return_area: None,
                fuel: None,
            })
        );
        assert_eq!(manifest.library, None);
        assert!(manifest.dependencies.is_empty());
        assert_eq!(manifest.tests, Some(DEFAULT_TEST_DIR.into()));
        let (built, (ran, summary)) = files.unwrap();
        assert_eq!(built, Ok(()));
        // Its test passes, as the program does nothing yet.
        assert_eq!(ran, "example.main_returns\n");
        assert_eq!((summary.passed, summary.failed), (1, 0));
        assert_eq!(gitignore, "/build\n");
    }

    #[test]
    fn new_library_checks() {
        let dir = std::env::temp_dir().join(format!("duck-new-lib-{}", std::process::id()));
        let library = dir.join("library");
        new(&library, Kind::Library).unwrap();
        let again = new(&library, Kind::Library).unwrap_err();

        let packages = package::resolve(&library, &duck::git::Cache::new(dir.join("cache")));
        let manifest = packages
            .as_ref()
            .map(|packages| packages.root().manifest.clone());
        let checked = packages.as_ref().ok().map(|packages| {
            let entry = library.join("src/lib.duck");
            let mut files = Files::new(packages, entry, Default::default()).unwrap();
            let checked = duck_compiler::check(&mut files);
            (checked, tested(files, &library))
        });
        let gitignore = fs::read_to_string(library.join(".gitignore")).unwrap();
        fs::remove_dir_all(&dir).unwrap();

        assert_eq!(again.kind(), io::ErrorKind::AlreadyExists);
        let manifest = manifest.unwrap();
        assert_eq!(manifest.component, None);
        assert_eq!(
            manifest.library,
            Some(Library {
                entry: "src/lib.duck".into(),
                fuel: None,
            })
        );
        assert!(manifest.dependencies.is_empty());
        assert_eq!(manifest.tests, Some(DEFAULT_TEST_DIR.into()));
        let (checked, (ran, summary)) = checked.unwrap();
        assert_eq!(checked, Ok(()));
        assert_eq!(ran, "example.adds\n");
        assert_eq!((summary.passed, summary.failed), (1, 0));
        assert_eq!(gitignore, "/build\n");
    }
}

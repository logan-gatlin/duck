//! `duck new`: the files of a fresh component or library.

use std::fs;
use std::io;
use std::path::Path;

use duck::manifest::MANIFEST;

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
# Address memory with 64 bits rather than 32, which makes pointers, `int` and
# `uint` 64 bits wide and lets sizes pass 4GiB.
# memory64 = true
# What memory may grow to. It starts with the pages its literals take, and
# those its constants grow it by.
# max = "16MiB"
# The address literals are placed from. If not given, it is 0.
# static = { start = "1KiB" }

# [const]
# How long the code that a constant runs may take, counted in wasm
# instructions: the constants of one item share it. If not given, it is about
# a second's worth.
# fuel = 10000000000

# Packages to `use` by name, each with a [library].
# [dependencies]
# json = { path = "../json" }
# xml = { git = "https://example.com/xml.git", tag = "v1.0" }
"#;

const DEFAULT_MAIN: &str = "pub fn main():\n\tpass\n";

const LIBRARY_MANIFEST: &str = r#"# Build using the `duck` cli

[library]
# The file other packages reach when they `use` this one.
entry = "src/lib.duck"

# Packages to `use` by name, each with a [library].
# [dependencies]
# json = { path = "../json" }
# xml = { git = "https://example.com/xml.git", tag = "v1.0" }
"#;

const LIBRARY_ENTRY: &str = "pub fn add(a: i32, b: i32) -> i32:\n\treturn a + b\n";

const DEFAULT_GITIGNORE: &str = "/build\n";

/// What kind of package `duck new` creates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A package that builds a wasm component.
    Component,
    /// A package that other packages use, which builds nothing.
    Library,
}

/// Creates a package of kind `kind` in the new directory `path`. Fails with
/// [`io::ErrorKind::AlreadyExists`] if anything is already at `path`.
pub fn new(path: &Path, kind: Kind) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::create_dir(path)?;
    fs::create_dir(path.join("src"))?;
    match kind {
        Kind::Component => {
            fs::write(path.join(MANIFEST), DEFAULT_MANIFEST)?;
            fs::write(path.join("src/main.duck"), DEFAULT_MAIN)?;
        }
        Kind::Library => {
            fs::write(path.join(MANIFEST), LIBRARY_MANIFEST)?;
            fs::write(path.join("src/lib.duck"), LIBRARY_ENTRY)?;
        }
    }
    fs::write(path.join(".gitignore"), DEFAULT_GITIGNORE)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use duck::files::Files;
    use duck::manifest::{Component, Library};
    use duck::package;

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
            let settings = component.settings(duck::files::wit(&module).unwrap());
            let mut files = Files::new(packages, entry, settings).unwrap();
            duck_compiler::compile(&mut files).map(|_| ())
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
                memory64: false,
                static_start: 0,
                fuel: None,
            })
        );
        assert_eq!(manifest.library, None);
        assert!(manifest.dependencies.is_empty());
        assert_eq!(files, Some(Ok(())));
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
            duck_compiler::check(&mut files)
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
        assert_eq!(checked, Some(Ok(())));
        assert_eq!(gitignore, "/build\n");
    }
}

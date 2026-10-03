//! `duck new`: the files of a fresh module or library.

use std::fs;
use std::io;
use std::path::Path;

use duck::manifest::MANIFEST;

const DEFAULT_MANIFEST: &str = r#"# Build using the `duck` cli

[module]
entry = "src/main.duck"
output = "build/out.wasm"
# A function taking and returning nothing, run when the module is instantiated.
start = "main"

# Sizes are B, KiB, MiB, GiB, or pgs (64KiB wasm pages).
# [memory]
# What memory starts with. If not given, it is just enough to hold `static`.
# min = "1pgs"
# max = "16MiB"
# The addresses literals are placed in, which `module.static` is. If not
# given, it starts at 0 and ends where the literals do.
# static = { start = "0B", end = "64KiB" }

# Packages to `import` by name, each with a [library].
# [dependencies]
# json = { path = "../json" }
# xml = { git = "https://example.com/xml.git", tag = "v1.0" }
"#;

const DEFAULT_MAIN: &str = "pub fn main():\n\tpass\n";

const LIBRARY_MANIFEST: &str = r#"# Build using the `duck` cli

[library]
# The file other packages reach when they `import` this one.
entry = "src/lib.duck"

# Packages to `import` by name, each with a [library].
# [dependencies]
# json = { path = "../json" }
# xml = { git = "https://example.com/xml.git", tag = "v1.0" }
"#;

const LIBRARY_ENTRY: &str = "pub fn add(a: i32, b: i32) -> i32:\n\treturn a + b\n";

const DEFAULT_GITIGNORE: &str = "/build\n";

/// What kind of package `duck new` creates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    /// A package that builds a wasm module.
    Module,
    /// A package that other packages import, which builds nothing.
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
        Kind::Module => {
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
    use duck_compiler::file::MemoryLimits;

    use super::*;
    use duck::files::Files;
    use duck::manifest::{Library, Module};
    use duck::package;

    #[test]
    fn new_module_builds() {
        let dir = std::env::temp_dir().join(format!("duck-new-{}", std::process::id()));
        let module = dir.join("module");
        new(&module, Kind::Module).unwrap();
        let again = new(&module, Kind::Module).unwrap_err();

        let packages = package::resolve(&module, &duck::git::Cache::new(dir.join("cache")));
        let manifest = packages
            .as_ref()
            .map(|packages| packages.root().manifest.clone());
        let files = packages.as_ref().ok().map(|packages| {
            let module_manifest = packages.root().manifest.module.as_ref().unwrap();
            let entry = module.join(&module_manifest.entry);
            let mut files = Files::new(packages, entry, module_manifest.settings()).unwrap();
            duck_compiler::compile(&mut files).map(|_| ())
        });
        let gitignore = fs::read_to_string(module.join(".gitignore")).unwrap();
        fs::remove_dir_all(&dir).unwrap();

        assert_eq!(again.kind(), io::ErrorKind::AlreadyExists);
        let manifest = manifest.unwrap();
        assert_eq!(
            manifest.module,
            Some(Module {
                entry: "src/main.duck".into(),
                output: "build/out.wasm".into(),
                start: Some("main".to_string()),
                memory: MemoryLimits {
                    min_pages: None,
                    max_pages: None,
                },
                static_section: None,
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
            duck_compiler::compile(&mut files).map(|_| ())
        });
        let gitignore = fs::read_to_string(library.join(".gitignore")).unwrap();
        fs::remove_dir_all(&dir).unwrap();

        assert_eq!(again.kind(), io::ErrorKind::AlreadyExists);
        let manifest = manifest.unwrap();
        assert_eq!(manifest.module, None);
        assert_eq!(
            manifest.library,
            Some(Library {
                entry: "src/lib.duck".into()
            })
        );
        assert!(manifest.dependencies.is_empty());
        assert_eq!(checked, Some(Ok(())));
        assert_eq!(gitignore, "/build\n");
    }
}

//! `duck new`: the files of a fresh module.

use std::fs;
use std::io;
use std::path::Path;

use crate::manifest::MANIFEST;

const DEFAULT_MANIFEST: &str = r#"[module]
entry = "src/main.duck"
output = "build/out.wasm"
# A function taking and returning nothing, run when the module is instantiated.
start = "main"

[memory]
# Sizes are KiB, MiB, GiB, or pgs (64KiB wasm pages).
min = "1pgs"
# max = "16MiB"

# Packages to `import` by name, each with a [library].
# [dependencies]
# json = { path = "../json" }
"#;

const DEFAULT_MAIN: &str = "pub fn main():\n\tpass\n";

const DEFAULT_GITIGNORE: &str = "/build\n";

/// Creates a module in the new directory `path`. Fails with
/// [`io::ErrorKind::AlreadyExists`] if anything is already at `path`.
pub fn new(path: &Path) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::create_dir(path)?;
    fs::create_dir(path.join("src"))?;
    fs::write(path.join(MANIFEST), DEFAULT_MANIFEST)?;
    fs::write(path.join("src/main.duck"), DEFAULT_MAIN)?;
    fs::write(path.join(".gitignore"), DEFAULT_GITIGNORE)?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use duck_compiler::file::MemoryLimits;

    use super::*;
    use crate::files::Files;
    use crate::manifest::Module;
    use crate::package;

    #[test]
    fn new_module_builds() {
        let dir = std::env::temp_dir().join(format!("duck-new-{}", std::process::id()));
        let module = dir.join("module");
        new(&module).unwrap();
        let again = new(&module).unwrap_err();

        let packages = package::resolve(&module);
        let manifest = packages
            .as_ref()
            .map(|packages| packages.root().manifest.clone());
        let files = packages.as_ref().ok().map(|packages| {
            let module_manifest = packages.root().manifest.module.as_ref().unwrap();
            let settings = duck_compiler::file::Settings {
                memory: module_manifest.memory,
                start: module_manifest.start.clone(),
            };
            let entry = module.join(&module_manifest.entry);
            let mut files = Files::new(packages, entry, settings).unwrap();
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
                    min_pages: 1,
                    max_pages: None,
                },
            })
        );
        assert_eq!(manifest.library, None);
        assert!(manifest.dependencies.is_empty());
        assert_eq!(files, Some(Ok(())));
        assert_eq!(gitignore, "/build\n");
    }
}

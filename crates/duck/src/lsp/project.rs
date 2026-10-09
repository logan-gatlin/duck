//! Checks a package as `duck build` does, giving each error as a place in a
//! file rather than printing it.

use std::fs;
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};

use duck::files::Files;
use duck::git::Cache;
use duck::manifest::{MANIFEST, ManifestError};
use duck::package::{self, Packages, ResolveError};
use duck_compiler::file::{FileId, FileManager, Settings};
use duck_compiler::lex::Span;
use duck_compiler::{Error, load, ty};
use lsp_types::{Position, Range};

/// The text of the file at a canonical path, if the editor has it open.
pub type Buffers<'a> = &'a dyn Fn(&Path) -> Option<&'a str>;

/// A package and every package it depends on, as their manifests were when
/// it was resolved.
pub struct Project {
    /// The directory holding the package's manifest.
    root: PathBuf,
    packages: Result<Packages, ResolveError>,
}

/// An error, and where it is.
#[derive(Debug, Clone, PartialEq)]
pub struct Problem {
    pub place: Place,
    pub message: String,
    /// What led to the error, nearest first.
    pub notes: Vec<Note>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Note {
    pub place: Place,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Place {
    /// The canonical path of the file.
    pub path: PathBuf,
    pub range: Range,
}

/// The files of a build, those open in the editor read as they are there
/// rather than as they were saved.
struct Overlay<'a> {
    files: Files,
    buffers: Buffers<'a>,
}

impl Project {
    /// Reads the manifest of the package in `root`, then those of its
    /// dependencies, fetching git dependencies into `cache`.
    pub fn resolve(root: PathBuf, cache: &Cache) -> Self {
        let packages = package::resolve(&root, cache);
        Self { root, packages }
    }

    /// Every error in the package's module and in its library. Files they
    /// don't use aren't checked.
    pub fn check(&self, buffers: Buffers<'_>) -> Vec<Problem> {
        let manifest_path = canonical(&self.root.join(MANIFEST));
        let packages = match &self.packages {
            Ok(packages) => packages,
            Err(error) => return vec![resolve_problem(manifest_path, error)],
        };
        let manifest = &packages.root().manifest;
        let module = (manifest.module.as_ref()).map(|module| (&module.entry, module.settings()));
        let library = manifest.library.as_ref();
        let library = library.map(|library| (&library.entry, library.settings()));

        let mut problems = Vec::new();
        for (entry, settings) in module.into_iter().chain(library) {
            let found = match Files::new(packages, self.root.join(entry), settings) {
                Ok(files) => Overlay { files, buffers }.problems(&manifest_path),
                Err(e) => {
                    let message = format!("cannot read {}: {e}", entry.display());
                    vec![Problem::in_manifest(manifest_path.clone(), message)]
                }
            };
            // A file both use has its errors found twice.
            for problem in found {
                if !problems.contains(&problem) {
                    problems.push(problem);
                }
            }
        }
        problems
    }
}

impl Problem {
    /// A problem with the whole of the manifest at `path`.
    fn in_manifest(path: PathBuf, message: String) -> Self {
        Self {
            place: Place {
                path,
                range: Range::default(),
            },
            message,
            notes: Vec::new(),
        }
    }
}

impl Overlay<'_> {
    /// The errors of compiling the files, those that no file holds placed
    /// in the manifest at `manifest_path`.
    fn problems(mut self, manifest_path: &Path) -> Vec<Problem> {
        // Half-written code is what the compiler is least tested on, and a
        // bug in it shouldn't end the server.
        let errors = panic::catch_unwind(AssertUnwindSafe(|| self.errors()));
        let Ok(errors) = errors else {
            let message = "the compiler crashed checking this package".to_string();
            return vec![Problem::in_manifest(manifest_path.to_path_buf(), message)];
        };
        let problems = errors.iter().map(|error| {
            let message = error.to_string();
            let Some(span) = error.span() else {
                return Problem::in_manifest(manifest_path.to_path_buf(), message);
            };
            let notes = error.instances().iter().map(|site| Note {
                place: self.place(site.span),
                message: format!("required by `{}` here", site.name),
            });
            Problem {
                notes: notes.collect(),
                place: self.place(span),
                message,
            }
        });
        problems.collect()
    }

    /// Loads and type checks the files, as [`duck_compiler::compile`] does
    /// before emitting them.
    fn errors(&mut self) -> Vec<Error> {
        let program = match load::load(self) {
            Ok(program) => program,
            Err(errors) => return errors,
        };
        let errors = ty::errors(&program, &self.settings());
        errors.into_iter().map(Error::Type).collect()
    }

    fn place(&mut self, span: Span) -> Place {
        let src = self.contents(span.file);
        Place {
            path: self.files.path(span.file).to_path_buf(),
            range: range(&src, span.start, span.end),
        }
    }
}

impl FileManager for Overlay<'_> {
    fn entry_point(&mut self) -> FileId {
        self.files.entry_point()
    }

    fn display_name(&mut self, id: FileId) -> String {
        self.files.display_name(id)
    }

    fn contents(&mut self, id: FileId) -> String {
        match (self.buffers)(self.files.path(id)) {
            Some(text) => text.to_string(),
            None => self.files.contents(id),
        }
    }

    fn open(&mut self, from: FileId, path: &[&str]) -> Option<FileId> {
        self.files.open(from, path)
    }

    fn open_package(&mut self, from: FileId, name: &str) -> Option<FileId> {
        self.files.open_package(from, name)
    }

    fn settings(&mut self) -> Settings {
        self.files.settings()
    }
}

/// The directory of the package `path` is in: the nearest directory with a
/// manifest, `path` itself or above it.
pub fn root_of(path: &Path) -> Option<PathBuf> {
    let root = path.ancestors().find(|dir| dir.join(MANIFEST).is_file());
    root.map(Path::to_path_buf)
}

/// The canonical path of `path`, or `path` itself if nothing is there.
pub fn canonical(path: &Path) -> PathBuf {
    fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

/// Places a failure to resolve the package whose manifest is at
/// `manifest_path`: in the manifest that is wrong if one is, and otherwise in
/// its own.
fn resolve_problem(manifest_path: PathBuf, error: &ResolveError) -> Problem {
    let ResolveError::Manifest { path, error } = error else {
        return Problem::in_manifest(manifest_path, error.to_string());
    };
    let mut problem = Problem::in_manifest(canonical(path), error.to_string());
    if let ManifestError::Toml(error) = error {
        // Without the excerpt of the source that the full message draws.
        problem.message = error.message().to_string();
        if let (Some(span), Ok(src)) = (error.span(), fs::read_to_string(path)) {
            problem.place.range = range(&src, span.start, span.end);
        }
    }
    problem
}

fn range(src: &str, start: usize, end: usize) -> Range {
    Range::new(position(src, start), position(src, end))
}

/// Where byte `offset` of `src` is, with the column in UTF-16 code units, as
/// editors count them unless asked otherwise.
fn position(src: &str, offset: usize) -> Position {
    let before = &src[..offset.min(src.len())];
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    let line = before.matches('\n').count();
    let column = before[line_start..].encode_utf16().count();
    Position::new(line as u32, column as u32)
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::HashMap;

    use super::*;

    /// A directory that is removed when dropped.
    pub(crate) struct TempDir(pub(crate) PathBuf);

    impl TempDir {
        pub(crate) fn new(name: &str) -> Self {
            let dir = std::env::temp_dir().join(format!("duck-lsp-{name}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir).unwrap();
            // Canonical, as the paths of problems are.
            Self(fs::canonicalize(dir).unwrap())
        }

        /// Writes each file, at a path relative to the directory.
        pub(crate) fn write(&self, files: &[(&str, &str)]) {
            for (path, contents) in files {
                let path = self.0.join(path);
                fs::create_dir_all(path.parent().unwrap()).unwrap();
                fs::write(path, contents).unwrap();
            }
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    pub(crate) const MODULE: &str = "[module]\nentry = \"main.duck\"\noutput = \"out.wasm\"\n[memory]\nmin = \"1pgs\"\nstatic = { start = \"0B\", end = \"64KiB\" }\n";

    const LIBRARY: &str = "[library]\nentry = \"lib.duck\"\n";

    /// Checks the package in `dir/app`, with each of `buffers` open in the
    /// editor. Gives each problem as `path:line:column-line:column: message`,
    /// with the path relative to `dir`, followed by its notes.
    fn check(dir: &TempDir, buffers: &[(&str, &str)]) -> Vec<String> {
        let buffers: HashMap<PathBuf, &str> = (buffers.iter())
            .map(|(path, text)| (dir.0.join(path), *text))
            .collect();
        let cache = Cache::new(dir.0.join("no-cache"));
        let project = Project::resolve(dir.0.join("app"), &cache);
        let show = |place: &Place, message: &str| {
            let path = place.path.strip_prefix(&dir.0).unwrap().display();
            let Range { start, end } = place.range;
            format!(
                "{path}:{}:{}-{}:{}: {message}",
                start.line, start.character, end.line, end.character
            )
        };
        let problems = project.check(&|path| buffers.get(path).copied());
        let lines = problems.iter().flat_map(|problem| {
            let notes = problem.notes.iter();
            let notes = notes.map(|note| show(&note.place, &note.message));
            std::iter::once(show(&problem.place, &problem.message)).chain(notes)
        });
        lines.collect()
    }

    #[test]
    fn positions_count_utf16_code_units() {
        let src = "let a = 1\nlet s = \"é😀\" @\n";
        let at = |text: &str| {
            let position = position(src, src.find(text).unwrap());
            (position.line, position.character)
        };
        assert_eq!(at("let a"), (0, 0));
        assert_eq!(at("1"), (0, 8));
        assert_eq!(at("é"), (1, 9));
        assert_eq!(at("😀"), (1, 10));
        // `é` is one unit and `😀` two, though they are two bytes and four.
        assert_eq!(at("@"), (1, 14));
        assert_eq!(position(src, src.len()), Position::new(2, 0));
        assert_eq!(position(src, src.len() + 9), Position::new(2, 0));
    }

    #[test]
    fn errors_are_placed_in_the_files_they_are_in() {
        let dir = TempDir::new("placed");
        dir.write(&[
            (
                "app/Duck.toml",
                &format!("{MODULE}[dependencies]\nutil = {{ path = \"../util\" }}\n"),
            ),
            ("app/main.duck", "use src.a\nuse util\nlet x: Nope = 1\n"),
            ("app/src/a.duck", "let ok = 1\nlet y = @\n"),
            ("app/src/unused.duck", "let z = @\n"),
            ("util/Duck.toml", LIBRARY),
            ("util/lib.duck", "fn f(: i32):\n    pass\n"),
        ]);
        assert_eq!(
            check(&dir, &[]),
            [
                "app/src/a.duck:1:8-1:9: unexpected character '@'",
                "util/lib.duck:0:5-0:6: expected identifier, found `:`",
            ]
        );

        dir.write(&[
            ("app/src/a.duck", ""),
            ("util/lib.duck", "pub let one = 1\n"),
        ]);
        assert_eq!(
            check(&dir, &[]),
            ["app/main.duck:2:7-2:11: unknown type `Nope`"]
        );
    }

    #[test]
    fn open_files_are_read_as_they_are_in_the_editor() {
        let dir = TempDir::new("buffers");
        dir.write(&[
            ("app/Duck.toml", MODULE),
            ("app/main.duck", "use a\nlet x = a.y\n"),
            ("app/a.duck", "pub let y = 1\n"),
        ]);
        assert_eq!(check(&dir, &[]), [] as [&str; 0]);
        assert_eq!(
            check(&dir, &[("app/a.duck", "\n\npub let y: Nope = 1\n")]),
            ["app/a.duck:2:11-2:15: unknown type `Nope`"]
        );
        assert_eq!(
            check(&dir, &[("app/main.duck", "let x = nope\n")]),
            ["app/main.duck:0:8-0:12: unknown name `nope`"]
        );
    }

    #[test]
    fn modules_and_libraries_are_both_checked() {
        let dir = TempDir::new("both");
        dir.write(&[
            ("app/Duck.toml", &format!("{MODULE}{LIBRARY}")),
            ("app/main.duck", "use shared\nlet a: A = 1\n"),
            ("app/lib.duck", "use shared\nlet b: B = 1\n"),
            ("app/shared.duck", "let s: S = 1\n"),
        ]);
        assert_eq!(
            check(&dir, &[]),
            [
                "app/shared.duck:0:7-0:8: unknown type `S`",
                "app/main.duck:1:7-1:8: unknown type `A`",
                "app/lib.duck:1:7-1:8: unknown type `B`",
            ]
        );
    }

    #[test]
    fn memory64_widens_a_module_and_not_the_library_beside_it() {
        let dir = TempDir::new("memory64");
        let module =
            "[module]\nentry = \"main.duck\"\noutput = \"out.wasm\"\n[memory]\nmemory64 = true\n";
        dir.write(&[
            ("app/Duck.toml", &format!("{module}{LIBRARY}")),
            ("app/main.duck", "let far: uint = 4294967296\n"),
            ("app/lib.duck", "let far: uint = 4294967296\n"),
        ]);
        // A library is checked alone with addresses 32 bits wide.
        assert_eq!(
            check(&dir, &[]),
            ["app/lib.duck:0:16-0:26: literal out of range for `uint`"]
        );
    }

    #[test]
    fn errors_in_instances_note_the_instances_that_led_to_them() {
        let dir = TempDir::new("instances");
        dir.write(&[
            ("app/Duck.toml", MODULE),
            (
                "app/main.duck",
                "fn(T) nest(x: T):\n    nest((x, x))\nfn f():\n    nest(true)\n",
            ),
        ]);
        // Each instance of `nest` needs another, without end.
        let problems = check(&dir, &[]);
        assert!(problems.len() > 2, "{problems:?}");
        assert!(
            problems[0].starts_with("app/main.duck:3:4-3:14: "),
            "{problems:?}"
        );
        assert_eq!(
            problems[1],
            "app/main.duck:1:4-1:16: required by `nest(bool)` here"
        );
    }

    #[test]
    fn errors_no_file_holds_are_placed_in_the_manifest() {
        let dir = TempDir::new("manifest");
        let start = MODULE.replace("[memory]", "start = \"main\"\n[memory]");
        dir.write(&[("app/Duck.toml", &start), ("app/main.duck", "")]);
        assert_eq!(
            check(&dir, &[]),
            ["app/Duck.toml:0:0-0:0: no function named `main` to start"]
        );

        fs::remove_file(dir.0.join("app/main.duck")).unwrap();
        let problems = check(&dir, &[]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("app/Duck.toml:0:0-0:0: cannot read main.duck: "),
            "{problems:?}"
        );
    }

    #[test]
    fn manifests_that_cannot_be_resolved() {
        let dir = TempDir::new("unresolved");
        dir.write(&[(
            "app/Duck.toml",
            "[library]\nentry = \"lib.duck\"\nnope = 1\n",
        )]);
        let problems = check(&dir, &[]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("app/Duck.toml:2:0-2:4: unknown field `nope`"),
            "{problems:?}"
        );

        dir.write(&[("app/Duck.toml", "[dependencies]\n")]);
        assert_eq!(
            check(&dir, &[]),
            ["app/Duck.toml:0:0-0:0: needs a [module] or [library] table"]
        );

        // A dependency's manifest holds what is wrong with it.
        dir.write(&[
            (
                "app/Duck.toml",
                &format!("{LIBRARY}[dependencies]\nutil = {{ path = \"../util\" }}\n"),
            ),
            ("app/lib.duck", ""),
            ("util/Duck.toml", "[library]\n"),
        ]);
        let problems = check(&dir, &[]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("util/Duck.toml:0:0-0:9: missing field `entry`"),
            "{problems:?}"
        );

        // But one that is missing is a problem with the package wanting it.
        fs::remove_file(dir.0.join("util/Duck.toml")).unwrap();
        let problems = check(&dir, &[]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("app/Duck.toml:0:0-0:0: cannot read "),
            "{problems:?}"
        );
    }

    #[test]
    fn a_crash_of_the_compiler_is_a_problem_of_the_package() {
        let dir = TempDir::new("crash");
        dir.write(&[("app/Duck.toml", MODULE), ("app/main.duck", "")]);
        let cache = Cache::new(dir.0.join("no-cache"));
        let project = Project::resolve(dir.0.join("app"), &cache);
        let problems = project.check(&|_| panic!("as a bug in the compiler would"));
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert_eq!(problems[0].place.path, dir.0.join("app/Duck.toml"));
        assert_eq!(
            problems[0].message,
            "the compiler crashed checking this package"
        );
    }

    #[test]
    fn packages_are_found_from_the_files_in_them() {
        let dir = TempDir::new("root");
        dir.write(&[
            ("app/Duck.toml", MODULE),
            ("app/src/deep/a.duck", ""),
            ("app/libs/util/Duck.toml", LIBRARY),
            ("app/libs/util/lib.duck", ""),
        ]);
        let root = |path: &str| root_of(&dir.0.join(path));
        assert_eq!(root("app"), Some(dir.0.join("app")));
        assert_eq!(root("app/src/deep/a.duck"), Some(dir.0.join("app")));
        assert_eq!(root("app/src/deep/unsaved.duck"), Some(dir.0.join("app")));
        assert_eq!(
            root("app/libs/util/lib.duck"),
            Some(dir.0.join("app/libs/util"))
        );
        assert_eq!(root("other.duck"), None);
    }
}

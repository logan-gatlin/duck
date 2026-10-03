//! The packages a build reads: the one being built, and every package it
//! depends on, directly or not.

use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::git::{Cache, GitError};
use crate::manifest::{Dependency, MANIFEST, Manifest, ManifestError};

/// Every package of a build, each once however many depend on it. The
/// first is the one being built.
#[derive(Debug)]
pub struct Packages(Vec<Package>);

#[derive(Debug)]
pub struct Package {
    /// The directory holding the manifest, as reached from the working
    /// directory.
    pub dir: PathBuf,
    pub manifest: Manifest,
    /// The package each dependency is, by its index in [`Packages`].
    pub dependencies: BTreeMap<String, usize>,
}

#[derive(Debug)]
pub enum ResolveError {
    Read {
        path: PathBuf,
        error: io::Error,
    },
    Manifest {
        path: PathBuf,
        error: ManifestError,
    },
    /// A dependency without a library to import.
    NotALibrary {
        name: String,
        dir: PathBuf,
    },
    /// A git dependency that couldn't be fetched.
    Git {
        name: String,
        error: GitError,
    },
    /// A git repository needed at two commits, each with the dependencies
    /// that lead to it from the package being built.
    Conflict {
        url: String,
        first: (String, String),
        second: (String, String),
    },
}

/// Gathers the packages a build of the package in `dir` reads.
struct Resolver<'c> {
    cache: &'c Cache,
    packages: Vec<Package>,
    /// Each package by the canonical path of its directory.
    ids: HashMap<PathBuf, usize>,
    /// The commit each git repository is needed at, by URL, and the
    /// dependencies that first led to it.
    commits: HashMap<String, (String, Vec<String>)>,
}

impl Packages {
    pub fn root(&self) -> &Package {
        &self.0[0]
    }

    pub fn iter(&self) -> impl Iterator<Item = &Package> {
        self.0.iter()
    }
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read { path, error } => write!(f, "cannot read {}: {error}", path.display()),
            Self::Manifest { path, error } => write!(f, "{}: {error}", path.display()),
            Self::NotALibrary { name, dir } => {
                write!(
                    f,
                    "dependency `{name}` at {} has no [library]",
                    dir.display()
                )
            }
            Self::Git { name, error } => write!(f, "dependency `{name}`: {error}"),
            Self::Conflict { url, first, second } => write!(
                f,
                "{url} is needed at two commits: {:.12} by {}, and {:.12} by {}",
                first.0, first.1, second.0, second.1
            ),
        }
    }
}

impl std::error::Error for ResolveError {}

/// Reads the manifest of the package in `dir`, then those of its
/// dependencies, recursively, fetching git dependencies into `cache`.
pub fn resolve(dir: &Path, cache: &Cache) -> Result<Packages, ResolveError> {
    let mut resolver = Resolver {
        cache,
        packages: Vec::new(),
        ids: HashMap::new(),
        commits: HashMap::new(),
    };
    resolver.package(dir, &[])?;
    Ok(Packages(resolver.packages))
}

/// The canonical path of `dir`, which is empty for the working directory.
pub fn canonical_dir(dir: &Path) -> io::Result<PathBuf> {
    fs::canonicalize(dir.join("."))
}

impl Resolver<'_> {
    /// The index of the package in `dir`, reading it if it's new. `chain`
    /// is the dependencies that lead to it.
    fn package(&mut self, dir: &Path, chain: &[String]) -> Result<usize, ResolveError> {
        let path = dir.join(MANIFEST);
        let read_error = |error| ResolveError::Read {
            path: path.clone(),
            error,
        };
        let canonical = canonical_dir(dir).map_err(read_error)?;
        if let Some(id) = self.ids.get(&canonical) {
            return Ok(*id);
        }
        let src = fs::read_to_string(&path).map_err(read_error)?;
        let manifest = Manifest::parse(&src).map_err(|error| ResolveError::Manifest {
            path: path.clone(),
            error,
        })?;
        let id = self.packages.len();
        self.ids.insert(canonical, id);
        let deps = manifest.dependencies.clone();
        self.packages.push(Package {
            dir: dir.to_path_buf(),
            manifest,
            dependencies: BTreeMap::new(),
        });
        for (name, dependency) in deps {
            let chain = [chain, std::slice::from_ref(&name)].concat();
            let dep_dir = match dependency {
                Dependency::Path(path) => dir.join(path),
                Dependency::Git {
                    url,
                    reference,
                    path,
                } => {
                    let checkout = self.cache.checkout(&url, &reference);
                    let (commit, checkout) = checkout.map_err(|error| ResolveError::Git {
                        name: name.clone(),
                        error,
                    })?;
                    self.pin(url, commit, &chain)?;
                    checkout.join(path.unwrap_or_default())
                }
            };
            let dep = self.package(&dep_dir, &chain)?;
            let Some(library) = &self.packages[dep].manifest.library else {
                return Err(ResolveError::NotALibrary { name, dir: dep_dir });
            };
            let entry = dep_dir.join(&library.entry);
            if let Err(error) = fs::metadata(&entry) {
                return Err(ResolveError::Read { path: entry, error });
            }
            self.packages[id].dependencies.insert(name, dep);
        }
        Ok(id)
    }

    /// Records that the dependencies `chain` need the repository at `url` at
    /// `commit`, which must be the commit any others need it at.
    fn pin(&mut self, url: String, commit: String, chain: &[String]) -> Result<(), ResolveError> {
        match self.commits.get(&url) {
            Some((first, _)) if *first == commit => Ok(()),
            Some((first, first_chain)) => Err(ResolveError::Conflict {
                first: (first.clone(), first_chain.join(" -> ")),
                second: (commit, chain.join(" -> ")),
                url,
            }),
            None => {
                self.commits.insert(url, (commit, chain.to_vec()));
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::{Path, PathBuf};

    use duck_compiler::file::{FileManager, Settings};

    use std::process::Command;

    use super::*;
    use crate::files::Files;

    /// A directory that is removed when dropped.
    struct TempDir(PathBuf);

    impl TempDir {
        fn new(name: &str) -> Self {
            let dir = std::env::temp_dir().join(format!("duck-{name}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir).unwrap();
            Self(dir)
        }

        /// Writes each file, at a path relative to the directory.
        fn write(&self, files: &[(&str, &str)]) {
            for (path, contents) in files {
                let path = self.0.join(path);
                fs::create_dir_all(path.parent().unwrap()).unwrap();
                fs::write(path, contents).unwrap();
            }
        }
    }

    /// Runs `git args` in `dir`, returning its output, trimmed.
    fn git(dir: &Path, args: &[&str]) -> String {
        let output = Command::new("git")
            .args(["-c", "user.name=duck", "-c", "user.email=duck@example.com"])
            .args(["-c", "init.defaultBranch=main", "-c", "tag.gpgSign=false"])
            .args(["-c", "commit.gpgSign=false", "-C"])
            .arg(dir)
            .args(args)
            .output()
            .unwrap();
        assert!(output.status.success(), "git {args:?}: {output:?}");
        String::from_utf8(output.stdout).unwrap().trim().to_string()
    }

    /// Commits `files` to the repository in `dir`, making it if needed, and
    /// tags the commit with `tag`. Returns the commit.
    fn commit(dir: &Path, files: &[(&str, &str)], tag: &str) -> String {
        if !dir.join(".git").exists() {
            fs::create_dir_all(dir).unwrap();
            git(dir, &["init", "--quiet"]);
        }
        for (path, contents) in files {
            let path = dir.join(path);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, contents).unwrap();
        }
        git(dir, &["add", "--all"]);
        git(dir, &["commit", "--quiet", "--allow-empty", "-m", "commit"]);
        git(dir, &["tag", "--force", tag]);
        git(dir, &["rev-parse", "HEAD"])
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn no_cache(root: &Path) -> Cache {
        Cache::new(root.join("no-cache"))
    }

    const LIBRARY: &str = "[library]\nentry = \"lib.duck\"\n";

    fn library(dependencies: &str) -> String {
        format!("{LIBRARY}[dependencies]\n{dependencies}")
    }

    /// The directory of each package, relative to `root`, and the index
    /// of each of its dependencies.
    fn layout(root: &Path, packages: &Packages) -> Vec<(String, Vec<(String, usize)>)> {
        packages
            .iter()
            .map(|package| {
                let dir = package.dir.strip_prefix(root).unwrap();
                let deps = package.dependencies.iter().map(|(n, i)| (n.clone(), *i));
                (dir.display().to_string(), deps.collect())
            })
            .collect()
    }

    /// Compiles the library of the package in `root`, giving each error as
    /// `path: message`, with the path relative to `root`.
    fn check(root: &Path) -> Result<(), Vec<String>> {
        check_with(root, &Cache::new(root.join("no-cache")))
    }

    fn check_with(root: &Path, cache: &Cache) -> Result<(), Vec<String>> {
        let packages = resolve(root, cache).map_err(|e| vec![e.to_string()])?;
        let library = packages.root().manifest.library.as_ref().unwrap();
        let entry = root.join(&library.entry);
        let mut files = Files::new(&packages, &entry, Settings::default()).unwrap();
        let errors = match duck_compiler::compile(&mut files) {
            Ok(_) => return Ok(()),
            Err(errors) => errors,
        };
        let errors = errors.iter().map(|error| {
            let file = files.display_name(error.span().unwrap().file);
            let file = Path::new(&file)
                .strip_prefix(root)
                .unwrap()
                .display()
                .to_string();
            format!("{file}: {error}")
        });
        Err(errors.collect())
    }

    #[test]
    fn dependencies_are_found_by_path_and_shared() {
        let dir = TempDir::new("shared");
        let root = dir.0.join("app");
        dir.write(&[
            (
                "app/Duck.toml",
                &library("json = { path = \"../json\" }\nxml = { path = \"../libs/xml\" }\n"),
            ),
            (
                "json/Duck.toml",
                &library("text = { path = \"../text\" }\n"),
            ),
            ("json/lib.duck", ""),
            (
                "libs/xml/Duck.toml",
                &library("t = { path = \"../../text/\" }\n"),
            ),
            ("libs/xml/lib.duck", ""),
            ("text/Duck.toml", LIBRARY),
            ("text/lib.duck", ""),
        ]);
        let packages = resolve(&root, &no_cache(&root)).unwrap();
        let root_text = root.display().to_string();
        assert_eq!(
            layout(&root, &packages),
            [
                (
                    "".to_string(),
                    vec![("json".to_string(), 1), ("xml".to_string(), 3)]
                ),
                ("../json".to_string(), vec![("text".to_string(), 2)]),
                ("../json/../text".to_string(), vec![]),
                ("../libs/xml".to_string(), vec![("t".to_string(), 2)]),
            ],
            "{root_text}"
        );
    }

    #[test]
    fn libraries_must_have_their_entry() {
        let dir = TempDir::new("no-entry");
        let root = dir.0.join("app");
        dir.write(&[
            ("app/Duck.toml", &library("util = { path = \"../util\" }\n")),
            ("util/Duck.toml", LIBRARY),
        ]);
        let error = resolve(&root, &no_cache(&root)).unwrap_err().to_string();
        let entry = root.join("../util/lib.duck");
        assert!(
            error.starts_with(&format!("cannot read {}: ", entry.display())),
            "{error}"
        );
    }

    #[test]
    fn dependencies_must_be_libraries() {
        let dir = TempDir::new("not-a-library");
        let root = dir.0.join("app");
        dir.write(&[
            ("app/Duck.toml", &library("tool = { path = \"../tool\" }\n")),
            (
                "tool/Duck.toml",
                "[module]\nentry = \"main.duck\"\noutput = \"out.wasm\"\n[memory]\nmin = \"1pgs\"\n",
            ),
        ]);
        let error = resolve(&root, &no_cache(&root)).unwrap_err().to_string();
        let tool = root.join("../tool");
        assert_eq!(
            error,
            format!("dependency `tool` at {} has no [library]", tool.display())
        );
    }

    #[test]
    fn missing_and_invalid_manifests() {
        let dir = TempDir::new("missing");
        let root = dir.0.join("app");
        dir.write(&[
            ("app/Duck.toml", &library("gone = { path = \"../gone\" }\n")),
            ("bad/Duck.toml", "[library]\n"),
        ]);
        let error = resolve(&root, &no_cache(&root)).unwrap_err().to_string();
        let gone = root.join("../gone").join(MANIFEST);
        assert!(
            error.starts_with(&format!("cannot read {}: ", gone.display())),
            "{error}"
        );

        dir.write(&[("app/Duck.toml", &library("bad = { path = \"../bad\" }\n"))]);
        let error = resolve(&root, &no_cache(&root)).unwrap_err().to_string();
        let bad = root.join("../bad").join(MANIFEST);
        assert!(
            error.starts_with(&format!("{}: ", bad.display()))
                && error.contains("missing field `entry`"),
            "{error}"
        );
    }

    #[test]
    fn packages_import_their_dependencies_by_name() {
        let dir = TempDir::new("import");
        let root = dir.0.join("app");
        dir.write(&[
            (
                "app/Duck.toml",
                &library("m = { path = \"../math\" }\nu = { path = \"../util\" }\n"),
            ),
            (
                "app/lib.duck",
                "import m\nimport u as util\npub fn f() -> i32:\n    return m.double(util.one)\n",
            ),
            ("math/Duck.toml", &library("util = { path = \"../util\" }\n")),
            (
                "math/lib.duck",
                "import util\npub fn double(x: i32) -> i32:\n    return x * util.two()\n",
            ),
            ("util/Duck.toml", LIBRARY),
            (
                "util/lib.duck",
                "import \"src/two.duck\" as consts\npub let one = 1\npub fn two() -> i32:\n    return consts.value\n",
            ),
            ("util/src/two.duck", "pub let value = 2\n"),
        ]);
        assert_eq!(check(&root), Ok(()));
    }

    #[test]
    fn dependency_names_are_local_to_their_package() {
        let dir = TempDir::new("local-names");
        let root = dir.0.join("app");
        dir.write(&[
            ("app/Duck.toml", &library("math = { path = \"../math\" }\n")),
            ("app/lib.duck", "import math\nimport util\n"),
            (
                "math/Duck.toml",
                &library("util = { path = \"../util\" }\n"),
            ),
            ("math/lib.duck", "import util\n"),
            ("util/Duck.toml", LIBRARY),
            ("util/lib.duck", ""),
        ]);
        assert_eq!(
            check(&root),
            Err(vec!["lib.duck: no dependency is named `util`".to_string()])
        );
    }

    #[test]
    fn files_of_other_packages_are_not_imported_by_path() {
        let dir = TempDir::new("outside");
        let root = dir.0.join("app");
        dir.write(&[
            ("app/Duck.toml", &library("util = { path = \"../util\" }\n")),
            ("app/lib.duck", "import \"../util/inner.duck\"\n"),
            ("util/Duck.toml", LIBRARY),
            ("util/lib.duck", ""),
            ("util/inner.duck", ""),
        ]);
        assert_eq!(
            check(&root),
            Err(vec![
                "lib.duck: `../util/inner.duck` is outside this package; import its package by name"
                    .to_string()
            ])
        );
    }

    #[test]
    fn git_dependencies_are_fetched_at_a_tag_once() {
        let dir = TempDir::new("git-tag");
        let root = dir.0.join("app");
        let remote = dir.0.join("remote/json");
        commit(
            &remote,
            &[("Duck.toml", LIBRARY), ("lib.duck", "pub let v = 1\n")],
            "v1",
        );
        let url = remote.display().to_string();
        dir.write(&[
            (
                "app/Duck.toml",
                &library(&format!("json = {{ git = \"{url}\", tag = \"v1\" }}\n")),
            ),
            ("app/lib.duck", "import json\nlet x: i32 = json.v\n"),
        ]);
        let cache = Cache::new(dir.0.join("cache"));
        assert_eq!(check_with(&root, &cache), Ok(()));

        // Tags are taken never to move, so once fetched the remote is never
        // asked again, even when the tag does move.
        commit(&remote, &[("lib.duck", "pub let w = 2\n")], "v1");
        assert_eq!(check_with(&root, &cache), Ok(()));
        fs::remove_dir_all(&remote).unwrap();
        assert_eq!(check_with(&root, &cache), Ok(()));
        let packages = resolve(&root, &cache).unwrap();
        let json = packages.iter().nth(1).unwrap();
        assert!(
            json.dir.starts_with(dir.0.join("cache")),
            "{}",
            json.dir.display()
        );
    }

    #[test]
    fn git_dependencies_at_a_rev_in_a_subdirectory() {
        let dir = TempDir::new("git-rev");
        let root = dir.0.join("app");
        let remote = dir.0.join("mono");
        let files = [
            ("libs/json/Duck.toml", LIBRARY),
            ("libs/json/lib.duck", "pub let v = 1\n"),
        ];
        let first = commit(&remote, &files, "v1");
        commit(&remote, &[("libs/json/lib.duck", "pub let w = 2\n")], "v2");
        let url = remote.display().to_string();
        for rev in [&first[..7], &first[..]] {
            dir.write(&[
                (
                    "app/Duck.toml",
                    &library(&format!(
                        "json = {{ git = \"{url}\", rev = \"{rev}\", path = \"libs/json\" }}\n"
                    )),
                ),
                ("app/lib.duck", "import json\nlet x: i32 = json.v\n"),
            ]);
            let cache = Cache::new(dir.0.join(format!("cache-{}", rev.len())));
            assert_eq!(check_with(&root, &cache), Ok(()), "{rev}");
        }
    }

    #[test]
    fn unknown_tags_and_repositories() {
        let dir = TempDir::new("git-unknown");
        let root = dir.0.join("app");
        let remote = dir.0.join("json");
        commit(&remote, &[("Duck.toml", LIBRARY), ("lib.duck", "")], "v1");
        let url = remote.display().to_string();
        dir.write(&[(
            "app/Duck.toml",
            &library(&format!("json = {{ git = \"{url}\", tag = \"v9\" }}\n")),
        )]);
        let cache = Cache::new(dir.0.join("cache"));
        assert_eq!(
            resolve(&root, &cache).unwrap_err().to_string(),
            format!("dependency `json`: {url} has no tag `v9`")
        );

        let gone = dir.0.join("gone").display().to_string();
        dir.write(&[(
            "app/Duck.toml",
            &library(&format!("json = {{ git = \"{gone}\", tag = \"v1\" }}\n")),
        )]);
        let error = resolve(&root, &cache).unwrap_err().to_string();
        assert!(
            error.starts_with("dependency `json`: `git fetch"),
            "{error}"
        );
    }

    #[test]
    fn a_repository_is_needed_at_one_commit() {
        let dir = TempDir::new("git-conflict");
        let root = dir.0.join("app");
        let remote = dir.0.join("util");
        let v1 = commit(&remote, &[("Duck.toml", LIBRARY), ("lib.duck", "")], "v1");
        let v2 = commit(&remote, &[], "v2");
        let url = remote.display().to_string();
        let util = |reference: &str| format!("util = {{ git = \"{url}\", {reference} }}\n");
        dir.write(&[
            (
                "app/Duck.toml",
                &library(
                    "a = { path = \"../a\" }\nb = { path = \"../b\" }\nc = { path = \"../c\" }\n",
                ),
            ),
            ("a/Duck.toml", &library(&util("tag = \"v1\""))),
            ("a/lib.duck", ""),
            (
                "b/Duck.toml",
                &library(&util(&format!("rev = \"{}\"", &v1[..10]))),
            ),
            ("b/lib.duck", ""),
            ("c/Duck.toml", &library(&util("tag = \"v2\""))),
            ("c/lib.duck", ""),
        ]);
        let cache = Cache::new(dir.0.join("cache"));
        assert_eq!(
            resolve(&root, &cache).unwrap_err().to_string(),
            format!(
                "{url} is needed at two commits: {} by a -> util, and {} by c -> util",
                &v1[..12],
                &v2[..12]
            )
        );

        // One commit, however it's named, is one package.
        dir.write(&[(
            "app/Duck.toml",
            &library("a = { path = \"../a\" }\nb = { path = \"../b\" }\n"),
        )]);
        let packages = resolve(&root, &cache).unwrap();
        assert_eq!(packages.iter().count(), 4);
    }
}

use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::time::SystemTime;

use duck_compiler::file::{
    FileId, FileManager, IncludeError, Included, Settings, TestModule, Wit, WitFile,
};
use duck_compiler::ty::Artifact;

use crate::package::{self, Packages};

/// What the file of a module is named after the module.
const EXTENSION: &str = "duck";

/// The directory of a package that holds its WIT, beside its manifest.
const WIT_DIR: &str = "wit";

/// The directory of [`WIT_DIR`] that holds the packages its WIT uses, each
/// a file or a directory of them.
const WIT_DEPS: &str = "deps";

/// What a WIT file is named after.
const WIT_EXTENSION: &str = "wit";

/// How far down a directory is looked in for the modules that make it one
/// that a `use` may lead through.
const MAX_DEPTH: usize = 8;

/// Source files on disk, read as they are opened, each in the package whose
/// module or dependency led to it.
#[derive(Debug, Clone)]
pub struct Files {
    /// Every opened file; the first is the entry point.
    files: Vec<File>,
    /// Each of those by its canonical path.
    by_canonical: HashMap<PathBuf, FileId>,
    /// The file that a module or a library at each path was opened as, or
    /// none if none could be: a path is read once in a build, however many
    /// `use`s lead along it.
    opened: HashMap<PathBuf, Option<FileId>>,
    /// Indexed like [`Packages`].
    packages: Vec<Package>,
    /// The test modules of the package being built, in order of their
    /// paths. None unless the files were given [its tests](Self::with_tests).
    tests: Vec<TestModule>,
    /// The directory those are named from, as reached from the working
    /// directory.
    test_root: Option<PathBuf>,
    settings: Settings,
    /// What was read of the files that were included.
    cache: IncludeCache,
    /// Each path that a file was asked for by to include, as it is written,
    /// whether or not a file is there.
    include_paths: Vec<String>,
    /// What names each package wherever it is compiled, by index, where
    /// something does: the hash of its source, as [`crate::artifacts`]
    /// keeps what it compiles to by.
    names: HashMap<usize, String>,
    /// What each package that is compiled already compiled to, by index.
    compiled: HashMap<usize, Rc<Artifact>>,
}

/// The files that `module.include` names, each as it was last read: one
/// that is as it was then is not read again. It is shared by what is cloned
/// of it, so the files of one build are read as those of the last were.
#[derive(Debug, Clone, Default)]
pub struct IncludeCache(Rc<RefCell<HashMap<PathBuf, Kept>>>);

/// A file as it was read to include, by its canonical path.
#[derive(Debug)]
struct Kept {
    /// When it was written and how long it was, if that is known: what
    /// tells whether it has been written since.
    written: Option<(SystemTime, u64)>,
    bytes: Rc<[u8]>,
    /// Whether it was included since [`IncludeCache::sweep`] last ran.
    used: bool,
}

#[derive(Debug, Clone)]
struct File {
    id: FileId,
    /// The path the file was reached by, relative to the working directory.
    path: PathBuf,
    /// Identifies the file however it was reached.
    canonical: PathBuf,
    contents: String,
    /// The index of its package.
    package: usize,
}

/// What files need of a package to open each other.
#[derive(Debug, Clone)]
struct Package {
    /// The directory holding its manifest, which the files it includes are
    /// named from, as reached from the working directory.
    dir: PathBuf,
    /// The directory its modules are named from, as reached from the working
    /// directory: the one holding the file the build enters the package by.
    root: PathBuf,
    /// The file other packages use, as reached from the working directory.
    library: Option<PathBuf>,
    /// The directory of its test modules, as reached from the working
    /// directory, if it has one: they are no part of the package as it is
    /// compiled whole.
    tests: Option<PathBuf>,
    /// The package each dependency is, by index.
    dependencies: Vec<(String, usize)>,
}

impl Files {
    /// The files of `packages`, starting at `entry_point`, a file of the first.
    pub fn new(
        packages: &Packages,
        entry_point: impl AsRef<Path>,
        settings: Settings,
    ) -> io::Result<Self> {
        Self::of(packages, 0, entry_point, settings)
    }

    /// The files of `packages`, starting at `entry_point`, a file of the
    /// package at `built`, which is the one being built.
    pub fn of(
        packages: &Packages,
        built: usize,
        entry_point: impl AsRef<Path>,
        settings: Settings,
    ) -> io::Result<Self> {
        let entry_point = entry_point.as_ref();
        let packages = packages.iter().enumerate().map(|(index, package)| {
            let library = package.manifest.library.as_ref();
            let library = library.map(|library| package.dir.join(&library.entry));
            // The package being built is entered by the entry point, and its
            // dependencies by their libraries.
            let entry = match index == built {
                true => Some(entry_point),
                false => library.as_deref(),
            };
            Package {
                dir: package.dir.clone(),
                root: (entry.and_then(Path::parent).unwrap_or(&package.dir)).to_path_buf(),
                library,
                tests: (package.manifest.tests.as_ref()).map(|tests| package.dir.join(tests)),
                dependencies: (package.dependencies.iter())
                    .map(|(name, id)| (name.clone(), *id))
                    .collect(),
            }
        });
        let mut files = Self {
            files: Vec::new(),
            by_canonical: HashMap::new(),
            opened: HashMap::new(),
            packages: packages.collect(),
            tests: Vec::new(),
            test_root: None,
            settings,
            cache: IncludeCache::default(),
            include_paths: Vec::new(),
            names: HashMap::new(),
            compiled: HashMap::new(),
        };
        files.read(entry_point.to_path_buf(), built)?;
        Ok(files)
    }

    /// Names the package at `index` `name` wherever it is compiled, and
    /// gives it what it compiled to, if it is compiled already: its files
    /// are then only opened, and nothing of it is compiled again.
    pub fn with_compiled(&mut self, index: usize, name: String, artifact: Option<Rc<Artifact>>) {
        self.names.insert(index, name);
        if let Some(artifact) = artifact {
            self.compiled.insert(index, artifact);
        }
    }

    /// The files with the tests of the package being built: each source
    /// file of its test directory `dir`, and of the directories that holds,
    /// as [`sources`] finds them, is a test module of the package, named by
    /// its path from `dir`. A directory that isn't there has none. Only
    /// files that are given them read anything of it.
    pub fn with_tests(mut self, dir: PathBuf) -> io::Result<Self> {
        let mut paths = Vec::new();
        if dir.is_dir() {
            sources(&dir, &mut paths)?;
        }
        for path in paths {
            let module = path.strip_prefix(&dir).unwrap_or(&path).with_extension("");
            let names = module
                .iter()
                .map(|name| name.to_string_lossy().into_owned());
            let test = TestModule {
                path: names.collect(),
                file: self.read(path, 0)?,
            };
            self.tests.push(test);
        }
        self.test_root = Some(dir);
        Ok(self)
    }

    /// The canonical path of an opened file.
    pub fn path(&self, id: FileId) -> &Path {
        &self.get(id).canonical
    }

    /// The opened file at the canonical path `path`, if one is.
    pub fn find(&self, path: &Path) -> Option<FileId> {
        self.by_canonical.get(path).copied()
    }

    /// Includes each file as `cache` last read it, where it is as it was
    /// then, rather than reading every one.
    pub fn reuse(&mut self, cache: &IncludeCache) {
        self.cache = cache.clone();
    }

    /// Each path that a `module.include` named a file by.
    pub fn include_paths(&self) -> &[String] {
        &self.include_paths
    }

    /// The names that the path of a `use` in the file `from` may go on
    /// with after `path`: the modules and the directories of modules that
    /// its package has there, and with no path yet, its dependencies too.
    pub fn children(&self, from: FileId, path: &[String]) -> Vec<String> {
        let package = &self.packages[self.get(from).package];
        let mut dir = package.root.clone();
        dir.extend(path);
        let mut names = Vec::new();
        for entry in fs::read_dir(dir).into_iter().flatten().flatten() {
            let entry = entry.path();
            let named = match entry.is_dir() {
                true => holds_modules(&entry, MAX_DEPTH),
                false => is_module(&entry),
            };
            if let Some(name) = entry.file_stem().and_then(|name| name.to_str())
                && named
                && !names.iter().any(|known| known == name)
            {
                names.push(name.to_string());
            }
        }
        if path.is_empty() {
            names.extend(package.dependencies.iter().map(|(name, _)| name.clone()));
        }
        names.sort();
        names
    }

    /// Reads the file at `path`, of package `package` unless it has been
    /// read already.
    fn read(&mut self, path: PathBuf, package: usize) -> io::Result<FileId> {
        let canonical = fs::canonicalize(&path)?;
        if let Some(id) = self.find(&canonical) {
            return Ok(id);
        }
        let id = Self::mint_file_id(self.files.len());
        let contents = fs::read_to_string(&canonical)?;
        self.by_canonical.insert(canonical.clone(), id);
        self.files.push(File {
            id,
            path,
            canonical,
            contents,
            package,
        });
        Ok(id)
    }

    /// Opens the file at `path`, of package `package`, as [`Self::read`]
    /// does, but only the first time it is asked for.
    fn open_path(&mut self, path: PathBuf, package: usize) -> Option<FileId> {
        if let Some(opened) = self.opened.get(&path) {
            return *opened;
        }
        let opened = self.read(path.clone(), package).ok();
        self.opened.insert(path, opened);
        opened
    }

    fn get(&self, id: FileId) -> &File {
        let file = self.files.iter().find(|f| f.id == id);
        file.unwrap_or_else(|| panic!("Invalid file id: {id:?}"))
    }
}

impl IncludeCache {
    /// The bytes of the file at the canonical path `file`, as they were
    /// last read if it hasn't been written since.
    fn read(&self, file: &Path) -> Included {
        let metadata = fs::metadata(file).map_err(unreadable)?;
        // What is no file may have no end to read to.
        if !metadata.is_file() {
            let reason = match metadata.is_dir() {
                true => "it is a directory",
                false => "it is not a file",
            };
            return Err(IncludeError::NotFound(reason.to_string()));
        }
        let written = metadata.modified().ok().map(|at| (at, metadata.len()));
        let mut kept = self.0.borrow_mut();
        if let Some(kept) = kept.get_mut(file)
            && written.is_some()
            && kept.written == written
        {
            kept.used = true;
            return Ok(kept.bytes.clone());
        }
        let bytes: Rc<[u8]> = fs::read(file).map_err(unreadable)?.into();
        let read = Kept {
            written,
            bytes: bytes.clone(),
            used: true,
        };
        kept.insert(file.to_path_buf(), read);
        Ok(bytes)
    }

    /// Forgets each file that wasn't included since this last ran: nothing
    /// includes it any longer.
    pub fn sweep(&self) {
        let mut kept = self.0.borrow_mut();
        kept.retain(|_, kept| std::mem::take(&mut kept.used));
    }
}

/// Why a file that `error` says can't be read isn't included.
fn unreadable(error: io::Error) -> IncludeError {
    IncludeError::NotFound(match error.kind() {
        io::ErrorKind::NotFound => "no such file".to_string(),
        _ => error.to_string(),
    })
}

/// Whether the file at `path` is one that a module is named after.
fn is_module(path: &Path) -> bool {
    path.extension().is_some_and(|e| e == EXTENSION) && path.is_file()
}

/// Whether the directory `dir` holds a module, in it or in the directories
/// it holds, down to `depth` of them. A hidden directory holds none.
fn holds_modules(dir: &Path, depth: usize) -> bool {
    let hidden = (dir.file_name()).is_some_and(|name| name.as_encoded_bytes().starts_with(b"."));
    let mut entries = fs::read_dir(dir).into_iter().flatten().flatten();
    !hidden
        && entries.any(|entry| {
            let path = entry.path();
            is_module(&path) || depth > 0 && path.is_dir() && holds_modules(&path, depth - 1)
        })
}

/// Adds the source file at `path` to `sources`, or every source file in the
/// directory there and in those it holds, in order of their names. A file in
/// a directory is a source file for being named after a module, and a hidden
/// directory holds none. No path at all is the working directory.
pub fn sources(path: &Path, sources: &mut Vec<PathBuf>) -> io::Result<()> {
    let dir = match path.as_os_str().is_empty() {
        true => Path::new("."),
        false => path,
    };
    if !fs::metadata(dir)?.is_dir() {
        sources.push(path.to_path_buf());
        return Ok(());
    }
    let mut entries = fs::read_dir(dir)?.collect::<io::Result<Vec<_>>>()?;
    entries.sort_by_key(fs::DirEntry::file_name);
    for entry in entries {
        let path = path.join(entry.file_name());
        let hidden = entry.file_name().as_encoded_bytes().starts_with(b".");
        let kind = entry.file_type()?;
        if kind.is_dir() && !hidden {
            self::sources(&path, sources)?;
        } else if kind.is_file() && path.extension().is_some_and(|e| e == EXTENSION) {
            sources.push(path);
        }
    }
    Ok(())
}

/// The WIT of `packages`: that of the package being built, which has its
/// worlds, and as packages for it to use, that of each package it depends
/// on, with what each of them uses. So the WIT a library needs is the
/// library's own to have.
pub fn wit(packages: &Packages) -> io::Result<Wit> {
    wit_of(packages, 0)
}

/// The WIT of the package at `built` of `packages`, as [`wit`] gives that
/// of the first: the one being built.
pub fn wit_of(packages: &Packages, built: usize) -> io::Result<Wit> {
    let own = packages
        .iter()
        .nth(built)
        .expect("the package is among them");
    let mut wit = wit_in(&own.dir)?;
    for (index, package) in packages.iter().enumerate() {
        if index == built {
            continue;
        }
        let Wit { package, deps } = wit_in(&package.dir)?;
        wit.deps
            .extend(Some(package).filter(|files| !files.is_empty()));
        wit.deps.extend(deps);
    }
    Ok(wit)
}

/// The WIT of the package in `dir`: the files of its [`WIT_DIR`], and those
/// of each package under [`WIT_DEPS`] there, in order of their names. A
/// package without the directory has none.
pub(crate) fn wit_in(dir: &Path) -> io::Result<Wit> {
    let dir = dir.join(WIT_DIR);
    if !dir.is_dir() {
        return Ok(Wit::default());
    }
    let mut deps = Vec::new();
    let deps_dir = dir.join(WIT_DEPS);
    if deps_dir.is_dir() {
        let mut entries = fs::read_dir(&deps_dir)?.collect::<io::Result<Vec<_>>>()?;
        entries.sort_by_key(fs::DirEntry::file_name);
        for entry in entries {
            let path = entry.path();
            let files = match path.is_dir() {
                true => wit_files(&path)?,
                false => wit_file(&path)?.into_iter().collect(),
            };
            if !files.is_empty() {
                deps.push(files);
            }
        }
    }
    Ok(Wit {
        package: wit_files(&dir)?,
        deps,
    })
}

/// The WIT files in the directory `dir`, in order of their names.
fn wit_files(dir: &Path) -> io::Result<Vec<WitFile>> {
    let mut entries = fs::read_dir(dir)?.collect::<io::Result<Vec<_>>>()?;
    entries.sort_by_key(fs::DirEntry::file_name);
    let mut files = Vec::new();
    for entry in entries {
        files.extend(wit_file(&entry.path())?);
    }
    Ok(files)
}

/// The file at `path`, if it is a WIT file.
fn wit_file(path: &Path) -> io::Result<Option<WitFile>> {
    if !path.is_file() || path.extension().is_none_or(|e| e != WIT_EXTENSION) {
        return Ok(None);
    }
    Ok(Some(WitFile {
        path: path.display().to_string(),
        contents: fs::read_to_string(path)?,
    }))
}

impl FileManager for Files {
    fn entry_point(&mut self) -> FileId {
        self.files[0].id
    }

    fn display_name(&mut self, id: FileId) -> String {
        self.get(id).path.display().to_string()
    }

    fn contents(&mut self, id: FileId) -> String {
        self.get(id).contents.clone()
    }

    fn open(&mut self, from: FileId, path: &[&str]) -> Option<FileId> {
        let package = self.get(from).package;
        let (name, dirs) = path.split_last()?;
        let mut file = self.packages[package].root.clone();
        file.extend(dirs);
        file.push(format!("{name}.{EXTENSION}"));
        self.open_path(file, package)
    }

    fn open_package(&mut self, from: FileId, name: &str) -> Option<FileId> {
        let dependencies = &self.packages[self.get(from).package].dependencies;
        let (_, package) = dependencies.iter().find(|(dep, _)| dep == name)?;
        let package = *package;
        let library = self.packages[package].library.clone()?;
        self.open_path(library, package)
    }

    fn package_name(&mut self, root: FileId) -> String {
        let package = self.get(root).package;
        match self.names.get(&package) {
            Some(name) => name.clone(),
            None => self.display_name(root),
        }
    }

    fn module_path(&mut self, file: FileId) -> Vec<String> {
        let file = self.get(file);
        let root = &self.packages[file.package].root;
        let path = file.path.strip_prefix(root).unwrap_or(&file.path);
        let path = path.with_extension("");
        path.iter()
            .map(|name| name.to_string_lossy().into_owned())
            .collect()
    }

    fn compiled(&mut self, library: FileId) -> Option<Rc<Artifact>> {
        let package = self.get(library).package;
        self.compiled.get(&package).cloned()
    }

    fn package_files(&mut self, library: FileId) -> Vec<FileId> {
        let package = self.get(library).package;
        let Package { root, tests, .. } = self.packages[package].clone();
        let mut paths = Vec::new();
        if sources(&root, &mut paths).is_err() {
            return Vec::new();
        }
        let sources = paths.into_iter().filter(|path| {
            let tested = tests.as_ref().is_some_and(|tests| path.starts_with(tests));
            !tested
        });
        sources
            .filter_map(|path| self.open_path(path, package))
            .collect()
    }

    fn tests(&mut self) -> Vec<TestModule> {
        self.tests.clone()
    }

    fn open_test(&mut self, from: FileId, path: &[&str]) -> Option<FileId> {
        if !self.tests.iter().any(|test| test.file == from) {
            return None;
        }
        let (name, dirs) = path.split_last()?;
        let mut file = self.test_root.clone()?;
        file.extend(dirs);
        file.push(format!("{name}.{EXTENSION}"));
        // Every file of the directory was read as the tests were given.
        let found = self.find(&fs::canonicalize(file).ok()?)?;
        self.tests
            .iter()
            .any(|test| test.file == found)
            .then_some(found)
    }

    fn include(&mut self, from: FileId, path: &str) -> Included {
        let dir = &self.packages[self.get(from).package].dir;
        let dir = package::canonical_dir(dir).map_err(unreadable)?;
        if !self.include_paths.iter().any(|asked| asked == path) {
            self.include_paths.push(path.to_string());
        }
        // A link may lead out of the package, which no path does.
        let file = fs::canonicalize(dir.join(path)).map_err(unreadable)?;
        if !file.starts_with(dir) {
            return Err(IncludeError::Outside);
        }
        self.cache.read(&file)
    }

    fn settings(&mut self) -> Settings {
        self.settings.clone()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sources_are_the_duck_files_of_a_directory() {
        let dir = std::env::temp_dir().join(format!("duck-sources-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        let files = [
            "src/main.duck",
            "src/util/geo.duck",
            "src/notes.md",
            "lib.duck",
            ".git/hook.duck",
        ];
        for file in files {
            let path = dir.join(file);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, "").unwrap();
        }

        let mut found = Vec::new();
        let all = sources(&dir, &mut found);
        // A file that is named is one whatever its name.
        let named = sources(&dir.join("src/notes.md"), &mut found);
        let missing = sources(&dir.join("missing.duck"), &mut found);
        fs::remove_dir_all(&dir).unwrap();

        assert!(all.is_ok() && named.is_ok());
        assert_eq!(missing.unwrap_err().kind(), io::ErrorKind::NotFound);
        let expected = [
            "lib.duck",
            "src/main.duck",
            "src/util/geo.duck",
            "src/notes.md",
        ];
        assert_eq!(found, expected.map(|file| dir.join(file)));
    }

    #[test]
    fn wit_is_the_wit_files_of_a_package_and_of_those_it_uses() {
        let dir = std::env::temp_dir().join(format!("duck-wit-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        let files = [
            "wit/world.wit",
            "wit/api.wit",
            "wit/notes.md",
            "wit/deps/math/math.wit",
            "wit/deps/math/more.wit",
            "wit/deps/single.wit",
            "wit/deps/empty/readme.md",
            "src/main.duck",
        ];
        for file in files {
            let path = dir.join(file);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, file).unwrap();
        }

        let found = wit_in(&dir);
        let none = wit_in(&dir.join("src"));
        fs::remove_dir_all(&dir).unwrap();

        let named = |files: &[&str]| -> Vec<_> {
            let file = |file: &&str| WitFile {
                path: dir.join(file).display().to_string(),
                contents: file.to_string(),
            };
            files.iter().map(file).collect()
        };
        let expected = Wit {
            package: named(&["wit/api.wit", "wit/world.wit"]),
            deps: vec![
                named(&["wit/deps/math/math.wit", "wit/deps/math/more.wit"]),
                named(&["wit/deps/single.wit"]),
            ],
        };
        assert_eq!(found.unwrap(), expected);
        // A package without the directory has no WIT of its own.
        assert_eq!(none.unwrap(), Wit::default());
    }
}

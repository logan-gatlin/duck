use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use duck_compiler::file::{FileId, FileManager, Settings, Wit, WitFile};

use crate::package::Packages;

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
    /// Indexed like [`Packages`].
    packages: Vec<Package>,
    settings: Settings,
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
    /// The directory its modules are named from, as reached from the working
    /// directory: the one holding the file the build enters the package by.
    root: PathBuf,
    /// The file other packages use, as reached from the working directory.
    library: Option<PathBuf>,
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
        let entry_point = entry_point.as_ref();
        let packages = packages.iter().enumerate().map(|(index, package)| {
            let library = package.manifest.library.as_ref();
            let library = library.map(|library| package.dir.join(&library.entry));
            // The package being built is entered by the entry point, and its
            // dependencies by their libraries.
            let entry = match index {
                0 => Some(entry_point),
                _ => library.as_deref(),
            };
            Package {
                root: (entry.and_then(Path::parent).unwrap_or(&package.dir)).to_path_buf(),
                library,
                dependencies: (package.dependencies.iter())
                    .map(|(name, id)| (name.clone(), *id))
                    .collect(),
            }
        });
        let mut files = Self {
            files: Vec::new(),
            packages: packages.collect(),
            settings,
        };
        files.read(entry_point.to_path_buf(), 0)?;
        Ok(files)
    }

    /// The canonical path of an opened file.
    pub fn path(&self, id: FileId) -> &Path {
        &self.get(id).canonical
    }

    /// The opened file at the canonical path `path`, if one is.
    pub fn find(&self, path: &Path) -> Option<FileId> {
        let file = self.files.iter().find(|f| f.canonical == path)?;
        Some(file.id)
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
        self.read_canonical(path, canonical, package)
    }

    fn read_canonical(
        &mut self,
        path: PathBuf,
        canonical: PathBuf,
        package: usize,
    ) -> io::Result<FileId> {
        if let Some(file) = self.files.iter().find(|f| f.canonical == canonical) {
            return Ok(file.id);
        }
        let id = Self::mint_file_id(self.files.len());
        let contents = fs::read_to_string(&canonical)?;
        self.files.push(File {
            id,
            path,
            canonical,
            contents,
            package,
        });
        Ok(id)
    }

    fn get(&self, id: FileId) -> &File {
        let file = self.files.iter().find(|f| f.id == id);
        file.unwrap_or_else(|| panic!("Invalid file id: {id:?}"))
    }
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

/// The WIT of the package in `dir`: the files of its [`WIT_DIR`], and those
/// of each package under [`WIT_DEPS`] there, in order of their names. A
/// package without the directory has none.
pub fn wit(dir: &Path) -> io::Result<Wit> {
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
        self.read(file, package).ok()
    }

    fn open_package(&mut self, from: FileId, name: &str) -> Option<FileId> {
        let dependencies = &self.packages[self.get(from).package].dependencies;
        let (_, package) = dependencies.iter().find(|(dep, _)| dep == name)?;
        let package = *package;
        let library = self.packages[package].library.clone()?;
        self.read(library, package).ok()
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

        let found = wit(&dir);
        let none = wit(&dir.join("src"));
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

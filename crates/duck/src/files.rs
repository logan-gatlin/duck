use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use duck_compiler::file::{FileId, FileManager, Settings};

use crate::package::Packages;

/// What the file of a module is named after the module.
const EXTENSION: &str = "duck";

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

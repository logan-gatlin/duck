use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use duck_compiler::file::{FileId, FileManager, OpenError, Settings};

use crate::package::{Packages, canonical_dir};

/// Source files on disk, read as they are opened, each in the package whose
/// directory holds it.
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
    /// The canonical path of the directory holding every file of the package.
    dir: PathBuf,
    /// The file other packages import, as reached from the working directory.
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
        let packages = packages
            .iter()
            .map(|package| {
                Ok(Package {
                    dir: canonical_dir(&package.dir)?,
                    library: (package.manifest.library.as_ref())
                        .map(|library| package.dir.join(&library.entry)),
                    dependencies: (package.dependencies.iter())
                        .map(|(name, id)| (name.clone(), *id))
                        .collect(),
                })
            })
            .collect::<io::Result<_>>()?;
        let mut files = Self {
            files: Vec::new(),
            packages,
            settings,
        };
        files.read(entry_point.as_ref().to_path_buf(), 0)?;
        Ok(files)
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

    fn open(&mut self, from: FileId, path: &str) -> Result<FileId, OpenError> {
        let from = self.get(from);
        let package = from.package;
        let path = from.path.parent().unwrap_or(Path::new("")).join(path);
        let canonical = fs::canonicalize(&path).map_err(|_| OpenError::NotFound)?;
        if !canonical.starts_with(&self.packages[package].dir) {
            return Err(OpenError::OutsidePackage);
        }
        (self.read_canonical(path, canonical, package)).map_err(|_| OpenError::NotFound)
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

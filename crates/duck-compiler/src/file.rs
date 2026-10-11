use std::collections::HashMap;
use std::rc::Rc;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub struct FileId(usize);

pub trait FileManager {
    /// Returns the entry point file (main.duck)
    fn entry_point(&mut self) -> FileId;
    /// Identifiable name of a file id
    fn display_name(&mut self, id: FileId) -> String;
    /// Get the contents of a file
    fn contents(&mut self, id: FileId) -> String;
    /// Attempt to open the module `path` names from the root of the package
    /// that the file `from` is in: `a/b.duck` for `["a", "b"]`. Deduplicates
    /// with already opened files, so every path to the same file gives the
    /// same id
    fn open(&mut self, from: FileId, path: &[&str]) -> Option<FileId>;
    /// Attempt to open the library of the dependency `name` of the package
    /// that the file `from` is in. Returns `None` when there is no such
    /// dependency
    fn open_package(&mut self, from: FileId, name: &str) -> Option<FileId>;
    /// Attempt to read the file that a `module.include` in the file `from`
    /// names by `path`, from the directory of the package `from` is in.
    /// `path` is one that [`include_path`] gives. Nothing is included
    /// without a file manager that reads what isn't source
    fn include(&mut self, _from: FileId, _path: &str) -> Included {
        Err(IncludeError::unread())
    }
    /// How to compile the module the files make up
    fn settings(&mut self) -> Settings;

    fn mint_file_id(id: usize) -> FileId {
        FileId(id)
    }
}

/// The bytes of a file that a `module.include` names, or why it has none.
pub type Included = Result<Rc<[u8]>, IncludeError>;

/// What each `module.include` of a program includes, by the module it is in
/// and the path it names.
pub type Includes = HashMap<(FileId, String), Included>;

/// Why a `module.include` includes nothing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IncludeError {
    /// Its path doesn't keep to the package: it isn't the names from the
    /// directory of the package down to a file, with a `/` between them, or
    /// it is of a file that a link takes elsewhere.
    Outside,
    /// Its file can't be read, for the reason this gives: there is none, or
    /// it is a directory.
    NotFound(String),
}

/// Module-wide choices that aren't written in any source file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Settings {
    /// The most pages memory may grow to, of 64 KiB each. `None` lets it
    /// grow without limit.
    pub max_pages: Option<u64>,
    /// The address literals are placed from. Memory starts with the pages
    /// below it, which hold no literal.
    pub static_start: u64,
    /// The function the module runs when it is instantiated, which takes no
    /// arguments and returns nothing.
    pub start: Option<String>,
    /// The fuel that the code run to evaluate the constants of one item has.
    /// `None` is [`crate::ty::DEFAULT_FUEL`].
    pub fuel: Option<u64>,
    /// The world the files are built as a component of, as
    /// [`crate::world::COMMAND`] names one. `None` for a library, which is
    /// built into the components that use it, and checked as one of no
    /// world.
    pub world: Option<String>,
    /// The WIT of the package, beside that of WASI 0.3, which is always
    /// there.
    pub wit: Wit,
    /// The bytes of the return area, which holds what a function passes
    /// the host in memory. `None` is as many as the most that one passes.
    pub return_area: Option<u32>,
}

/// The WIT a package has of its own: its `wit` directory.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Wit {
    /// The files of the package that has its worlds. None if it has no WIT.
    pub package: Vec<WitFile>,
    /// The files of each package those use, in any order.
    pub deps: Vec<Vec<WitFile>>,
}

/// One file of a WIT package.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WitFile {
    /// Where it is, for errors to name.
    pub path: String,
    pub contents: String,
}

impl IncludeError {
    /// Why nothing is included where no file is read for it.
    pub(crate) fn unread() -> Self {
        Self::NotFound("no file is read here".to_string())
    }
}

/// `path` as a `module.include` may write it: the names from the directory
/// of its package down to a file, with a `/` between them. None is empty,
/// `.` or `..`, and none has a `\`, so a file has the one path, which is
/// the same wherever the package is built.
pub fn include_path(path: &str) -> Result<&str, IncludeError> {
    let named = |name: &str| !matches!(name, "" | "." | "..") && !name.contains('\\');
    match path.split('/').all(named) {
        true => Ok(path),
        false => Err(IncludeError::Outside),
    }
}

#[cfg(test)]
pub(crate) struct DummyManager;

#[cfg(test)]
impl DummyManager {
    pub fn new() -> Self {
        Self
    }
}

#[cfg(test)]
fn guard<T>(file_id: FileId, out: T) -> T {
    if file_id == FileId(0) {
        out
    } else {
        panic!("Invalid file id: {file_id:?}")
    }
}

#[cfg(test)]
impl FileManager for DummyManager {
    fn entry_point(&mut self) -> FileId {
        FileId(0)
    }

    fn display_name(&mut self, id: FileId) -> String {
        guard(id, "example.duck".to_string())
    }

    fn contents(&mut self, id: FileId) -> String {
        guard(id, include_str!("../example.duck").to_string())
    }

    fn open(&mut self, _from: FileId, _path: &[&str]) -> Option<FileId> {
        None
    }

    fn open_package(&mut self, _from: FileId, _name: &str) -> Option<FileId> {
        None
    }

    fn settings(&mut self) -> Settings {
        Settings::default()
    }
}

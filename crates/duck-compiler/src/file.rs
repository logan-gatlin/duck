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
    /// How to compile the module the files make up
    fn settings(&mut self) -> Settings;

    fn mint_file_id(id: usize) -> FileId {
        FileId(id)
    }
}

/// Module-wide choices that aren't written in any source file.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Settings {
    pub memory: MemoryLimits,
    /// Whether an address is 64 bits wide rather than 32, as the memory's
    /// and the table's then are, and with them every pointer, function
    /// pointer, `int` and `uint`.
    pub memory64: bool,
    /// `None` places literals from address 0, in a section that ends where
    /// they do.
    pub static_section: Option<StaticSection>,
    /// The function the module runs when it is instantiated, which takes no
    /// arguments and returns nothing.
    pub start: Option<String>,
    /// The fuel that the code run to evaluate the constants of one item has.
    /// `None` is [`crate::ty::DEFAULT_FUEL`].
    pub fuel: Option<u64>,
}

/// Sizes of the module's linear memory, in 64 KiB pages.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MemoryLimits {
    /// `None` starts the memory with the fewest pages that hold the static
    /// data section.
    pub min_pages: Option<u64>,
    /// `None` lets the memory grow without limit.
    pub max_pages: Option<u64>,
}

/// The addresses `start..end` that literals are placed in, from `start` up.
/// `start` is at most `end`.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct StaticSection {
    pub start: u64,
    pub end: u64,
}

pub(crate) struct DummyManager;

impl DummyManager {
    pub fn new() -> Self {
        Self
    }
}

fn guard<T>(file_id: FileId, out: T) -> T {
    if file_id == FileId(0) {
        out
    } else {
        panic!("Invalid file id: {file_id:?}")
    }
}

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

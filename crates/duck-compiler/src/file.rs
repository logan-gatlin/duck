#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(usize);

pub trait FileManager {
    /// Returns the entry point file (main.duck)
    fn entry_point(&mut self) -> FileId;
    /// Identifiable name of a file id
    fn display_name(&mut self, id: FileId) -> String;
    /// Get the contents of a file
    fn contents(&mut self, id: FileId) -> String;
    /// Attempt to open a file by pathname. Deduplicates with already opened
    /// files. Returns `None` when no file is found
    fn open(&mut self, _path: &str) -> Option<FileId>;

    fn mint_file_id(id: usize) -> FileId {
        FileId(id)
    }
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

    fn open(&mut self, _path: &str) -> Option<FileId> {
        None
    }
}

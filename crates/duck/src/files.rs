use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use duck_compiler::file::{FileId, FileManager, Settings};

/// Source files on disk, read as they are opened.
#[derive(Debug, Clone)]
pub struct Files {
    /// Every opened file; the first is the entry point.
    files: Vec<File>,
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
}

impl Files {
    pub fn new(entry_point: impl AsRef<Path>, settings: Settings) -> io::Result<Self> {
        let mut files = Self {
            files: Vec::new(),
            settings,
        };
        files.read(entry_point.as_ref().to_path_buf())?;
        Ok(files)
    }

    fn read(&mut self, path: PathBuf) -> io::Result<FileId> {
        let canonical = fs::canonicalize(&path)?;
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

    fn open(&mut self, from: FileId, path: &str) -> Option<FileId> {
        let dir = self.get(from).path.parent().unwrap_or(Path::new(""));
        self.read(dir.join(path)).ok()
    }

    fn settings(&mut self) -> Settings {
        self.settings.clone()
    }
}

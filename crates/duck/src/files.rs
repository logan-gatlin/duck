use duck_compiler::file::FileManager;

#[derive(Debug, Clone)]
pub struct Files {
    main: String,
}

impl Files {
    pub fn new() -> Self {
        let main = std::fs::read_to_string("main.duck").unwrap();
        Self { main }
    }
}

impl FileManager for Files {
    fn entry_point(&mut self) -> duck_compiler::file::FileId {
        Self::mint_file_id(0)
    }

    fn display_name(&mut self, id: duck_compiler::file::FileId) -> String {
        if id == self.entry_point() {
            "main.duck".into()
        } else {
            panic!()
        }
    }

    fn contents(&mut self, id: duck_compiler::file::FileId) -> String {
        if id == self.entry_point() {
            self.main.clone()
        } else {
            panic!()
        }
    }

    fn open(&mut self, _path: &str) -> Option<duck_compiler::file::FileId> {
        panic!()
    }
}

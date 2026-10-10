//! `duck agents`: an overview of the language for coding agents.

/// The overview, in Markdown. Every ```duck block in it compiles on its own,
/// and is formatted.
pub const OVERVIEW: &str = include_str!("agents.md");

#[cfg(test)]
mod tests {
    use duck_compiler::file::{FileId, FileManager, Settings};

    use super::*;

    /// One file, which uses nothing.
    struct Single(&'static str);

    impl FileManager for Single {
        fn entry_point(&mut self) -> FileId {
            Self::mint_file_id(0)
        }

        fn display_name(&mut self, _id: FileId) -> String {
            "agents.md".to_string()
        }

        fn contents(&mut self, _id: FileId) -> String {
            self.0.to_string()
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

    /// The contents of every ```duck block in `markdown`.
    fn duck_blocks(markdown: &'static str) -> Vec<&'static str> {
        let mut blocks = Vec::new();
        let mut rest = markdown;
        while let Some(start) = rest.find("\n```duck\n") {
            let body = &rest[start + "\n```duck\n".len()..];
            let end = body.find("\n```").expect("unclosed code block");
            blocks.push(&body[..=end]);
            rest = &body[end..];
        }
        blocks
    }

    #[test]
    fn examples_compile() {
        let blocks = duck_blocks(OVERVIEW);
        assert!(blocks.len() > 5, "found {} blocks", blocks.len());
        for block in blocks {
            if let Err(errors) = duck_compiler::check(&mut Single(block)) {
                let errors: Vec<_> = errors.iter().map(ToString::to_string).collect();
                panic!("{block}\n{errors:#?}");
            }
        }
    }

    #[test]
    fn examples_are_formatted() {
        for block in duck_blocks(OVERVIEW) {
            assert_eq!(duck_compiler::format::format(block).as_deref(), Ok(block));
        }
    }
}

//! `duck agents`: an overview of the language for coding agents.

/// The overview, in Markdown. Every ```duck block in it compiles on its own,
/// and is formatted.
pub const OVERVIEW: &str = include_str!("agents.md");

#[cfg(test)]
mod tests {
    use duck_compiler::file::{FileId, FileManager, Settings, Wit, WitFile};

    use super::*;

    /// One file, which uses nothing.
    struct Single(&'static str, Settings);

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
            self.1.clone()
        }
    }

    /// The contents of the ```wit block in `markdown`, which has one.
    fn wit_block(markdown: &'static str) -> &'static str {
        let (_, body) = markdown.split_once("\n```wit\n").expect("a WIT block");
        let (body, _) = body.split_once("\n```").expect("unclosed code block");
        body
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
        // The example of a world is a component of the world beside it.
        let file = WitFile {
            path: "agents.wit".to_string(),
            contents: wit_block(OVERVIEW).to_string(),
        };
        let app = Settings {
            world: Some("app".to_string()),
            wit: Wit {
                package: vec![file],
                deps: Vec::new(),
            },
            ..Settings::default()
        };
        let mut worlds = 0;
        for block in blocks {
            let checked = match block.contains("\npub \"") {
                true => {
                    worlds += 1;
                    duck_compiler::compile(&mut Single(block, app.clone())).map(|_| ())
                }
                false => duck_compiler::check(&mut Single(block, Settings::default())),
            };
            if let Err(errors) = checked {
                let errors: Vec<_> = errors.iter().map(ToString::to_string).collect();
                panic!("{block}\n{errors:#?}");
            }
        }
        assert_eq!(worlds, 1);
    }

    #[test]
    fn examples_are_formatted() {
        for block in duck_blocks(OVERVIEW) {
            assert_eq!(duck_compiler::format::format(block).as_deref(), Ok(block));
        }
    }
}

//! Gathers a program from its entry point and every file it imports.

use std::collections::HashSet;
use std::fmt;

use crate::Error;
use crate::file::{FileId, FileManager};
use crate::lex::{self, Span};
use crate::parse::{self, Item, ItemKind, Module};

#[derive(Debug, Clone, PartialEq)]
pub struct ImportError {
    pub kind: ImportErrorKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ImportErrorKind {
    /// No file was found at the path.
    NotFound(String),
    /// A file that is already part of the program, including one that is
    /// being imported by one of its own imports.
    Duplicate(String),
}

struct Loader<'f, F> {
    files: &'f mut F,
    /// Every file that has been imported, and the entry point.
    loaded: HashSet<FileId>,
    items: Vec<Item>,
    errors: Vec<Error>,
}

impl fmt::Display for ImportErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFound(path) => write!(f, "cannot find `{path}`"),
            Self::Duplicate(path) => write!(f, "`{path}` is already imported"),
        }
    }
}

impl fmt::Display for ImportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}..{}", self.kind, self.span.start, self.span.end)
    }
}

impl std::error::Error for ImportError {}

/// Lexes and parses the entry point of `files`, replacing each `import` with
/// the items of the file it names, recursively. Items keep the spans of the
/// file they are written in.
///
/// Each file is loaded once; importing it again is an error at that
/// `import`. Errors in one file don't stop the others from loading, but the
/// imports of a file that fails to lex or parse are not followed.
pub fn load(files: &mut impl FileManager) -> Result<Module, Vec<Error>> {
    let entry = files.entry_point();
    let mut loader = Loader {
        files,
        loaded: HashSet::from([entry]),
        items: Vec::new(),
        errors: Vec::new(),
    };
    loader.file(entry);
    if loader.errors.is_empty() {
        Ok(Module {
            items: loader.items,
        })
    } else {
        Err(loader.errors)
    }
}

impl<F: FileManager> Loader<'_, F> {
    fn file(&mut self, id: FileId) {
        let src = self.files.contents(id);
        let tokens = match lex::tokenize(id, &src) {
            Ok(tokens) => tokens,
            Err(e) => return self.errors.push(Error::Lex(e)),
        };
        let module = match parse::parse(&tokens) {
            Ok(module) => module,
            Err(errors) => return self.errors.extend(errors.into_iter().map(Error::Parse)),
        };
        for item in module.items {
            match &item.kind {
                ItemKind::Import(path) => self.import(id, path, item.span),
                _ => self.items.push(item),
            }
        }
    }

    fn import(&mut self, from: FileId, path: &str, span: Span) {
        let kind = match self.files.open(from, path) {
            None => ImportErrorKind::NotFound(path.to_string()),
            Some(id) if !self.loaded.insert(id) => ImportErrorKind::Duplicate(path.to_string()),
            Some(id) => return self.file(id),
        };
        self.errors.push(Error::Import(ImportError { kind, span }));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::Settings;
    use crate::ir::Const;
    use crate::lex::TokenKind;
    use crate::parse::ParseErrorKind;
    use crate::ty;

    /// Files named by the paths that import them; the first is the entry
    /// point.
    struct Memory(Vec<(&'static str, &'static str)>);

    impl Memory {
        fn index(&self, id: FileId) -> usize {
            (0..self.0.len())
                .find(|&i| Self::mint_file_id(i) == id)
                .unwrap()
        }

        fn id(&self, name: &str) -> FileId {
            Self::mint_file_id(self.0.iter().position(|f| f.0 == name).unwrap())
        }

        /// The source text that `span` covers.
        fn text(&self, span: Span) -> &'static str {
            &self.0[self.index(span.file)].1[span.start..span.end]
        }
    }

    impl FileManager for Memory {
        fn entry_point(&mut self) -> FileId {
            Self::mint_file_id(0)
        }

        fn display_name(&mut self, id: FileId) -> String {
            self.0[self.index(id)].0.to_string()
        }

        fn contents(&mut self, id: FileId) -> String {
            self.0[self.index(id)].1.to_string()
        }

        fn open(&mut self, _from: FileId, path: &str) -> Option<FileId> {
            let index = self.0.iter().position(|f| f.0 == path)?;
            Some(Self::mint_file_id(index))
        }

        fn settings(&mut self) -> Settings {
            Settings::default()
        }
    }

    /// The name of each item, followed by the file it came from.
    fn items(files: &mut Memory) -> Vec<String> {
        let module = load(files).unwrap();
        let name = |item: &Item| match &item.kind {
            ItemKind::Fn(f) => f.sig.name.name.clone(),
            ItemKind::Binding(b) => b.name.name.clone(),
            _ => unreachable!(),
        };
        module
            .items
            .iter()
            .map(|item| format!("{} {}", name(item), files.display_name(item.span.file)))
            .collect()
    }

    /// Each error's message, and the file and text it points at.
    fn errors(files: &mut Memory) -> Vec<String> {
        let errors = match load(files) {
            Ok(module) => ty::check(&module, &files.settings())
                .unwrap_err()
                .into_iter()
                .map(Error::Type)
                .collect(),
            Err(errors) => errors,
        };
        errors
            .iter()
            .map(|e| {
                let span = e.span();
                let file = files.display_name(span.file);
                format!("{file} {:?}: {e}", files.text(span))
            })
            .collect()
    }

    #[test]
    fn imports_are_evaluated_in_place() {
        let mut files = Memory(vec![
            ("main", "let a = 1\nimport \"b\"\nlet d = 4\nimport \"e\"\n"),
            ("b", "let b = 2\nimport \"c\"\n"),
            ("c", "let c = 3\n"),
            ("e", "fn e():\n    pass\n"),
        ]);
        assert_eq!(items(&mut files), ["a main", "b b", "c c", "d main", "e e"]);
        let module = load(&mut files).unwrap();
        assert_eq!(module.items[2].span.file, files.id("c"));
        assert_eq!(files.text(module.items[2].span), "let c = 3");
    }

    #[test]
    fn globals_are_initialized_in_import_order() {
        let mut files = Memory(vec![
            ("main", "let a = 1\nimport \"b\"\nlet c = b + 1\n"),
            ("b", "let b = a + 1\n"),
        ]);
        let module = ty::check(&load(&mut files).unwrap(), &files.settings()).unwrap();
        let inits: Vec<_> = module.globals.iter().map(|g| g.init).collect();
        assert_eq!(inits, [Const::I32(1), Const::I32(2), Const::I32(3)]);
    }

    #[test]
    fn importing_a_file_twice_is_an_error_at_the_import() {
        let mut files = Memory(vec![
            ("main", "import \"a\"\nimport \"b\"\nimport \"a\"\n"),
            ("a", "let a = 1\nfn f():\n    pass\n"),
            ("b", "import \"a\"\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "b \"import \\\"a\\\"\": `a` is already imported",
                "main \"import \\\"a\\\"\": `a` is already imported",
            ]
        );
    }

    #[test]
    fn import_cycles_are_duplicates() {
        let mut files = Memory(vec![
            ("main", "import \"a\"\n"),
            ("a", "import \"main\"\nimport \"a\"\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "a \"import \\\"main\\\"\": `main` is already imported",
                "a \"import \\\"a\\\"\": `a` is already imported",
            ]
        );
    }

    #[test]
    fn missing_files() {
        let mut files = Memory(vec![("main", "let a = 1\nimport \"nope\"\n")]);
        assert_eq!(
            errors(&mut files),
            ["main \"import \\\"nope\\\"\": cannot find `nope`"]
        );
    }

    #[test]
    fn errors_point_into_the_file_they_are_in() {
        let mut files = Memory(vec![
            ("main", "import \"a\"\nimport \"b\"\nlet x = 1\n"),
            ("a", "let x = 1\nlet y = @\n"),
            ("b", "fn f(: i32):\n    pass\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "a \"@\": unexpected character '@'",
                "b \":\": expected identifier, found `:`",
            ]
        );

        let mut files = Memory(vec![
            ("main", "import \"a\"\nlet x = 1\n"),
            ("a", "\nlet x = 2\nlet y: Nope = 3\n"),
        ]);
        assert_eq!(
            errors(&mut files),
            [
                "main \"x\": `x` is already defined",
                "a \"Nope\": unknown type `Nope`",
            ]
        );
    }

    #[test]
    fn import_syntax() {
        let mut files = Memory(vec![
            (
                "main",
                "pub import \"a\"\nimport a\nfn f():\n    import \"a\"\n",
            ),
            ("a", ""),
        ]);
        let kinds: Vec<_> = load(&mut files)
            .unwrap_err()
            .into_iter()
            .map(|e| match e {
                Error::Parse(e) => e.kind,
                e => panic!("{e:?}"),
            })
            .collect();
        assert_eq!(
            kinds,
            [
                ParseErrorKind::PubImport,
                ParseErrorKind::Expected {
                    expected: "string".into(),
                    found: TokenKind::Ident("a".into()),
                },
                ParseErrorKind::Expected {
                    expected: "expression".into(),
                    found: TokenKind::Import,
                },
            ]
        );
    }
}

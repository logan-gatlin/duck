use std::fmt;

use crate::file::FileManager;
use crate::lex::{LexError, Span};
use crate::load::ImportError;
use crate::parse::ParseError;
use crate::ty::{InstanceSite, TypeError};

pub mod emit;
pub mod file;
pub mod ir;
pub mod lex;
pub mod load;
pub mod parse;
pub mod ty;

/// An error from any stage of [`compile`].
#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    Lex(LexError),
    Parse(ParseError),
    Import(ImportError),
    Type(TypeError),
}

impl Error {
    /// Where in the source the error is. `None` for errors in the
    /// [`file::Settings`], which no source file holds.
    pub fn span(&self) -> Option<Span> {
        match self {
            Self::Lex(e) => Some(e.span),
            Self::Parse(e) => Some(e.span),
            Self::Import(e) => Some(e.span),
            Self::Type(e) => e.span,
        }
    }

    /// The instances of generic functions the error is in, innermost first,
    /// each with the call that first used it.
    pub fn instances(&self) -> &[InstanceSite] {
        match self {
            Self::Type(e) => &e.instances,
            _ => &[],
        }
    }
}

/// Displays the message alone; locating [`Error::span`] is up to the caller.
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lex(e) => e.kind.fmt(f),
            Self::Parse(e) => e.kind.fmt(f),
            Self::Import(e) => e.kind.fmt(f),
            Self::Type(e) => e.kind.fmt(f),
        }
    }
}

impl std::error::Error for Error {}

/// Compiles the entry point of `files`, and every file it imports, to a
/// WebAssembly binary module.
///
/// Stops at the first stage that fails, returning all of its errors. Loading
/// every file counts as one stage.
pub fn compile(files: &mut impl FileManager) -> Result<Vec<u8>, Vec<Error>> {
    let module = load::load(files)?;
    let module = ty::check(&module, &files.settings())
        .map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
    Ok(emit::emit(&module))
}

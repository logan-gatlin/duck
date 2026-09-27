use std::fmt;

use crate::file::FileId;
use crate::lex::{LexError, Span};
use crate::parse::ParseError;
use crate::ty::TypeError;

pub mod emit;
pub mod file;
pub mod ir;
pub mod lex;
pub mod parse;
pub mod ty;

/// An error from any stage of [`compile`].
#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    Lex(LexError),
    Parse(ParseError),
    Type(TypeError),
}

impl Error {
    pub fn span(&self) -> Span {
        match self {
            Self::Lex(e) => e.span,
            Self::Parse(e) => e.span,
            Self::Type(e) => e.span,
        }
    }
}

/// Displays the message alone; locating [`Error::span`] is up to the caller.
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lex(e) => e.kind.fmt(f),
            Self::Parse(e) => e.kind.fmt(f),
            Self::Type(e) => e.kind.fmt(f),
        }
    }
}

impl std::error::Error for Error {}

/// Compiles the source text of `file` to a WebAssembly binary module.
///
/// Stops at the first stage that fails, returning all of its errors.
pub fn compile(file: FileId, src: &str) -> Result<Vec<u8>, Vec<Error>> {
    fn wrap<E>(errors: Vec<E>, f: fn(E) -> Error) -> Vec<Error> {
        errors.into_iter().map(f).collect()
    }
    let tokens = lex::tokenize(file, src).map_err(|e| vec![Error::Lex(e)])?;
    let module = parse::parse(&tokens).map_err(|e| wrap(e, Error::Parse))?;
    let module = ty::check(&module).map_err(|e| wrap(e, Error::Type))?;
    Ok(emit::emit(&module))
}

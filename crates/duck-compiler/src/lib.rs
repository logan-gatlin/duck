use std::fmt;

use crate::file::FileManager;
use crate::lex::{LexError, Span};
use crate::load::UseError;
use crate::parse::ParseError;
use crate::ty::{InstanceSite, TypeError, TypeErrorKind};
use crate::world::{World, WorldError};

pub mod bindgen;
pub mod emit;
mod eval;
pub mod file;
pub mod format;
pub mod ir;
pub mod lex;
pub mod load;
pub mod parse;
pub mod ty;
pub mod world;

/// An error from any stage of [`compile`].
#[derive(Debug, Clone, PartialEq)]
pub enum Error {
    Lex(LexError),
    Parse(ParseError),
    Use(UseError),
    Type(TypeError),
    /// The module is no component of its world: it imports what the world
    /// doesn't have, lacks what it exports, or declares either as the
    /// Canonical ABI doesn't.
    Component(String),
}

impl Error {
    /// Where in the source the error is. `None` for errors in the
    /// [`file::Settings`], which no source file holds.
    pub fn span(&self) -> Option<Span> {
        match self {
            Self::Lex(e) => Some(e.span),
            Self::Parse(e) => Some(e.span),
            Self::Use(e) => Some(e.span),
            Self::Type(e) => e.span,
            Self::Component(_) => None,
        }
    }

    /// For an error in the type arguments a call gives a generic function,
    /// the instances that need what they lack, outermost first, each with
    /// where in its body it needs it.
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
            Self::Use(e) => e.kind.fmt(f),
            Self::Type(e) => e.kind.fmt(f),
            Self::Component(e) => write!(f, "cannot make a component of the module: {e}"),
        }
    }
}

impl std::error::Error for Error {}

/// Compiles the entry point of `files`, and every file it uses, to a
/// WebAssembly component of the world its [`file::Settings`] name.
///
/// Stops at the first stage that fails, returning all of its errors. Loading
/// every file counts as one stage.
pub fn compile(files: &mut impl FileManager) -> Result<Vec<u8>, Vec<Error>> {
    let settings = files.settings();
    if settings.world.is_none() {
        let error = TypeError::nowhere(TypeErrorKind::World(WorldError::Library));
        return Err(vec![Error::Type(error)]);
    }
    let module = lower(files)?;
    // The module has no errors, so the settings name a world.
    let world = World::load(&settings).expect("the world is read");
    let component = world.encode(emit::emit(&module));
    component.map_err(|e| vec![Error::Component(e)])
}

/// Lowers the entry point of `files`, and every file it uses, to the core
/// module that [`compile`] makes a component of.
pub fn lower(files: &mut impl FileManager) -> Result<ir::Module, Vec<Error>> {
    let module = load::load(files)?;
    ty::check(&module, &files.settings()).map_err(|e| e.into_iter().map(Error::Type).collect())
}

/// Finds the errors [`compile`] does in the entry point of `files`, and
/// every file it uses, without making the module of a program that has none.
pub fn check(files: &mut impl FileManager) -> Result<(), Vec<Error>> {
    let module = load::load(files)?;
    let errors = ty::errors(&module, &files.settings());
    match errors.is_empty() {
        true => Ok(()),
        false => Err(errors.into_iter().map(Error::Type).collect()),
    }
}

use std::fmt;

use crate::file::FileManager;
use crate::lex::{LexError, Span};
use crate::load::UseError;
use crate::parse::ParseError;
use crate::ty::{InstanceSite, TypeError};
use crate::world::{RUN_EXPORT, World, WorldError};

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
    /// There is no world to build a component of, or none for what the
    /// [`file::Settings`] ask of it.
    World(WorldError),
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
            Self::World(_) | Self::Component(_) => None,
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
            Self::World(e) => e.fmt(f),
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
        return Err(vec![Error::World(WorldError::Library)]);
    }
    if settings.memory64 {
        return Err(vec![Error::World(WorldError::Memory64)]);
    }
    let world = World::load(&settings).map_err(|e| vec![Error::World(e)])?;
    let module = lower_in(files, &world)?;
    let component = world.encode(emit::emit(&module));
    component.map_err(|e| vec![Error::Component(e)])
}

/// Lowers the entry point of `files`, and every file it uses, to the core
/// module that [`compile`] makes a component of.
pub fn lower(files: &mut impl FileManager) -> Result<ir::Module, Vec<Error>> {
    let world = World::load(&files.settings()).map_err(|e| vec![Error::World(e)])?;
    lower_in(files, &world)
}

/// Finds the errors [`compile`] does in the entry point of `files`, and
/// every file it uses, without making the module of a program that has none.
pub fn check(files: &mut impl FileManager) -> Result<(), Vec<Error>> {
    let settings = files.settings();
    let world = World::load(&settings).map_err(|e| vec![Error::World(e)])?;
    let module = load::load(files)?;
    let errors = ty::errors(&module, &settings);
    if !errors.is_empty() {
        return Err(errors.into_iter().map(Error::Type).collect());
    }
    match settings.start.is_some() && !world.exports_run() {
        true => Err(vec![Error::World(world.start_error())]),
        false => Ok(()),
    }
}

/// [`lower`] as a component of `world`, whose `run` calls the start
/// function rather than it running when the module is instantiated: no
/// import that reads or writes memory can be called until then.
fn lower_in(files: &mut impl FileManager, world: &World) -> Result<ir::Module, Vec<Error>> {
    let program = load::load(files)?;
    let checked = ty::check(&program, &files.settings());
    let mut module = checked.map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
    let Some(start) = module.start.take() else {
        return Ok(module);
    };
    if !world.exports_run() {
        return Err(vec![Error::World(world.start_error())]);
    }
    // It returns the `result` of `run`, which is `ok` once the start
    // function returns: a program that fails exits with a status.
    let ok = ir::Expr::Const(ir::Const::I32(0));
    module.funcs.push(ir::Func {
        name: RUN_EXPORT.to_string(),
        exports: vec![RUN_EXPORT.to_string()],
        params: Vec::new(),
        results: vec![ir::ValType::I32],
        locals: Vec::new(),
        body: vec![
            ir::Stmt::Call {
                func: start,
                args: Vec::new(),
                dests: Vec::new(),
            },
            ir::Stmt::Return(vec![ok]),
        ],
    });
    Ok(module)
}

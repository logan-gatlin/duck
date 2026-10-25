use std::fmt;

use crate::file::{FileId, FileManager};
use crate::lex::{LexError, Span};
use crate::load::UseError;
use crate::parse::ParseError;
use crate::ty::{Artifact, InstanceSite, Test, TypeError, TypeErrorKind};
use crate::world::{World, WorldError};

pub mod bindgen;
mod codec;
pub mod emit;
mod eval;
pub mod file;
pub mod format;
pub mod ir;
pub mod lex;
pub mod load;
pub mod parse;
pub mod ty;
mod visit;
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

/// The tests of a package, as [`compile_tests`] compiles them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tests {
    /// The component that runs them. It imports what the world of the
    /// package does, and exports the function [`world::TEST_EXPORT`] alone,
    /// which takes the index of a test in `tests` and calls it. Each test
    /// is to run in an instance of its own, which starts as the constants
    /// of the package left it.
    pub component: Vec<u8>,
    /// Each test, in the order they are run in.
    pub tests: Vec<Test>,
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

    /// What names the kind of error, whatever it is about: it stays as it
    /// is where the message is written anew, for an editor to tell errors by
    /// and for a change that mends one to say which.
    pub fn code(&self) -> &'static str {
        match self {
            Self::Lex(e) => e.kind.code(),
            Self::Parse(e) => e.kind.code(),
            Self::Use(e) => e.kind.code(),
            Self::Type(e) => e.kind.code(),
            Self::Component(_) => "component",
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
            Self::Type(e) => e.message().fmt(f),
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
///
/// The test modules of `files` are modules of the program, so a package is
/// built from files that have none: [`compile_tests`] is for those that do.
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

/// Compiles the package of the entry point of `files` to its [`Artifact`]:
/// what [`link`] makes the component of with those of the packages it
/// uses, and what a program that uses the package is checked against. A
/// package it uses that is compiled already, which `files` have the
/// artifact of, isn't compiled again.
///
/// Stops at the first stage that fails, as [`compile`] does.
pub fn compile_package(files: &mut impl FileManager) -> Result<Artifact, Vec<Error>> {
    let settings = files.settings();
    let program = load::load(files)?;
    let built = ty::build(&program, &settings, files, false);
    let mut built = built.map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
    Ok(built.artifacts.pop().expect("the entry's package is last"))
}

/// The module of `program`, which has `settings`, linked from the artifact
/// of each of its packages: those it has from the packages that are
/// compiled already, and those `built` of the rest.
pub(crate) fn linked(
    program: &load::Program,
    settings: &file::Settings,
    built: &[Artifact],
) -> Result<ir::Module, Vec<Error>> {
    let artifacts: Vec<&Artifact> = program
        .packages
        .iter()
        .zip(built)
        .map(|(package, built)| {
            let compiled = program.imported.iter().find(|c| c.root == package.root);
            compiled.map_or(built, |compiled| &*compiled.artifact)
        })
        .collect();
    let module = ty::link_refs(&artifacts, settings);
    // An error of linking is in a file of the artifacts, numbered as they
    // are laid end to end: each artifact's are its package's, in order.
    let files: Vec<FileId> = (program.packages.iter())
        .flat_map(|package| package.files.iter().copied())
        .collect();
    let placed = |mut error: TypeError| {
        if let Some(span) = &mut error.span {
            span.file = files[span.file.index()];
        }
        for site in &mut error.instances {
            site.span.file = files[site.span.file.index()];
        }
        Error::Type(error)
    };
    module.map_err(|e| e.into_iter().map(placed).collect())
}

/// Compiles the entry point of `files`, and every file it uses, to the
/// [`Artifact`] of each of its packages, those it depends on first: what
/// [`link`] makes the component of that [`compile`] makes.
///
/// Stops at the first stage that fails, as [`compile`] does. The errors of
/// linking are found by [`link`].
pub fn compile_artifacts(files: &mut impl FileManager) -> Result<Vec<Artifact>, Vec<Error>> {
    let settings = files.settings();
    if settings.world.is_none() {
        let error = TypeError::nowhere(TypeErrorKind::World(WorldError::Library));
        return Err(vec![Error::Type(error)]);
    }
    let program = load::load(files)?;
    let artifacts = ty::artifacts(&program, &settings, files);
    artifacts.map_err(|e| e.into_iter().map(Error::Type).collect())
}

/// Links `artifacts`, which [`compile_artifacts`] makes of files with
/// `settings`, to the component that [`compile`] makes of those files.
///
/// Each error is in the file of [`Artifact::linked_files`] that its span's
/// [`file::FileId`] is minted from the index of.
pub fn link(artifacts: &[Artifact], settings: &file::Settings) -> Result<Vec<u8>, Vec<Error>> {
    let world = World::load(settings).map_err(|e| {
        let error = TypeError::nowhere(TypeErrorKind::World(e));
        vec![Error::Type(error)]
    })?;
    if world.is_library() {
        let error = TypeError::nowhere(TypeErrorKind::World(WorldError::Library));
        return Err(vec![Error::Type(error)]);
    }
    let module = ty::link(artifacts, settings);
    let module = module.map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
    let component = world.encode(emit::emit(&module));
    component.map_err(|e| vec![Error::Component(e)])
}

/// Compiles the entry point of `files`, every file it uses, and each of its
/// test modules, with what those use, to a WebAssembly component that runs
/// the tests of the package: one of the world that [`World::tests`] makes
/// of the world its [`file::Settings`] name. A library, which has no world
/// to be built as a component of, is tested as one that imports what its
/// `extern` blocks name.
///
/// Stops at the first stage that fails, as [`compile`] does.
pub fn compile_tests(files: &mut impl FileManager) -> Result<Tests, Vec<Error>> {
    let settings = files.settings();
    let program = load::load(files)?;
    let (module, tests, world) = match program.imported.is_empty() {
        true => {
            let tested = ty::check_tests(&program, &settings);
            let tested = tested.map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
            (tested.module, tested.tests, tested.world)
        }
        false => {
            let built = ty::build(&program, &settings, files, true);
            let built = built.map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
            let module = linked(&program, &settings, &built.artifacts)?;
            (module, built.tests, built.world)
        }
    };
    let component = world.encode(emit::emit(&module));
    let component = component.map_err(|e| vec![Error::Component(e)])?;
    Ok(Tests { component, tests })
}

/// Lowers the entry point of `files`, every file it uses, and each of its
/// test modules to the core module that [`compile_tests`] makes a
/// component of.
pub fn lower_tests(files: &mut impl FileManager) -> Result<ir::Module, Vec<Error>> {
    let settings = files.settings();
    let program = load::load(files)?;
    if program.imported.is_empty() {
        let tested = ty::check_tests(&program, &settings);
        return tested
            .map(|tested| tested.module)
            .map_err(|e| e.into_iter().map(Error::Type).collect());
    }
    let built = ty::build(&program, &settings, files, true);
    let built = built.map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
    linked(&program, &settings, &built.artifacts)
}

/// Lowers the entry point of `files`, and every file it uses, to the core
/// module that [`compile`] makes a component of.
pub fn lower(files: &mut impl FileManager) -> Result<ir::Module, Vec<Error>> {
    let settings = files.settings();
    let program = load::load(files)?;
    // A package that is compiled already is linked as it was compiled.
    if !program.imported.is_empty() {
        let built = ty::build(&program, &settings, files, false);
        let built = built.map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
        return linked(&program, &settings, &built.artifacts);
    }
    ty::check(&program, &settings).map_err(|e| e.into_iter().map(Error::Type).collect())
}

/// Finds the errors [`compile`] does in the entry point of `files`, and
/// every file it uses, without making the module of a program that has none.
pub fn check(files: &mut impl FileManager) -> Result<(), Vec<Error>> {
    let settings = files.settings();
    let program = load::load(files)?;
    if !program.imported.is_empty() {
        let built = ty::build(&program, &settings, files, false);
        let built = built.map_err(|e| e.into_iter().map(Error::Type).collect::<Vec<_>>())?;
        return linked(&program, &settings, &built.artifacts).map(|_| ());
    }
    let errors = ty::errors(&program, &settings);
    match errors.is_empty() {
        true => Ok(()),
        false => Err(errors.into_iter().map(Error::Type).collect()),
    }
}

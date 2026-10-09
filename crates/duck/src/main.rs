mod agents;
mod lsp;
mod new;
mod run;

use std::fmt::Display;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use duck::files::{self, Files};
use duck::manifest::{MANIFEST, Manifest};
use duck::package::Packages;
use duck::{git, package};
use duck_compiler::file::FileManager;

#[derive(Parser)]
#[command(version, about = "The duck programming language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Compile the package described by the nearest Duck.toml: build its
    /// module, or check its library if it has no module
    Build,
    /// Compile the module of the package described by the nearest Duck.toml
    /// and run its `start` function in Wasmtime, which gives it WASI 0.2 and
    /// with it the files and the network of this machine
    Run {
        /// The arguments the program is given
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// Lay out the source files of the package described by the nearest
    /// Duck.toml as the language is written, with lines of up to 100 columns.
    /// A file that doesn't parse is left as it is
    Format {
        /// Format these files, and every source file of these directories,
        /// in place of the package's
        paths: Vec<PathBuf>,
        /// Write nothing: name each file that isn't formatted, and fail if
        /// there are any
        #[arg(long)]
        check: bool,
    },
    /// Create a new package in a new directory: a module, or a library with --lib
    New {
        /// The directory to create
        path: PathBuf,
        /// Create a library for other packages to use, not a module
        #[arg(long)]
        lib: bool,
    },
    /// Print an overview of the duck language for coding agents
    Agents,
    /// Report the errors of duck packages to an editor, speaking the Language
    /// Server Protocol over stdio
    Lsp,
}

fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Build => build(),
        Command::Run { args } => run(args),
        Command::Format { paths, check } => format(paths, check),
        Command::New { path, lib } => {
            let kind = if lib {
                new::Kind::Library
            } else {
                new::Kind::Module
            };
            match new::new(&path, kind) {
                Ok(()) => ExitCode::SUCCESS,
                Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
                    fail(format_args!("{} already exists", path.display()))
                }
                Err(e) => fail(format_args!("cannot create {}: {e}", path.display())),
            }
        }
        Command::Agents => {
            print!("{}", agents::OVERVIEW);
            ExitCode::SUCCESS
        }
        Command::Lsp => lsp::serve(),
    }
}

fn build() -> ExitCode {
    let (root, packages) = match resolve() {
        Ok(resolved) => resolved,
        Err(code) => return code,
    };
    let manifest = &packages.root().manifest;

    // A package without a module is only checked.
    let (entry, settings) = match (&manifest.module, &manifest.library) {
        (Some(module), _) => (&module.entry, module.settings()),
        (None, Some(library)) => (&library.entry, library.settings()),
        (None, None) => unreachable!("every manifest has a module or a library"),
    };
    let entry = root.join(entry);
    let mut files = match Files::new(&packages, &entry, settings) {
        Ok(files) => files,
        Err(e) => return fail(format_args!("cannot read {}: {e}", entry.display())),
    };
    let compiled = match &manifest.module {
        Some(_) => duck_compiler::compile(&mut files).map(Some),
        None => duck_compiler::check(&mut files).map(|()| None),
    };
    let bytes = match compiled {
        Ok(bytes) => bytes,
        Err(errors) => return report(&errors, &mut files, &root.join(MANIFEST)),
    };

    let (Some(module), Some(bytes)) = (&manifest.module, bytes) else {
        return ExitCode::SUCCESS;
    };
    let output = root.join(&module.output);
    if let Some(dir) = output.parent()
        && let Err(e) = fs::create_dir_all(dir)
    {
        return fail(format_args!("cannot create {}: {e}", dir.display()));
    }
    if let Err(e) = fs::write(&output, bytes) {
        return fail(format_args!("cannot write {}: {e}", output.display()));
    }
    ExitCode::SUCCESS
}

/// Compiles the module of the nearest package and runs it, writing nothing.
/// The program is named as the module's output is, before `args`.
fn run(args: Vec<String>) -> ExitCode {
    let (root, packages) = match resolve() {
        Ok(resolved) => resolved,
        Err(code) => return code,
    };
    let Some(module) = &packages.root().manifest.module else {
        return fail(format_args!("nothing to run: {MANIFEST} has no [module]"));
    };
    let entry = root.join(&module.entry);
    let mut files = match Files::new(&packages, &entry, module.settings()) {
        Ok(files) => files,
        Err(e) => return fail(format_args!("cannot read {}: {e}", entry.display())),
    };
    let lowered = match duck_compiler::lower(&mut files) {
        Ok(lowered) => lowered,
        Err(errors) => return report(&errors, &mut files, &root.join(MANIFEST)),
    };
    let name = module.output.file_name().unwrap_or_default();
    let name = name.to_string_lossy().into_owned();
    let args: Vec<_> = [name].into_iter().chain(args).collect();
    match run::run(lowered, &args) {
        Ok(status) => ExitCode::from(status),
        Err(e) => fail(e),
    }
}

/// Formats the source files that `paths` name, or those of the nearest
/// package if there are none. With `check` it names the files that formatting
/// would change, and changes none. Fails if a file doesn't parse, or if one
/// that `check` finds would change.
fn format(mut paths: Vec<PathBuf>, check: bool) -> ExitCode {
    if paths.is_empty() {
        match Manifest::find() {
            Ok(Some(root)) => paths.push(root),
            Ok(None) => {
                return fail(format_args!(
                    "cannot find {MANIFEST} in this directory or any parent"
                ));
            }
            Err(e) => return fail(format_args!("cannot find {MANIFEST}: {e}")),
        }
    }
    let mut sources = Vec::new();
    let mut code = ExitCode::SUCCESS;
    for path in paths {
        if let Err(e) = files::sources(&path, &mut sources) {
            code = fail(format_args!("cannot read {}: {e}", path.display()));
        }
    }
    for path in sources {
        let source = match fs::read_to_string(&path) {
            Ok(source) => source,
            Err(e) => {
                code = fail(format_args!("cannot read {}: {e}", path.display()));
                continue;
            }
        };
        let formatted = match duck_compiler::format::format(&source) {
            Ok(formatted) => formatted,
            Err(errors) => {
                for error in errors {
                    let offset = error.span().map_or(0, |span| span.start);
                    let (line, col) = line_col(&source, offset);
                    eprintln!("{}:{line}:{col}: error: {error}", path.display());
                }
                code = ExitCode::FAILURE;
                continue;
            }
        };
        if formatted == source {
            continue;
        }
        if check {
            println!("{}", path.display());
            code = ExitCode::FAILURE;
        } else if let Err(e) = fs::write(&path, formatted) {
            code = fail(format_args!("cannot write {}: {e}", path.display()));
        }
    }
    code
}

/// The root of the nearest package, and it with every package it depends
/// on. Reports why there are none.
fn resolve() -> Result<(PathBuf, Packages), ExitCode> {
    let root = match Manifest::find() {
        Ok(Some(root)) => root,
        Ok(None) => {
            return Err(fail(format_args!(
                "cannot find {MANIFEST} in this directory or any parent"
            )));
        }
        Err(e) => return Err(fail(format_args!("cannot find {MANIFEST}: {e}"))),
    };
    let packages = package::resolve(&root, &git::Cache::from_env()).map_err(fail)?;
    Ok((root, packages))
}

/// Prints each of `errors` with where in `files` it is, or with the manifest
/// if it's in no file.
fn report(errors: &[duck_compiler::Error], files: &mut Files, manifest: &Path) -> ExitCode {
    for error in errors {
        let Some(span) = error.span() else {
            eprintln!("{}: error: {error}", manifest.display());
            continue;
        };
        let (line, col) = line_col(&files.contents(span.file), span.start);
        eprintln!(
            "{}:{line}:{col}: error: {error}",
            files.display_name(span.file)
        );
        for site in error.instances() {
            let span = site.span;
            let (line, col) = line_col(&files.contents(span.file), span.start);
            eprintln!(
                "{}:{line}:{col}: note: required by `{}` here",
                files.display_name(span.file),
                site.name
            );
        }
    }
    ExitCode::FAILURE
}

fn fail(message: impl Display) -> ExitCode {
    eprintln!("error: {message}");
    ExitCode::FAILURE
}

/// The 1-based line and column of byte `offset` in `src`.
fn line_col(src: &str, offset: usize) -> (usize, usize) {
    let before = &src[..offset.min(src.len())];
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    let line = before.matches('\n').count() + 1;
    let col = before[line_start..].chars().count() + 1;
    (line, col)
}

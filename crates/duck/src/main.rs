mod agents;
mod lsp;
mod new;

use std::fmt::Display;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use duck::files::Files;
use duck::manifest::{MANIFEST, Manifest};
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
    let root = match Manifest::find() {
        Ok(Some(root)) => root,
        Ok(None) => {
            return fail(format_args!(
                "cannot find {MANIFEST} in this directory or any parent"
            ));
        }
        Err(e) => return fail(format_args!("cannot find {MANIFEST}: {e}")),
    };
    let manifest_path = root.join(MANIFEST);
    let packages = match package::resolve(&root, &git::Cache::from_env()) {
        Ok(packages) => packages,
        Err(e) => return fail(e),
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
        Err(errors) => {
            for error in &errors {
                let Some(span) = error.span() else {
                    eprintln!("{}: error: {error}", manifest_path.display());
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
            return ExitCode::FAILURE;
        }
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

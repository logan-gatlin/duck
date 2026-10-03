mod files;
mod git;
mod manifest;
mod new;
mod package;

use std::fmt::Display;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use duck_compiler::file::{FileManager, MemoryLimits, Settings};

use crate::files::Files;
use crate::manifest::{MANIFEST, MAX_PAGES, Manifest};

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
    /// Create a new module in a new directory
    New {
        /// The directory to create
        path: PathBuf,
    },
}

fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Build => build(),
        Command::New { path } => match new::new(&path) {
            Ok(()) => ExitCode::SUCCESS,
            Err(e) if e.kind() == io::ErrorKind::AlreadyExists => {
                fail(format_args!("{} already exists", path.display()))
            }
            Err(e) => fail(format_args!("cannot create {}: {e}", path.display())),
        },
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

    // A package without a module is only checked, with room for any data.
    let (entry, settings) = match (&manifest.module, &manifest.library) {
        (Some(module), _) => (
            &module.entry,
            Settings {
                memory: module.memory,
                start: module.start.clone(),
            },
        ),
        (None, Some(library)) => (
            &library.entry,
            Settings {
                memory: MemoryLimits {
                    min_pages: MAX_PAGES,
                    max_pages: None,
                },
                start: None,
            },
        ),
        (None, None) => unreachable!("every manifest has a module or a library"),
    };
    let entry = root.join(entry);
    let mut files = match Files::new(&packages, &entry, settings) {
        Ok(files) => files,
        Err(e) => return fail(format_args!("cannot read {}: {e}", entry.display())),
    };
    let bytes = match duck_compiler::compile(&mut files) {
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
                    let call = site.call;
                    let (line, col) = line_col(&files.contents(call.file), call.start);
                    eprintln!(
                        "{}:{line}:{col}: note: in `{}`, called here",
                        files.display_name(call.file),
                        site.name
                    );
                }
            }
            return ExitCode::FAILURE;
        }
    };

    let Some(module) = &manifest.module else {
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

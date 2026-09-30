mod files;
mod manifest;
mod new;

use std::fmt::Display;
use std::fs;
use std::io;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use duck_compiler::file::{FileManager, Settings};

use crate::files::Files;
use crate::manifest::{MANIFEST, Manifest};

#[derive(Parser)]
#[command(version, about = "The duck programming language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Compile the module described by the nearest Duck.toml
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
    let manifest = match fs::read_to_string(&manifest_path) {
        Ok(src) => Manifest::parse(&src),
        Err(e) => return fail(format_args!("cannot read {}: {e}", manifest_path.display())),
    };
    let manifest = match manifest {
        Ok(manifest) => manifest,
        Err(e) => return fail(format_args!("{}: {e}", manifest_path.display())),
    };

    let entry = root.join(&manifest.entry);
    let settings = Settings {
        memory: manifest.memory,
        start: manifest.start,
    };
    let mut files = match Files::new(&entry, settings) {
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

    let output = root.join(&manifest.output);
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

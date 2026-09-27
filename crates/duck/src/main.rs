mod files;

use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use duck_compiler::file::FileManager;

use crate::files::Files;

#[derive(Parser)]
#[command(version, about = "The duck programming language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Compile a source file to a WebAssembly module
    Build,
}

fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Build => build(),
    }
}

fn build() -> ExitCode {
    let mut files = Files::new();
    let entry = files.entry_point();
    let src = files.contents(entry);
    let bytes = match duck_compiler::compile(files.entry_point(), &src) {
        Ok(bytes) => bytes,
        Err(errors) => {
            for error in &errors {
                let (line, col) = line_col(&src, error.span().start);
                eprintln!("{}:{line}:{col}: error: {error}", files.display_name(entry));
            }
            return ExitCode::FAILURE;
        }
    };
    let output = "build/main.wasm";
    if let Err(e) = fs::write(&output, bytes) {
        eprintln!("error: cannot write {}: {e}", output);
        return ExitCode::FAILURE;
    }
    ExitCode::SUCCESS
}

/// The 1-based line and column of byte `offset` in `src`.
fn line_col(src: &str, offset: usize) -> (usize, usize) {
    let before = &src[..offset.min(src.len())];
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    let line = before.matches('\n').count() + 1;
    let col = before[line_start..].chars().count() + 1;
    (line, col)
}

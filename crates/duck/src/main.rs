use std::fs;
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use duck_compiler::file::FileId;

#[derive(Parser)]
#[command(version, about = "The duck programming language")]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Compile a source file to a WebAssembly module
    Build {
        /// The `.duck` file to compile
        input: PathBuf,
        /// Where to write the module [default: the input with a `.wasm` extension]
        #[arg(short, long)]
        output: Option<PathBuf>,
    },
}

fn main() -> ExitCode {
    match Cli::parse().command {
        Command::Build { input, output } => build(input, output),
    }
}

fn build(input: PathBuf, output: Option<PathBuf>) -> ExitCode {
    let src = match fs::read_to_string(&input) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", input.display());
            return ExitCode::FAILURE;
        }
    };
    let bytes = match duck_compiler::compile(FileId::new(0), &src) {
        Ok(bytes) => bytes,
        Err(errors) => {
            for error in &errors {
                let (line, col) = line_col(&src, error.span().start);
                eprintln!("{}:{line}:{col}: error: {error}", input.display());
            }
            return ExitCode::FAILURE;
        }
    };
    let output = output.unwrap_or_else(|| input.with_extension("wasm"));
    if let Err(e) = fs::write(&output, bytes) {
        eprintln!("error: cannot write {}: {e}", output.display());
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

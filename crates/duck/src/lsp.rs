//! `duck lsp`: a language server that reports the errors of duck packages
//! to an editor, speaking the Language Server Protocol over stdio.

mod project;
mod server;

use std::process::ExitCode;

use duck::git::Cache;
use lsp_server::Connection;

/// Serves the editor on stdio until it asks to exit.
pub fn serve() -> ExitCode {
    let (connection, io_threads) = Connection::stdio();
    let served = server::run(&connection, Cache::from_env());
    // Closes the channels the threads read, so that they end.
    drop(connection);
    let joined = io_threads.join();
    match served.and(joined.map_err(Into::into)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::FAILURE
        }
    }
}

//! The language server: keeps what the editor has open, and publishes the
//! errors of the packages those files are in whenever one changes.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::error::Error;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use duck::git::Cache;
use duck::manifest::MANIFEST;
use lsp_server::{Connection, ErrorCode, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{
    DidChangeTextDocument, DidChangeWatchedFiles, DidCloseTextDocument, DidOpenTextDocument,
    DidSaveTextDocument, Notification as _, PublishDiagnostics,
};
use lsp_types::request::{RegisterCapability, Request as _};
use lsp_types::{
    Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, DidChangeTextDocumentParams,
    DidChangeWatchedFilesRegistrationOptions, DidCloseTextDocumentParams,
    DidOpenTextDocumentParams, FileSystemWatcher, GlobPattern, InitializeParams, InitializeResult,
    Location, PublishDiagnosticsParams, Registration, RegistrationParams, ServerCapabilities,
    ServerInfo, TextDocumentSyncCapability, TextDocumentSyncKind, TextDocumentSyncOptions,
    TextDocumentSyncSaveOptions, Uri,
};
use url::Url;

use crate::project::{self, Place, Problem, Project};

type Fallible = Result<(), Box<dyn Error + Send + Sync>>;

struct Server<'c> {
    connection: &'c Connection,
    cache: Cache,
    /// The directories the editor has open.
    folders: Vec<PathBuf>,
    /// The files the editor has open, by canonical path.
    documents: HashMap<PathBuf, Document>,
    /// The packages last checked, by directory. They are resolved again
    /// once dropped.
    projects: HashMap<PathBuf, Project>,
    /// The diagnostics the editor has of each file that has any.
    published: BTreeMap<Uri, Vec<Diagnostic>>,
    /// Whether something changed since the diagnostics were published.
    stale: bool,
}

/// A file as it is in the editor, saved or not.
struct Document {
    /// What the editor calls it, which need not be its canonical path.
    uri: Uri,
    version: i32,
    text: String,
}

/// Serves the editor at the other end of `connection` until it asks to exit,
/// fetching git dependencies into `cache`.
pub fn run(connection: &Connection, cache: Cache) -> Fallible {
    let (id, params) = connection.initialize_start()?;
    let params: InitializeParams = serde_json::from_value(params)?;
    let result = InitializeResult {
        capabilities: capabilities(),
        server_info: Some(ServerInfo {
            name: env!("CARGO_PKG_NAME").to_string(),
            version: Some(env!("CARGO_PKG_VERSION").to_string()),
        }),
    };
    connection.initialize_finish(id, serde_json::to_value(result)?)?;

    let mut server = Server {
        connection,
        cache,
        folders: folders(&params),
        documents: HashMap::new(),
        projects: HashMap::new(),
        published: BTreeMap::new(),
        stale: false,
    };
    if watches_on_request(&params) {
        server.watch()?;
    }
    server.publish()?;
    for message in &connection.receiver {
        match message {
            Message::Request(request) => {
                if connection.handle_shutdown(&request)? {
                    return Ok(());
                }
                server.refuse(request)?;
            }
            Message::Notification(notification) => server.notified(notification),
            Message::Response(_) => {}
        }
        // One check answers every change the editor has sent so far.
        if server.stale && connection.receiver.is_empty() {
            server.publish()?;
        }
    }
    Ok(())
}

impl Server<'_> {
    /// Asks the editor to tell of changes to source files and manifests it
    /// doesn't have open.
    fn watch(&self) -> Fallible {
        let watcher = |glob: String| FileSystemWatcher {
            glob_pattern: GlobPattern::String(glob),
            kind: None,
        };
        let options = DidChangeWatchedFilesRegistrationOptions {
            watchers: vec![
                watcher("**/*.duck".to_string()),
                watcher(format!("**/{MANIFEST}")),
            ],
        };
        let params = RegistrationParams {
            registrations: vec![Registration {
                id: "watch".to_string(),
                method: DidChangeWatchedFiles::METHOD.to_string(),
                register_options: Some(serde_json::to_value(options)?),
            }],
        };
        let method = RegisterCapability::METHOD.to_string();
        // The only request the server makes.
        let request = Request::new(RequestId::from(0), method, params);
        self.connection.sender.send(request.into())?;
        Ok(())
    }

    /// Answers a request for something the server doesn't do.
    fn refuse(&self, request: Request) -> Fallible {
        let message = format!("unknown request `{}`", request.method);
        let code = ErrorCode::MethodNotFound as i32;
        let response = Response::new_err(request.id, code, message);
        self.connection.sender.send(response.into())?;
        Ok(())
    }

    fn notified(&mut self, notification: Notification) {
        let Notification { method, params } = notification;
        match method.as_str() {
            DidOpenTextDocument::METHOD => {
                let Ok(params) = serde_json::from_value::<DidOpenTextDocumentParams>(params) else {
                    return;
                };
                let document = params.text_document;
                let Some(path) = path_of(&document.uri) else {
                    return;
                };
                self.documents.insert(
                    path,
                    Document {
                        uri: document.uri,
                        version: document.version,
                        text: document.text,
                    },
                );
            }
            DidChangeTextDocument::METHOD => {
                let Ok(params) = serde_json::from_value::<DidChangeTextDocumentParams>(params)
                else {
                    return;
                };
                let DidChangeTextDocumentParams {
                    text_document,
                    mut content_changes,
                } = params;
                let path = path_of(&text_document.uri);
                let document = path.and_then(|path| self.documents.get_mut(&path));
                // Each change is the whole text, so the last is what's left.
                let (Some(document), Some(change)) = (document, content_changes.pop()) else {
                    return;
                };
                document.version = text_document.version;
                document.text = change.text;
                // The manifests are as they were, as they are read saved.
                self.stale = true;
                return;
            }
            DidCloseTextDocument::METHOD => {
                let Ok(params) = serde_json::from_value::<DidCloseTextDocumentParams>(params)
                else {
                    return;
                };
                if let Some(path) = path_of(&params.text_document.uri) {
                    self.documents.remove(&path);
                }
            }
            DidSaveTextDocument::METHOD | DidChangeWatchedFiles::METHOD => {}
            _ => return,
        }
        self.projects.clear();
        self.stale = true;
    }

    /// Checks every package the editor has a file of open, and sends it the
    /// diagnostics of each file whose diagnostics changed.
    // A `Uri` only mutates what it remembers of parsing itself, which
    // neither its order nor its hash reads.
    #[allow(clippy::mutable_key_type)]
    fn publish(&mut self) -> Fallible {
        self.stale = false;
        let paths = self.folders.iter().chain(self.documents.keys());
        let roots: BTreeSet<PathBuf> = paths.filter_map(|path| project::root_of(path)).collect();
        self.projects.retain(|root, _| roots.contains(root));

        let mut diagnostics: BTreeMap<Uri, Vec<Diagnostic>> = BTreeMap::new();
        for root in roots {
            let project = (self.projects.entry(root.clone()))
                .or_insert_with(|| Project::resolve(root, &self.cache));
            let documents = &self.documents;
            let problems = project.check(&|path| Some(documents.get(path)?.text.as_str()));
            for problem in problems {
                let Some((uri, diagnostic)) = self.diagnostic(problem) else {
                    continue;
                };
                // A file of two packages has its errors found twice.
                let diagnostics = diagnostics.entry(uri).or_default();
                if !diagnostics.contains(&diagnostic) {
                    diagnostics.push(diagnostic);
                }
            }
        }

        let fixed = self.published.keys();
        let fixed: Vec<Uri> = (fixed.filter(|uri| !diagnostics.contains_key(uri)))
            .cloned()
            .collect();
        for uri in fixed {
            self.send(uri, Vec::new())?;
        }
        for (uri, diagnostics) in diagnostics {
            if self.published.get(&uri) != Some(&diagnostics) {
                self.send(uri, diagnostics)?;
            }
        }
        Ok(())
    }

    /// Tells the editor that `diagnostics` are all there are for `uri`.
    fn send(&mut self, uri: Uri, diagnostics: Vec<Diagnostic>) -> Fallible {
        let mut documents = self.documents.values();
        let version = documents.find(|d| d.uri == uri).map(|d| d.version);
        let params = PublishDiagnosticsParams {
            uri: uri.clone(),
            diagnostics: diagnostics.clone(),
            version,
        };
        let method = PublishDiagnostics::METHOD.to_string();
        let notification = Notification::new(method, params);
        self.connection.sender.send(notification.into())?;
        if diagnostics.is_empty() {
            self.published.remove(&uri);
        } else {
            self.published.insert(uri, diagnostics);
        }
        Ok(())
    }

    /// The diagnostic `problem` is, and the file it is for. `None` when the
    /// file can't be named to the editor.
    fn diagnostic(&self, problem: Problem) -> Option<(Uri, Diagnostic)> {
        let notes = problem.notes.into_iter().filter_map(|note| {
            Some(DiagnosticRelatedInformation {
                location: Location {
                    uri: self.uri_of(&note.place.path)?,
                    range: note.place.range,
                },
                message: note.message,
            })
        });
        let notes: Vec<_> = notes.collect();
        let Place { path, range } = problem.place;
        let diagnostic = Diagnostic {
            range,
            severity: Some(DiagnosticSeverity::ERROR),
            source: Some("duck".to_string()),
            message: problem.message,
            related_information: (!notes.is_empty()).then_some(notes),
            ..Diagnostic::default()
        };
        Some((self.uri_of(&path)?, diagnostic))
    }

    /// What the editor calls the file at the canonical path `path`.
    fn uri_of(&self, path: &Path) -> Option<Uri> {
        if let Some(document) = self.documents.get(path) {
            return Some(document.uri.clone());
        }
        let url = Url::from_file_path(path).ok()?;
        Uri::from_str(url.as_str()).ok()
    }
}

/// What the server asks of the editor: the whole text of each file it has
/// open, whenever it changes.
fn capabilities() -> ServerCapabilities {
    let sync = TextDocumentSyncOptions {
        open_close: Some(true),
        change: Some(TextDocumentSyncKind::FULL),
        save: Some(TextDocumentSyncSaveOptions::Supported(true)),
        ..TextDocumentSyncOptions::default()
    };
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Options(sync)),
        ..ServerCapabilities::default()
    }
}

/// The directories the editor has open.
fn folders(params: &InitializeParams) -> Vec<PathBuf> {
    if let Some(folders) = &params.workspace_folders {
        return folders.iter().filter_map(|f| path_of(&f.uri)).collect();
    }
    // What editors from before workspace folders send.
    #[allow(deprecated)]
    let root = params.root_uri.as_ref();
    root.and_then(path_of).into_iter().collect()
}

/// Whether the editor watches files only once asked to.
fn watches_on_request(params: &InitializeParams) -> bool {
    let workspace = params.capabilities.workspace.as_ref();
    let watching = workspace.and_then(|workspace| workspace.did_change_watched_files);
    watching.and_then(|watching| watching.dynamic_registration) == Some(true)
}

/// The canonical path of the file `uri` names, if it names one on disk.
fn path_of(uri: &Uri) -> Option<PathBuf> {
    let path = Url::parse(uri.as_str()).ok()?.to_file_path().ok()?;
    Some(project::canonical(&path))
}

#[cfg(test)]
mod tests {
    use std::thread;
    use std::time::Duration;

    use lsp_types::notification::{Exit, Initialized};
    use lsp_types::request::{Initialize, Shutdown};
    use serde_json::{Value, json};

    use super::*;
    use crate::project::tests::{MODULE, TempDir};

    /// An editor at the other end of a server's connection.
    struct Editor {
        connection: Connection,
        server: thread::JoinHandle<()>,
        requests: i32,
    }

    impl Editor {
        /// Starts a server and initializes it with `dir` open.
        fn start(dir: &TempDir, capabilities: Value) -> Self {
            let (server, connection) = Connection::memory();
            let cache = Cache::new(dir.0.join("no-cache"));
            let server = thread::spawn(move || run(&server, cache).unwrap());
            let mut editor = Self {
                connection,
                server,
                requests: 0,
            };
            let folder = json!({ "uri": uri(&dir.0), "name": "dir" });
            let params = json!({ "capabilities": capabilities, "workspaceFolders": [folder] });
            let result = editor.request(Initialize::METHOD, params);
            assert_eq!(result["serverInfo"]["name"], "duck-lsp");
            assert_eq!(result["capabilities"]["textDocumentSync"]["change"], 1);
            editor.notify(Initialized::METHOD, json!({}));
            editor
        }

        fn notify(&self, method: &str, params: Value) {
            let notification = Notification::new(method.to_string(), params);
            self.connection.sender.send(notification.into()).unwrap();
        }

        /// Sends a request and waits for its result.
        fn request(&mut self, method: &str, params: Value) -> Value {
            self.requests += 1;
            let id = RequestId::from(self.requests);
            let request = Request::new(id.clone(), method.to_string(), params);
            self.connection.sender.send(request.into()).unwrap();
            match self.receive() {
                Message::Response(response) if response.id == id => {
                    response.response_result.unwrap()
                }
                message => panic!("{message:?}"),
            }
        }

        fn receive(&self) -> Message {
            let timeout = Duration::from_secs(10);
            self.connection.receiver.recv_timeout(timeout).unwrap()
        }

        fn open(&self, path: &Path, text: &str) {
            let document =
                json!({ "uri": uri(path), "languageId": "duck", "version": 1, "text": text });
            self.notify(
                DidOpenTextDocument::METHOD,
                json!({ "textDocument": document }),
            );
        }

        fn change(&self, path: &Path, version: i32, text: &str) {
            let document = json!({ "uri": uri(path), "version": version });
            let params = json!({ "textDocument": document, "contentChanges": [{ "text": text }] });
            self.notify(DidChangeTextDocument::METHOD, params);
        }

        /// The next diagnostics the server publishes: the file they are
        /// for, relative to `dir`, the version of it they are for, and each
        /// as `line:column message`.
        fn diagnostics(&self, dir: &TempDir) -> (String, Option<i32>, Vec<String>) {
            let Message::Notification(notification) = self.receive() else {
                panic!("not a notification")
            };
            assert_eq!(notification.method, PublishDiagnostics::METHOD);
            let params: PublishDiagnosticsParams =
                serde_json::from_value(notification.params).unwrap();
            let path = path_of(&params.uri).unwrap();
            let path = path.strip_prefix(&dir.0).unwrap().display().to_string();
            let diagnostics = params.diagnostics.iter().map(|d| {
                assert_eq!(d.severity, Some(DiagnosticSeverity::ERROR));
                let start = d.range.start;
                format!("{}:{} {}", start.line, start.character, d.message)
            });
            (path, params.version, diagnostics.collect())
        }

        /// Shuts the server down, which must have nothing more to say.
        fn stop(mut self) {
            self.request(Shutdown::METHOD, Value::Null);
            self.notify(Exit::METHOD, Value::Null);
            self.server.join().unwrap();
            assert!(self.connection.receiver.try_recv().is_err());
        }
    }

    fn uri(path: &Path) -> String {
        Url::from_file_path(path).unwrap().to_string()
    }

    /// What [`Editor::diagnostics`] gives.
    fn published(
        file: &str,
        version: Option<i32>,
        diagnostics: &[&str],
    ) -> (String, Option<i32>, Vec<String>) {
        let diagnostics = diagnostics.iter().map(|d| d.to_string());
        (file.to_string(), version, diagnostics.collect())
    }

    #[test]
    fn diagnostics_follow_the_editor() {
        let dir = TempDir::new("server");
        dir.write(&[
            ("Duck.toml", MODULE),
            ("main.duck", "import \"a.duck\"\nlet x = a.y\n"),
            ("a.duck", "pub let y: Nope = 1\n"),
        ]);
        let main = dir.0.join("main.duck");
        let a = dir.0.join("a.duck");

        // The package of the open directory is checked before any file is
        // open.
        let editor = Editor::start(&dir, json!({}));
        let error = "0:11 unknown type `Nope`";
        assert_eq!(
            editor.diagnostics(&dir),
            published("a.duck", None, &[error])
        );

        // Unsaved changes are checked, and fix errors in files that import
        // the changed one.
        editor.open(&a, "pub let y: Nope = 1\n");
        editor.change(&a, 2, "pub let z = 1\n");
        let error = "1:10 `a` has no item `y`";
        assert_eq!(editor.diagnostics(&dir), published("a.duck", Some(2), &[]));
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", None, &[error])
        );

        editor.open(&main, "import \"a.duck\"\nlet x = a.y\n");
        editor.change(&main, 2, "import \"a.duck\"\n\nlet x = a.y\n");
        let error = "2:10 `a` has no item `y`";
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", Some(2), &[error])
        );

        // Closing a file leaves it as it was saved.
        let params = json!({ "textDocument": { "uri": uri(&a) } });
        editor.notify(DidCloseTextDocument::METHOD, params);
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", Some(2), &[])
        );
        assert_eq!(
            editor.diagnostics(&dir),
            published("a.duck", None, &["0:11 unknown type `Nope`"])
        );
        editor.stop();
    }

    #[test]
    fn manifests_are_read_again_when_saved() {
        let dir = TempDir::new("server-manifest");
        dir.write(&[("Duck.toml", "[library]\n"), ("lib.duck", "")]);
        let mut editor = Editor::start(
            &dir,
            json!({ "workspace": { "didChangeWatchedFiles": { "dynamicRegistration": true } } }),
        );
        let Message::Request(request) = editor.receive() else {
            panic!("not a request")
        };
        assert_eq!(request.method, RegisterCapability::METHOD);
        let watchers = &request.params["registrations"][0]["registerOptions"]["watchers"];
        assert_eq!(watchers[0]["globPattern"], "**/*.duck");
        assert_eq!(watchers[1]["globPattern"], "**/Duck.toml");
        let error = "0:0 missing field `entry`";
        assert_eq!(
            editor.diagnostics(&dir),
            published("Duck.toml", None, &[error])
        );

        dir.write(&[("Duck.toml", "[library]\nentry = \"lib.duck\"\n")]);
        let params = json!({ "textDocument": { "uri": uri(&dir.0.join("Duck.toml")) } });
        editor.notify(DidSaveTextDocument::METHOD, params);
        assert_eq!(editor.diagnostics(&dir), published("Duck.toml", None, &[]));

        // Changes to files that aren't open are checked once the editor
        // tells of them.
        dir.write(&[("lib.duck", "let x = @\n")]);
        let change = json!({ "uri": uri(&dir.0.join("lib.duck")), "type": 2 });
        editor.notify(
            DidChangeWatchedFiles::METHOD,
            json!({ "changes": [change] }),
        );
        let error = "0:8 unexpected character '@'";
        assert_eq!(
            editor.diagnostics(&dir),
            published("lib.duck", None, &[error])
        );

        // Requests for anything else are refused, not left unanswered.
        editor.requests += 1;
        let id = RequestId::from(editor.requests);
        let hover = Request::new(id.clone(), "textDocument/hover".to_string(), json!({}));
        editor.connection.sender.send(hover.into()).unwrap();
        let Message::Response(response) = editor.receive() else {
            panic!("not a response")
        };
        assert_eq!(response.id, id);
        let error = response.response_result.unwrap_err();
        assert_eq!(error.code, ErrorCode::MethodNotFound as i32);
        editor.stop();
    }
}

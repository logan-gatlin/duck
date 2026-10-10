//! The language server: keeps what the editor has open, publishes the
//! errors of the packages those files are in whenever one changes, and
//! answers what the editor asks of a place in one.

use std::collections::{BTreeMap, BTreeSet, HashMap, VecDeque};
use std::error::Error;
use std::panic;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use duck::git::Cache;
use duck::manifest::MANIFEST;
use duck_compiler::ty::{self, CompletionKind, HintKind, SymbolKind};
use duck_compiler::{format, lex};
use lsp_server::{Connection, ErrorCode, Message, Notification, Request, RequestId, Response};
use lsp_types::notification::{
    Cancel, DidChangeTextDocument, DidChangeWatchedFiles, DidChangeWorkspaceFolders,
    DidCloseTextDocument, DidOpenTextDocument, DidSaveTextDocument, Exit, Notification as _,
    PublishDiagnostics,
};
use lsp_types::request::{
    CodeActionRequest, Completion, DocumentHighlightRequest, DocumentSymbolRequest, Formatting,
    GotoDefinition, GotoImplementation, GotoTypeDefinition, HoverRequest, InlayHintRequest,
    PrepareRenameRequest, References, RegisterCapability, Rename, Request as _, Shutdown,
    SignatureHelpRequest, WorkspaceSymbolRequest,
};
use lsp_types::{
    CancelParams, CodeAction, CodeActionKind, CodeActionOrCommand, CodeActionParams,
    CodeActionProviderCapability, CompletionItem, CompletionItemKind, CompletionOptions,
    CompletionParams, Diagnostic, DiagnosticRelatedInformation, DiagnosticSeverity, DiagnosticTag,
    DidChangeTextDocumentParams, DidChangeWatchedFilesRegistrationOptions,
    DidChangeWorkspaceFoldersParams, DidCloseTextDocumentParams, DidOpenTextDocumentParams,
    DocumentChangeOperation, DocumentChanges, DocumentFormattingParams, DocumentHighlight,
    DocumentHighlightParams, DocumentSymbol, DocumentSymbolParams, FileSystemWatcher, GlobPattern,
    GotoDefinitionParams, Hover, HoverContents, HoverParams, HoverProviderCapability,
    ImplementationProviderCapability, InitializeParams, InitializeResult, InlayHint, InlayHintKind,
    InlayHintLabel, InlayHintParams, Location, MarkupContent, MarkupKind, NumberOrString, OneOf,
    OptionalVersionedTextDocumentIdentifier, ParameterInformation, ParameterLabel, Position,
    PublishDiagnosticsParams, Range, ReferenceParams, Registration, RegistrationParams, RenameFile,
    RenameOptions, RenameParams, ResourceOp, ResourceOperationKind, ServerCapabilities, ServerInfo,
    SignatureHelp, SignatureHelpOptions, SignatureHelpParams, SignatureInformation,
    SymbolInformation, TextDocumentEdit, TextDocumentPositionParams, TextDocumentSyncCapability,
    TextDocumentSyncKind, TextDocumentSyncOptions, TextDocumentSyncSaveOptions, TextEdit,
    TypeDefinitionProviderCapability, Uri, WorkspaceEdit, WorkspaceFoldersServerCapabilities,
    WorkspaceServerCapabilities, WorkspaceSymbolParams,
};
use serde::Serialize;
use serde::de::DeserializeOwned;
use url::Url;

use super::changes;
use super::project::{self, Mend, Outline, Place, Problem, Project, Renaming, Suggestion};

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
    /// Whether the editor renames a file when a change says to.
    renames_files: bool,
}

/// A file as it is in the editor, saved or not.
struct Document {
    /// What the editor calls it, which need not be its canonical path.
    uri: Uri,
    version: i32,
    text: String,
}

/// The words of the language that a name can be written in place of.
const KEYWORDS: [&str; 27] = [
    "and", "as", "break", "continue", "defer", "else", "enum", "extern", "false", "fn", "for",
    "if", "in", "let", "match", "module", "not", "or", "pass", "pub", "return", "struct", "true",
    "union", "use", "var", "while",
];

/// What marks the source in a hover as duck, for an editor to highlight.
const LANGUAGE: &str = "duck";

/// What the file of a module is named after the module.
const EXTENSION: &str = "duck";

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
        renames_files: renames_files(&params),
    };
    if watches_on_request(&params) {
        server.watch()?;
    }
    server.publish()?;
    // What the editor has sent and is yet to be answered, in order.
    let mut waiting: VecDeque<Message> = VecDeque::new();
    loop {
        waiting.extend(connection.receiver.try_iter());
        let message = match waiting.pop_front() {
            Some(message) => message,
            None => match connection.receiver.recv() {
                Ok(message) => message,
                Err(_) => return Ok(()),
            },
        };
        match message {
            Message::Request(request) if request.method == Shutdown::METHOD => {
                let response = Response::new_ok(request.id, ());
                connection.sender.send(response.into())?;
            }
            // One that the editor has since said it no longer waits for is
            // not worked out.
            Message::Request(request) if cancelled(&mut waiting, &request.id) => {
                let code = ErrorCode::RequestCanceled as i32;
                let response = Response::new_err(request.id, code, "cancelled".to_string());
                connection.sender.send(response.into())?;
            }
            Message::Request(request) => server.requested(request)?,
            Message::Notification(notification) if notification.method == Exit::METHOD => {
                return Ok(());
            }
            Message::Notification(notification) => server.notified(notification),
            Message::Response(_) => {}
        }
        // One check answers every change the editor has sent so far.
        if server.stale && waiting.is_empty() && connection.receiver.is_empty() {
            server.publish()?;
        }
    }
}

/// Whether the editor has said, among what is `waiting`, that it no longer
/// waits for the answer to request `id`. That it said so is then forgotten.
fn cancelled(waiting: &mut VecDeque<Message>, id: &RequestId) -> bool {
    let cancels = |message: &Message| {
        let Message::Notification(notification) = message else {
            return false;
        };
        let params = serde_json::from_value::<CancelParams>(notification.params.clone());
        let cancelled = params.ok().map(|params| match params.id {
            NumberOrString::Number(id) => RequestId::from(id),
            NumberOrString::String(id) => RequestId::from(id),
        });
        notification.method == Cancel::METHOD && cancelled.as_ref() == Some(id)
    };
    match waiting.iter().position(cancels) {
        Some(index) => waiting.remove(index).is_some(),
        None => false,
    }
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

    /// Answers a request, or refuses one for something the server doesn't
    /// do.
    fn requested(&mut self, request: Request) -> Fallible {
        let Request { id, method, params } = request;
        match method.as_str() {
            HoverRequest::METHOD
            | GotoDefinition::METHOD
            | GotoTypeDefinition::METHOD
            | GotoImplementation::METHOD
            | References::METHOD
            | DocumentHighlightRequest::METHOD
            | DocumentSymbolRequest::METHOD
            | WorkspaceSymbolRequest::METHOD
            | InlayHintRequest::METHOD
            | CodeActionRequest::METHOD
            | PrepareRenameRequest::METHOD
            | Rename::METHOD => {
                // What is written is answered of as it was last checked.
                if self.stale {
                    self.publish()?;
                }
                match method.as_str() {
                    HoverRequest::METHOD => self.answer(id, params, Self::hover),
                    GotoDefinition::METHOD => self.answer(id, params, Self::definition),
                    GotoTypeDefinition::METHOD => self.answer(id, params, Self::type_definition),
                    References::METHOD => self.answer(id, params, Self::references),
                    DocumentHighlightRequest::METHOD => self.answer(id, params, Self::highlights),
                    DocumentSymbolRequest::METHOD => self.answer(id, params, Self::symbols),
                    WorkspaceSymbolRequest::METHOD => self.answer(id, params, Self::all_symbols),
                    InlayHintRequest::METHOD => self.answer(id, params, Self::hints),
                    CodeActionRequest::METHOD => self.answer(id, params, Self::actions),
                    PrepareRenameRequest::METHOD => self.attempt(id, params, Self::renamed),
                    Rename::METHOD => self.attempt(id, params, Self::rename),
                    _ => self.answer(id, params, Self::implementations),
                }
            }
            Completion::METHOD => self.answer(id, params, Self::complete),
            Formatting::METHOD => self.answer(id, params, Self::format),
            SignatureHelpRequest::METHOD => self.answer(id, params, Self::signature),
            _ => {
                let message = format!("unknown request `{method}`");
                let code = ErrorCode::MethodNotFound as i32;
                let response = Response::new_err(id, code, message);
                self.connection.sender.send(response.into())?;
                Ok(())
            }
        }
    }

    /// Answers request `id` with what `answer` makes of its `params`.
    fn answer<P: DeserializeOwned, R: Serialize>(
        &mut self,
        id: RequestId,
        params: serde_json::Value,
        answer: impl FnOnce(&mut Self, P) -> R,
    ) -> Fallible {
        let response = match serde_json::from_value(params) {
            Ok(params) => Response::new_ok(id, answer(self, params)),
            Err(e) => Response::new_err(id, ErrorCode::InvalidParams as i32, e.to_string()),
        };
        self.connection.sender.send(response.into())?;
        Ok(())
    }

    /// Answers request `id` with what `attempt` makes of its `params`, or
    /// with why it makes nothing of them.
    fn attempt<P: DeserializeOwned, R: Serialize>(
        &mut self,
        id: RequestId,
        params: serde_json::Value,
        attempt: impl FnOnce(&mut Self, P) -> Result<R, String>,
    ) -> Fallible {
        let response = match serde_json::from_value(params) {
            Ok(params) => match attempt(self, params) {
                Ok(result) => Response::new_ok(id, result),
                Err(why) => Response::new_err(id, ErrorCode::RequestFailed as i32, why),
            },
            Err(e) => Response::new_err(id, ErrorCode::InvalidParams as i32, e.to_string()),
        };
        self.connection.sender.send(response.into())?;
        Ok(())
    }

    /// What is written at a place in a file: its declaration or its type,
    /// as source.
    fn hover(&mut self, params: HoverParams) -> Option<Hover> {
        let at = params.text_document_position_params;
        let (range, text, docs) = self.ask(at, Project::hover)?;
        let mut value = format!("```{LANGUAGE}\n{text}\n```");
        if !docs.is_empty() {
            // Each line of a comment is a line, indented as it is.
            let line = |line: &str| {
                let said = line.trim_start_matches(' ');
                format!("{}{said}", "\u{a0}".repeat(line.len() - said.len()))
            };
            let lines: Vec<_> = docs.lines().map(line).collect();
            value = format!("{value}\n\n---\n\n{}", lines.join("  \n"));
        }
        Some(Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value,
            }),
            range: Some(range),
        })
    }

    /// Where the type of what is at a place in a file is declared.
    fn type_definition(&mut self, params: GotoDefinitionParams) -> Option<Location> {
        let at = params.text_document_position_params;
        let place = self.ask(at, Project::type_definition)?;
        self.location(place)
    }

    /// Where the name at a place in a file is written in that file, for
    /// what it stands for there.
    fn highlights(&mut self, params: DocumentHighlightParams) -> Vec<DocumentHighlight> {
        let at = params.text_document_position_params;
        let ranges = self.ask(at, |project, buffers, path, position| {
            Some(project.highlights(buffers, path, position))
        });
        let highlight = |range| DocumentHighlight { range, kind: None };
        ranges.into_iter().flatten().map(highlight).collect()
    }

    /// What a file declares, each with what it is made of.
    fn symbols(&mut self, params: DocumentSymbolParams) -> Vec<DocumentSymbol> {
        // No symbol is deprecated, which the field that says so is.
        #[allow(deprecated)]
        fn symbol(outline: Outline) -> DocumentSymbol {
            DocumentSymbol {
                name: outline.name,
                detail: None,
                kind: symbol_kind(outline.kind),
                tags: None,
                deprecated: None,
                range: outline.range,
                selection_range: outline.named,
                children: Some(outline.children.into_iter().map(symbol).collect()),
            }
        }
        let Some(path) = path_of(&params.text_document.uri) else {
            return Vec::new();
        };
        let root = project::root_of(&path);
        let Some(project) = root.and_then(|root| self.projects.get_mut(&root)) else {
            return Vec::new();
        };
        let documents = &self.documents;
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        let outlines = project.symbols(&buffers, &path);
        outlines.into_iter().map(symbol).collect()
    }

    /// What the packages the editor has open declare whose names have the
    /// letters asked for, in order: every one, if none are.
    fn all_symbols(&mut self, params: WorkspaceSymbolParams) -> Vec<SymbolInformation> {
        let query: Vec<char> = params.query.to_lowercase().chars().collect();
        let asked = |name: &str| {
            let mut letters = name.chars().flat_map(char::to_lowercase);
            query
                .iter()
                .all(|wanted| letters.any(|letter| letter == *wanted))
        };
        let documents = &self.documents;
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        let mut declared: Vec<(PathBuf, Vec<Outline>)> = Vec::new();
        for project in self.projects.values_mut() {
            for (path, outlines) in project.all_symbols(&buffers) {
                if !declared.iter().any(|(known, _)| *known == path) {
                    declared.push((path, outlines));
                }
            }
        }
        declared.sort_by(|a, b| a.0.cmp(&b.0));
        let mut symbols = Vec::new();
        for (path, outlines) in declared {
            let Some(uri) = self.uri_of(&path) else {
                continue;
            };
            // No symbol is deprecated, which the field that says so is.
            #[allow(deprecated)]
            let mut symbol = |outline: &Outline, container: Option<&str>| {
                symbols.extend(asked(&outline.name).then(|| SymbolInformation {
                    name: outline.name.clone(),
                    kind: symbol_kind(outline.kind),
                    tags: None,
                    deprecated: None,
                    location: Location {
                        uri: uri.clone(),
                        range: outline.named,
                    },
                    container_name: container.map(str::to_string),
                }));
            };
            for outline in &outlines {
                symbol(outline, None);
                for child in &outline.children {
                    symbol(child, Some(&outline.name));
                }
            }
        }
        symbols
    }

    /// What to show in part of a file as if it were written there.
    fn hints(&mut self, params: InlayHintParams) -> Vec<InlayHint> {
        let Some(path) = path_of(&params.text_document.uri) else {
            return Vec::new();
        };
        let root = project::root_of(&path);
        let Some(project) = root.and_then(|root| self.projects.get_mut(&root)) else {
            return Vec::new();
        };
        let documents = &self.documents;
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        let hints = project.hints(&buffers, &path, params.range).into_iter();
        let hint = |(position, label, kind): (Position, String, HintKind)| InlayHint {
            position,
            label: InlayHintLabel::String(label),
            kind: Some(match kind {
                HintKind::Type => InlayHintKind::TYPE,
                HintKind::Parameter => InlayHintKind::PARAMETER,
            }),
            text_edits: None,
            tooltip: None,
            padding_left: None,
            padding_right: None,
            data: None,
        };
        hints.map(hint).collect()
    }

    /// What mends the errors in part of a file.
    // A `Uri` only mutates what it remembers of parsing itself, which its
    // hash doesn't read.
    #[allow(clippy::mutable_key_type)]
    fn actions(&mut self, params: CodeActionParams) -> Vec<CodeActionOrCommand> {
        let Some(path) = path_of(&params.text_document.uri) else {
            return Vec::new();
        };
        let root = project::root_of(&path);
        let Some(project) = root.and_then(|root| self.projects.get_mut(&root)) else {
            return Vec::new();
        };
        let documents = &self.documents;
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        let mends = project.mends(&buffers, &path, params.range);
        let action = |Mend { title, edits }: Mend| {
            let mut changes: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
            for (Place { path, range }, new_text) in edits {
                let edit = TextEdit { range, new_text };
                changes.entry(self.uri_of(&path)?).or_default().push(edit);
            }
            Some(CodeActionOrCommand::CodeAction(CodeAction {
                title,
                kind: Some(CodeActionKind::QUICKFIX),
                edit: Some(WorkspaceEdit {
                    changes: Some(changes),
                    ..WorkspaceEdit::default()
                }),
                ..CodeAction::default()
            }))
        };
        mends.into_iter().filter_map(action).collect()
    }

    /// Where what the name at a place in a file stands for is declared.
    fn definition(&mut self, params: GotoDefinitionParams) -> Option<Location> {
        let place = self.ask(params.text_document_position_params, Project::definition)?;
        self.location(place)
    }

    /// Where each type that is given for one bounded by the type named at
    /// a place in a file is declared.
    fn implementations(&mut self, params: GotoDefinitionParams) -> Vec<Location> {
        let at = params.text_document_position_params;
        let places = self.ask(at, |project, buffers, path, position| {
            Some(project.implementations(buffers, path, position))
        });
        let locations = places.into_iter().flatten();
        locations.filter_map(|place| self.location(place)).collect()
    }

    /// What changes lay out a file the editor has open as the language is
    /// written, as `duck format` does, each no more of it than differs.
    /// `None` for one that doesn't parse, which is left as it is.
    fn format(&mut self, params: DocumentFormattingParams) -> Option<Vec<TextEdit>> {
        let path = path_of(&params.text_document.uri)?;
        let text = &self.documents.get(&path)?.text;
        // A bug in the formatter shouldn't end the server.
        let formatted = panic::catch_unwind(|| format::format(text)).ok()?.ok()?;
        let changes = changes::changes(text, &formatted).into_iter();
        let edits = changes.map(|(replaced, new_text)| TextEdit {
            range: project::range(text, replaced.start, replaced.end),
            new_text,
        });
        Some(edits.collect())
    }

    /// Where each name is written that stands for what the name at a place
    /// in a file does: in the package the file is in, and in every other
    /// that the editor has open and that uses what the name is declared in.
    fn references(&mut self, params: ReferenceParams) -> Vec<Location> {
        let at = params.text_document_position;
        let declared = params.context.include_declaration;
        let found = self.ask(at.clone(), |project, buffers, path, position| {
            Some(project.references(buffers, path, position, declared))
        });
        let mut places = found.unwrap_or_default();
        // Another package knows the name by where it is declared, which a
        // module isn't at any one place.
        let named = |place: &Place| place.range.start != place.range.end;
        let declaration = self.ask(at, Project::definition).filter(named);
        let documents = &self.documents;
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        for project in self.projects.values_mut() {
            let Some(Place { path, range }) = &declaration else {
                break;
            };
            for place in project.references(&buffers, path, range.start, declared) {
                if !places.contains(&place) {
                    places.push(place);
                }
            }
        }
        let locations = places.into_iter();
        locations.filter_map(|place| self.location(place)).collect()
    }

    /// The name at a place in a file that another can be written for, if
    /// there is one: all of it.
    fn renamed(&mut self, at: TextDocumentPositionParams) -> Result<Option<Range>, String> {
        Ok(self.renaming(at)?.map(|renaming| renaming.at))
    }

    /// The changes that write `new_name` for the name at a place in a file,
    /// wherever it is written so and stands for the same.
    // A `Uri` only mutates what it remembers of parsing itself, which its
    // hash doesn't read.
    #[allow(clippy::mutable_key_type)]
    fn rename(&mut self, params: RenameParams) -> Result<Option<WorkspaceEdit>, String> {
        let name = params.new_name;
        if !lex::is_identifier(&name) {
            return Err(format!("`{name}` is not a name"));
        }
        let at = params.text_document_position;
        let Some(renaming) = self.renaming(at.clone())? else {
            return Ok(None);
        };
        let old = &renaming.name;
        let collides = self.ask(at, |project, buffers, path, position| {
            project
                .collides(buffers, path, position, &name)
                .then_some(())
        });
        if collides.is_some() {
            return Err(format!(
                "cannot rename `{old}` to `{name}`: something is named `{name}` where it is"
            ));
        }
        let mut changes: HashMap<Uri, Vec<TextEdit>> = HashMap::new();
        for Place { path, range } in &renaming.places {
            if self.cache.holds(path) {
                let path = path.display();
                return Err(format!(
                    "cannot rename `{old}`: {path} is of a dependency that git fetched"
                ));
            }
            let Some(uri) = self.uri_of(path) else {
                return Err(format!("cannot name {} to the editor", path.display()));
            };
            let edit = TextEdit {
                range: *range,
                new_text: name.clone(),
            };
            changes.entry(uri).or_default().push(edit);
        }
        let Some(module) = &renaming.module else {
            return Ok(Some(WorkspaceEdit {
                changes: Some(changes),
                ..WorkspaceEdit::default()
            }));
        };
        // A module is named as its file is, which is renamed once every
        // file that names it is changed.
        let renamed = module.with_file_name(format!("{name}.{EXTENSION}"));
        let (from, to) = (self.uri_of(module), self.uri_of(&renamed));
        let (Some(from), Some(to), true) = (from, to, self.renames_files) else {
            return Err(format!(
                "cannot rename `{old}`: the editor doesn't rename {} when asked to",
                module.display()
            ));
        };
        if renamed.exists() || module.with_file_name(&name).is_dir() {
            return Err(format!(
                "cannot rename `{old}` to `{name}`: a module is named `{name}` there"
            ));
        }
        let edits = changes.into_iter().map(|(uri, edits)| {
            DocumentChangeOperation::Edit(TextDocumentEdit {
                text_document: OptionalVersionedTextDocumentIdentifier { uri, version: None },
                edits: edits.into_iter().map(OneOf::Left).collect(),
            })
        });
        let rename = DocumentChangeOperation::Op(ResourceOp::Rename(RenameFile {
            old_uri: from,
            new_uri: to,
            options: None,
            annotation_id: None,
        }));
        Ok(Some(WorkspaceEdit {
            document_changes: Some(DocumentChanges::Operations(edits.chain([rename]).collect())),
            ..WorkspaceEdit::default()
        }))
    }

    /// What writing another name for the one at a place in a file changes:
    /// in the package the file is in, and in every other that the editor
    /// has open and that uses what the name is declared in.
    fn renaming(&mut self, at: TextDocumentPositionParams) -> Result<Option<Renaming>, String> {
        let renaming = self.ask(at.clone(), |project, buffers, path, position| {
            Some(project.rename(buffers, path, position))
        });
        let Some(mut renaming) = renaming.transpose()?.flatten() else {
            return Ok(None);
        };
        let Some(declared) = self.ask(at, Project::definition) else {
            return Ok(Some(renaming));
        };
        let documents = &self.documents;
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        for project in self.projects.values_mut() {
            // Another package names it as it is declared, if it is named
            // so here.
            let other = project.rename(&buffers, &declared.path, declared.range.start)?;
            let places = other.filter(|other| other.name == renaming.name);
            for place in places.into_iter().flat_map(|other| other.places) {
                if !renaming.places.contains(&place) {
                    renaming.places.push(place);
                }
            }
        }
        Ok(Some(renaming))
    }

    /// Asks `ask` of the package that the file at a place is in, as it was
    /// last checked, with the files the editor has open as they are there.
    fn ask<T>(
        &mut self,
        at: TextDocumentPositionParams,
        ask: impl FnOnce(&mut Project, project::Buffers<'_>, &Path, Position) -> Option<T>,
    ) -> Option<T> {
        let path = path_of(&at.text_document.uri)?;
        let project = self.projects.get_mut(&project::root_of(&path)?)?;
        let documents = &self.documents;
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        ask(project, &buffers, &path, at.position)
    }

    /// `place` as the editor is told of it. `None` when its file can't be
    /// named to the editor.
    fn location(&self, place: Place) -> Option<Location> {
        Some(Location {
            uri: self.uri_of(&place.path)?,
            range: place.range,
        })
    }

    /// What can be written at a place in a file the editor has open: the
    /// names in scope there and the words of the language, or what follows
    /// the `.` before it. Asked by something typed that isn't a `.`, only
    /// what the path of a `use` goes on with there, which is all that it
    /// asks for.
    fn complete(&mut self, params: CompletionParams) -> Vec<CompletionItem> {
        let TextDocumentPositionParams {
            text_document,
            position,
        } = params.text_document_position;
        let typed = params.context.and_then(|context| context.trigger_character);
        let used = typed.is_some_and(|typed| typed != ".");
        let Some((path, root)) = self.package_of(&text_document.uri) else {
            return Vec::new();
        };
        let (project, documents) = (&self.projects[&root], &self.documents);
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        let text = &documents[&path].text;
        let suggested = project.complete(&buffers, &path, text, position, used);
        let suggestions = suggested.suggestions.into_iter().enumerate();
        let item = |(index, suggestion): (usize, Suggestion)| {
            let Suggestion {
                completion,
                insert,
                import,
            } = suggestion;
            let import = import.map(|(at, new_text)| TextEdit {
                range: Range::new(at, at),
                new_text,
            });
            CompletionItem {
                label: completion.name,
                kind: Some(match completion.kind {
                    CompletionKind::Variable => CompletionItemKind::VARIABLE,
                    CompletionKind::Function => CompletionItemKind::FUNCTION,
                    CompletionKind::Struct | CompletionKind::Union => CompletionItemKind::STRUCT,
                    CompletionKind::Enum => CompletionItemKind::ENUM,
                    CompletionKind::Member | CompletionKind::Variant => {
                        CompletionItemKind::ENUM_MEMBER
                    }
                    CompletionKind::Field => CompletionItemKind::FIELD,
                    CompletionKind::Module => CompletionItemKind::MODULE,
                    CompletionKind::Type => CompletionItemKind::TYPE_PARAMETER,
                }),
                detail: (!completion.detail.is_empty()).then_some(completion.detail),
                insert_text: insert,
                additional_text_edits: import.map(|import| vec![import]),
                // The nearest are first, where the editor has nothing else
                // to order them by.
                sort_text: Some(format!("{index:05}")),
                ..CompletionItem::default()
            }
        };
        let completions = suggestions.map(item);
        let keywords = KEYWORDS
            .iter()
            .filter(|_| suggested.names)
            .map(|keyword| CompletionItem {
                label: keyword.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                sort_text: Some(format!("{}{keyword}", u32::MAX)),
                ..CompletionItem::default()
            });
        completions.chain(keywords).collect()
    }

    /// What the call takes whose arguments a place in a file the editor has
    /// open is in, and which of them the one there is.
    fn signature(&mut self, params: SignatureHelpParams) -> Option<SignatureHelp> {
        let TextDocumentPositionParams {
            text_document,
            position,
        } = params.text_document_position_params;
        let (path, root) = self.package_of(&text_document.uri)?;
        let (project, documents) = (&self.projects[&root], &self.documents);
        let buffers = |path: &Path| Some(documents.get(path)?.text.as_str());
        let text = &documents[&path].text;
        let (signature, active) = project.signature(&buffers, &path, text, position)?;
        let ty::Signature { label, params } = signature;
        // The editor counts in UTF-16 code units here, too.
        let units = |end: usize| label[..end].encode_utf16().count() as u32;
        let params = params.iter().map(|param| ParameterInformation {
            label: ParameterLabel::LabelOffsets([units(param.range.start), units(param.range.end)]),
            documentation: None,
        });
        let active = active.map(|active| active as u32);
        let signature = SignatureInformation {
            parameters: Some(params.collect()),
            label,
            documentation: None,
            active_parameter: active,
        };
        Some(SignatureHelp {
            signatures: vec![signature],
            active_signature: Some(0),
            active_parameter: active,
        })
    }

    /// The canonical path of the file `uri` names, which the editor has
    /// open, and the directory of the package it is in, which is resolved
    /// if it wasn't.
    fn package_of(&mut self, uri: &Uri) -> Option<(PathBuf, PathBuf)> {
        let path = path_of(uri).filter(|path| self.documents.contains_key(path))?;
        let root = project::root_of(&path)?;
        (self.projects.entry(root.clone()))
            .or_insert_with(|| Project::resolve(root.clone(), &self.cache));
        Some((path, root))
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
                    content_changes,
                } = params;
                let path = path_of(&text_document.uri);
                let Some(document) = path.and_then(|path| self.documents.get_mut(&path)) else {
                    return;
                };
                document.version = text_document.version;
                // Each change is to the text that the one before it left: a
                // part of it, or all of it where none is said.
                for change in content_changes {
                    match change.range {
                        Some(range) => {
                            let text = &document.text;
                            let start = project::offset(text, range.start);
                            let end = project::offset(text, range.end).max(start);
                            document.text.replace_range(start..end, &change.text);
                        }
                        None => document.text = change.text,
                    }
                }
                // The manifests are as they were, as they are read saved.
                self.stale = true;
                return;
            }
            DidChangeWorkspaceFolders::METHOD => {
                let params = serde_json::from_value::<DidChangeWorkspaceFoldersParams>(params);
                let Ok(DidChangeWorkspaceFoldersParams { event }) = params else {
                    return;
                };
                let paths = |folders: Vec<lsp_types::WorkspaceFolder>| -> Vec<PathBuf> {
                    folders.iter().filter_map(|f| path_of(&f.uri)).collect()
                };
                let removed = paths(event.removed);
                self.folders.retain(|folder| !removed.contains(folder));
                self.folders.extend(paths(event.added));
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
            let errors = problems.into_iter().map(|problem| (problem, true));
            let warnings = project
                .warnings()
                .iter()
                .map(|problem| (problem.clone(), false));
            let problems: Vec<_> = errors.chain(warnings).collect();
            for (problem, error) in problems {
                let Some((uri, diagnostic)) = self.diagnostic(problem, error) else {
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
    fn diagnostic(&self, problem: Problem, error: bool) -> Option<(Uri, Diagnostic)> {
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
            severity: Some(match error {
                true => DiagnosticSeverity::ERROR,
                false => DiagnosticSeverity::WARNING,
            }),
            // What is never used is shown as what could be taken away.
            tags: (!error).then(|| vec![DiagnosticTag::UNNECESSARY]),
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

/// What the server asks of the editor, each change to each file it has
/// open and to the directories it has open, and what it answers: what is at
/// a place, where it and its type are declared, where else it is named,
/// what naming it otherwise changes and what a type there bounds, what a
/// file and every file declares, what isn't written and would say more,
/// what mends an error, what can be written after a `.` or anywhere, what a
/// call takes once it is opened or goes on to another argument, and how a
/// file is laid out.
fn capabilities() -> ServerCapabilities {
    let sync = TextDocumentSyncOptions {
        open_close: Some(true),
        change: Some(TextDocumentSyncKind::INCREMENTAL),
        save: Some(TextDocumentSyncSaveOptions::Supported(true)),
        ..TextDocumentSyncOptions::default()
    };
    let triggers = |characters: &[&str]| Some(characters.iter().map(|c| c.to_string()).collect());
    ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Options(sync)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        definition_provider: Some(OneOf::Left(true)),
        type_definition_provider: Some(TypeDefinitionProviderCapability::Simple(true)),
        document_highlight_provider: Some(OneOf::Left(true)),
        document_symbol_provider: Some(OneOf::Left(true)),
        workspace_symbol_provider: Some(OneOf::Left(true)),
        inlay_hint_provider: Some(OneOf::Left(true)),
        code_action_provider: Some(CodeActionProviderCapability::Simple(true)),
        workspace: Some(WorkspaceServerCapabilities {
            workspace_folders: Some(WorkspaceFoldersServerCapabilities {
                supported: Some(true),
                change_notifications: Some(OneOf::Left(true)),
            }),
            file_operations: None,
        }),
        references_provider: Some(OneOf::Left(true)),
        rename_provider: Some(OneOf::Right(RenameOptions {
            prepare_provider: Some(true),
            work_done_progress_options: Default::default(),
        })),
        document_formatting_provider: Some(OneOf::Left(true)),
        implementation_provider: Some(ImplementationProviderCapability::Simple(true)),
        completion_provider: Some(CompletionOptions {
            // All but the `.` go on with the path of a `use`, in a group.
            trigger_characters: triggers(&[".", "{", ",", " "]),
            ..CompletionOptions::default()
        }),
        signature_help_provider: Some(SignatureHelpOptions {
            trigger_characters: triggers(&["(", ","]),
            ..SignatureHelpOptions::default()
        }),
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

/// Whether the editor renames a file when a change it is asked to make
/// says to.
fn renames_files(params: &InitializeParams) -> bool {
    let workspace = params.capabilities.workspace.as_ref();
    let edit = workspace.and_then(|workspace| workspace.workspace_edit.as_ref());
    let operations = edit.and_then(|edit| edit.resource_operations.as_ref());
    operations.is_some_and(|operations| operations.contains(&ResourceOperationKind::Rename))
}

/// What the editor calls a symbol of kind `kind`.
fn symbol_kind(kind: SymbolKind) -> lsp_types::SymbolKind {
    match kind {
        SymbolKind::Function => lsp_types::SymbolKind::FUNCTION,
        SymbolKind::Struct | SymbolKind::Union => lsp_types::SymbolKind::STRUCT,
        SymbolKind::Enum => lsp_types::SymbolKind::ENUM,
        SymbolKind::Variable => lsp_types::SymbolKind::VARIABLE,
        SymbolKind::Field => lsp_types::SymbolKind::FIELD,
        SymbolKind::Variant | SymbolKind::Member => lsp_types::SymbolKind::ENUM_MEMBER,
    }
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
    use crate::lsp::project::tests::{MODULE, TempDir};

    /// An editor at the other end of a server's connection.
    struct Editor {
        connection: Connection,
        server: thread::JoinHandle<()>,
        requests: i32,
        /// What the server said it does.
        capabilities: Value,
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
                capabilities: Value::Null,
            };
            let folder = json!({ "uri": uri(&dir.0), "name": "dir" });
            let params = json!({ "capabilities": capabilities, "workspaceFolders": [folder] });
            let result = editor.request(Initialize::METHOD, params);
            assert_eq!(result["serverInfo"]["name"], "duck");
            assert_eq!(result["capabilities"]["textDocumentSync"]["change"], 2);
            editor.capabilities = result["capabilities"].clone();
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

        /// Sends a request that the server fails, and gives why it did.
        fn failure(&mut self, method: &str, params: Value) -> String {
            self.requests += 1;
            let id = RequestId::from(self.requests);
            let request = Request::new(id.clone(), method.to_string(), params);
            self.connection.sender.send(request.into()).unwrap();
            match self.receive() {
                Message::Response(response) if response.id == id => {
                    let error = response.response_result.unwrap_err();
                    assert_eq!(error.code, ErrorCode::RequestFailed as i32);
                    error.message
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
        /// as `line:column message`, or `line:column warning: message`.
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
                let start = d.range.start;
                let warning = match d.severity {
                    Some(DiagnosticSeverity::ERROR) => "",
                    Some(DiagnosticSeverity::WARNING) => {
                        assert_eq!(d.tags, Some(vec![DiagnosticTag::UNNECESSARY]));
                        "warning: "
                    }
                    severity => panic!("{severity:?}"),
                };
                format!("{}:{} {warning}{}", start.line, start.character, d.message)
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
            ("main.duck", "use a\npub let x = a.y\n"),
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

        // Unsaved changes are checked, and fix errors in files that use the
        // changed one.
        editor.open(&a, "pub let y: Nope = 1\n");
        editor.change(&a, 2, "pub let z = 1\n");
        let error = "1:14 `a` has no item `y`";
        assert_eq!(editor.diagnostics(&dir), published("a.duck", Some(2), &[]));
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", None, &[error])
        );

        editor.open(&main, "use a\npub let x = a.y\n");
        editor.change(&main, 2, "use a\n\npub let x = a.y\n");
        let error = "2:14 `a` has no item `y`";
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

        // Requests for anything else are refused, not left unanswered, as
        // are those that don't say what they ask.
        let mut refused = |method: &str| {
            editor.requests += 1;
            let id = RequestId::from(editor.requests);
            let request = Request::new(id.clone(), method.to_string(), json!({}));
            editor.connection.sender.send(request.into()).unwrap();
            let Message::Response(response) = editor.receive() else {
                panic!("not a response")
            };
            assert_eq!(response.id, id);
            response.response_result.unwrap_err().code
        };
        assert_eq!(
            refused("textDocument/foldingRange"),
            ErrorCode::MethodNotFound as i32
        );
        assert_eq!(
            refused(HoverRequest::METHOD),
            ErrorCode::InvalidParams as i32
        );
        editor.stop();
    }

    #[test]
    fn a_file_is_laid_out_by_the_changes_that_format_it() {
        let dir = TempDir::new("server-format");
        dir.write(&[("Duck.toml", MODULE), ("main.duck", "")]);
        let main = dir.0.join("main.duck");
        let mut editor = Editor::start(&dir, json!({}));
        assert_eq!(editor.capabilities["documentFormattingProvider"], true);
        let params = json!({
            "textDocument": { "uri": uri(&main) },
            "options": { "tabSize": 4, "insertSpaces": false },
        });
        // Only a file that is open is, as it is in the editor.
        assert_eq!(
            editor.request(Formatting::METHOD, params.clone()),
            Value::Null
        );
        editor.open(
            &main,
            "pub fn  f(a:i32)->i32:\n    let é = a\n\n\n    return é+1\n",
        );
        let edit = |line: u32, start: u32, end_line: u32, end: u32, text: &str| {
            json!({
                "range": {
                    "start": { "line": line, "character": start },
                    "end": { "line": end_line, "character": end },
                },
                "newText": text,
            })
        };
        assert_eq!(
            editor.request(Formatting::METHOD, params.clone()),
            json!([
                edit(0, 7, 0, 8, ""),
                edit(0, 12, 0, 12, " "),
                edit(0, 16, 0, 16, " "),
                edit(0, 18, 0, 18, " "),
                edit(1, 0, 1, 4, "\t"),
                // A blank line goes with the indentation after it.
                edit(3, 0, 4, 4, "\t"),
                edit(4, 12, 4, 12, " "),
                edit(4, 13, 4, 13, " "),
            ])
        );
        // One that is laid out already has no changes, and one that doesn't
        // parse is left as it is.
        editor.change(&main, 2, "pub fn f():\n\tpass\n");
        assert_eq!(
            editor.request(Formatting::METHOD, params.clone()),
            json!([])
        );
        editor.change(&main, 3, "fn  f(: i32):\n    pass\n");
        let error = "0:6 expected identifier, found `:`";
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", Some(3), &[error])
        );
        assert_eq!(editor.request(Formatting::METHOD, params), Value::Null);
        editor.stop();
    }

    #[test]
    fn a_name_is_referred_to_in_every_package_that_is_open() {
        let dir = TempDir::new("server-references");
        let library = "[library]\nentry = \"lib.duck\"\n";
        let app = "use util\npub fn main():\n    util.log(1.0)\n";
        let util = "pub fn log(x: f32):\n    pass\npub fn twice():\n    log(2.0)\n";
        dir.write(&[
            (
                "app/Duck.toml",
                &format!("{MODULE}[dependencies]\nutil = {{ path = \"../util\" }}\n"),
            ),
            ("app/main.duck", app),
            ("util/Duck.toml", library),
            ("util/lib.duck", util),
        ]);
        let mut editor = Editor::start(&dir, json!({}));
        let (main, lib) = (dir.0.join("app/main.duck"), dir.0.join("util/lib.duck"));
        let referred = |file: &Path, line: u32, character: u32| {
            json!({
                "textDocument": { "uri": uri(file) },
                "position": { "line": line, "character": character },
                "context": { "includeDeclaration": true },
            })
        };
        let at = |file: &Path, line: u32, start: u32| {
            json!({
                "uri": uri(file),
                "range": {
                    "start": { "line": line, "character": start },
                    "end": { "line": line, "character": start + 3 },
                },
            })
        };
        // The library is a package of its own, which knows nothing of what
        // uses it.
        editor.open(&lib, util);
        assert_eq!(
            editor.request(References::METHOD, referred(&lib, 0, 7)),
            json!([at(&lib, 0, 7), at(&lib, 3, 4)])
        );
        // Until a package that does is open too.
        editor.open(&main, app);
        let all = json!([at(&lib, 0, 7), at(&lib, 3, 4), at(&main, 2, 9)]);
        assert_eq!(
            editor.request(References::METHOD, referred(&lib, 3, 4)),
            all
        );
        assert_eq!(
            editor.request(References::METHOD, referred(&main, 2, 9)),
            json!([at(&main, 2, 9), at(&lib, 0, 7), at(&lib, 3, 4)])
        );
        editor.stop();
    }

    #[test]
    fn a_name_is_renamed_in_every_file_that_writes_it() {
        let dir = TempDir::new("server-rename");
        let geo = "pub fn len(x: f32) -> f32:\n    return x\n";
        let saved = "use geo\nuse geo.len as length\npub fn main():\n    geo.len(length(1.0))\n";
        dir.write(&[
            ("Duck.toml", MODULE),
            ("main.duck", saved),
            ("geo.duck", geo),
        ]);
        let (main, geo) = (dir.0.join("main.duck"), dir.0.join("geo.duck"));
        let renames = json!({ "workspaceEdit": { "resourceOperations": ["rename"] } });
        let mut editor = Editor::start(&dir, json!({ "workspace": renames }));
        assert_eq!(
            editor.capabilities["renameProvider"],
            json!({ "prepareProvider": true })
        );
        editor.open(&main, saved);
        let at = |line: u32, character: u32| {
            json!({
                "textDocument": { "uri": uri(&main) },
                "position": { "line": line, "character": character },
            })
        };
        let range = |line: u32, start: u32, end: u32| {
            json!({
                "start": { "line": line, "character": start },
                "end": { "line": line, "character": end },
            })
        };
        let rename = |line: u32, character: u32, name: &str| {
            let mut params = at(line, character);
            params["newName"] = json!(name);
            params
        };
        let edit = |line: u32, start: u32, end: u32, name: &str| json!({ "range": range(line, start, end), "newText": name });

        // The name is all of the one the place is in.
        assert_eq!(
            editor.request(PrepareRenameRequest::METHOD, at(3, 10)),
            range(3, 8, 11)
        );
        let renamed = editor.request(Rename::METHOD, rename(3, 10, "size"));
        assert_eq!(
            renamed["changes"][uri(&geo)],
            json!([edit(0, 7, 10, "size")])
        );
        // What a `use` names otherwise is left as it is.
        assert_eq!(
            renamed["changes"][uri(&main)],
            json!([edit(1, 8, 11, "size"), edit(3, 8, 11, "size")])
        );
        let renamed = editor.request(Rename::METHOD, rename(3, 12, "long"));
        assert_eq!(
            renamed["changes"],
            json!({ uri(&main): [edit(1, 15, 21, "long"), edit(3, 12, 18, "long")] })
        );
        // A literal has no name, and nothing is named what something
        // else is where it is.
        assert_eq!(
            editor.request(Rename::METHOD, rename(3, 20, "one")),
            Value::Null
        );
        assert_eq!(
            editor.failure(Rename::METHOD, rename(3, 12, "main")),
            "cannot rename `length` to `main`: something is named `main` where it is"
        );
        let renamed = editor.request(Rename::METHOD, rename(3, 10, "main"));
        assert_eq!(
            renamed["changes"][uri(&geo)],
            json!([edit(0, 7, 10, "main")])
        );

        // A module is named as its file is, which is renamed with it by
        // an editor that says it renames files.
        assert_eq!(
            editor.request(PrepareRenameRequest::METHOD, at(3, 5)),
            range(3, 4, 7)
        );
        let renamed = editor.request(Rename::METHOD, rename(3, 5, "shapes"));
        let shapes = dir.0.join("shapes.duck");
        assert_eq!(
            renamed["documentChanges"],
            json!([
                {
                    "textDocument": { "uri": uri(&main), "version": null },
                    "edits": [
                        edit(0, 4, 7, "shapes"),
                        edit(1, 4, 7, "shapes"),
                        edit(3, 4, 7, "shapes"),
                    ],
                },
                { "kind": "rename", "oldUri": uri(&geo), "newUri": uri(&shapes) },
            ])
        );
        assert_eq!(
            editor.failure(Rename::METHOD, rename(3, 5, "main")),
            "cannot rename `geo` to `main`: something is named `main` where it is"
        );
        dir.write(&[("taken.duck", "")]);
        assert_eq!(
            editor.failure(Rename::METHOD, rename(3, 5, "taken")),
            "cannot rename `geo` to `taken`: a module is named `taken` there"
        );
        assert_eq!(
            editor.failure(Rename::METHOD, rename(3, 10, "not a name")),
            "`not a name` is not a name"
        );
        assert_eq!(
            editor.failure(Rename::METHOD, rename(3, 10, "while")),
            "`while` is not a name"
        );
        // Not every use of a name is known in a file that doesn't parse.
        editor.change(&main, 2, &format!("{saved}    geo.len(\n"));
        let error = "4:11 unclosed '('";
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", Some(2), &[error])
        );
        let why = editor.failure(Rename::METHOD, rename(3, 10, "size"));
        assert!(why.starts_with("cannot rename in a package"), "{why}");
        let why = editor.failure(PrepareRenameRequest::METHOD, at(3, 10));
        assert!(why.starts_with("cannot rename in a package"), "{why}");
        editor.change(&main, 3, saved);
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", Some(3), &[])
        );
        assert_eq!(
            editor.request(PrepareRenameRequest::METHOD, at(3, 10)),
            range(3, 8, 11)
        );
        editor.stop();
    }

    const KIT: &str = "# A point in the plane.\n#   Flat.\npub struct Point:\n    pub x: f32\n    pub y: f32 = 0.0\npub enum(u8) Color:\n    red\n    green\npub fn len(p: Point, scale: f32 = 1.0) -> f32:\n    return p.x * scale\n";

    const PICK: &str = "use kit\npub fn pick(c: kit.Color, wide: i64) -> i32:\n    let p = kit.Point(x: 1.0)\n    let far = kit.len(p, 2.0)\n    match c:\n        .red:\n            return 1\n    let n: i32 = wide\n    return n\n";

    /// An editor with a package open whose module, [`PICK`], uses [`KIT`]
    /// and has two errors and something unused, which it has been told of.
    fn picking(name: &str) -> (TempDir, Editor, PathBuf, PathBuf) {
        let dir = TempDir::new(name);
        dir.write(&[
            ("Duck.toml", MODULE),
            ("main.duck", PICK),
            ("kit.duck", KIT),
        ]);
        let (main, kit) = (dir.0.join("main.duck"), dir.0.join("kit.duck"));
        let editor = Editor::start(&dir, json!({}));
        editor.open(&main, PICK);
        let problems = [
            "4:10 `match` has no arm for `.green`; give it one, or an `else`",
            "7:17 expected `i32`, found `i64`",
            "3:8 warning: `far` is never used",
        ];
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", None, &problems)
        );
        (dir, editor, main, kit)
    }

    #[test]
    fn a_package_is_told_of_as_it_was_last_checked() {
        let (_dir, mut editor, main, kit) = picking("server-told");
        let capabilities = editor.capabilities.clone();
        for provider in [
            "typeDefinitionProvider",
            "documentHighlightProvider",
            "documentSymbolProvider",
            "workspaceSymbolProvider",
            "inlayHintProvider",
            "codeActionProvider",
        ] {
            assert_eq!(capabilities[provider], true, "{provider}");
        }
        let document = json!({ "uri": uri(&main) });
        let at = |line: u32, character: u32| {
            json!({
                "textDocument": document,
                "position": { "line": line, "character": character },
            })
        };
        let range = |line: u32, start: u32, end: u32| {
            json!({
                "start": { "line": line, "character": start },
                "end": { "line": line, "character": end },
            })
        };
        let lines = |start: u32, end: u32| {
            json!({
                "start": { "line": start, "character": 0 },
                "end": { "line": end, "character": 0 },
            })
        };

        // What is said of a declaration is told with it, line by line.
        let hover = editor.request(HoverRequest::METHOD, at(2, 16));
        let point = "```duck\nstruct Point:\n\tpub x: f32\n\tpub y: f32 = 0.0\n```";
        assert_eq!(
            hover["contents"]["value"],
            format!("{point}\n\n---\n\nA point in the plane.  \n\u{a0}\u{a0}Flat.")
        );

        let located = |line: u32, start: u32, end: u32| json!({ "uri": uri(&kit), "range": range(line, start, end) });
        assert_eq!(
            editor.request(GotoTypeDefinition::METHOD, at(3, 22)),
            located(2, 11, 16)
        );
        assert_eq!(
            editor.request(GotoTypeDefinition::METHOD, at(1, 27)),
            Value::Null
        );
        assert_eq!(
            editor.request(DocumentHighlightRequest::METHOD, at(2, 8)),
            json!([{ "range": range(2, 8, 9) }, { "range": range(3, 22, 23) }])
        );

        // What a file declares, and what every file does by name.
        let symbols = editor.request(
            DocumentSymbolRequest::METHOD,
            json!({ "textDocument": document }),
        );
        assert_eq!(symbols.as_array().unwrap().len(), 1);
        assert_eq!(symbols[0]["name"], "pick");
        assert_eq!(symbols[0]["kind"], 12);
        assert_eq!(symbols[0]["selectionRange"], range(1, 7, 11));
        assert_eq!(
            symbols[0]["range"]["end"],
            json!({ "line": 8, "character": 12 })
        );
        let named = |query: &str, editor: &mut Editor| -> Vec<String> {
            let symbols = editor.request(WorkspaceSymbolRequest::METHOD, json!({ "query": query }));
            let symbols = symbols.as_array().unwrap().iter();
            let show = |symbol: &Value| match symbol["containerName"].as_str() {
                Some(container) => format!("{container}.{}", symbol["name"].as_str().unwrap()),
                None => symbol["name"].as_str().unwrap().to_string(),
            };
            symbols.map(show).collect()
        };
        assert_eq!(
            named("", &mut editor),
            [
                "Point",
                "Point.x",
                "Point.y",
                "Color",
                "Color.red",
                "Color.green",
                "len",
                "pick"
            ]
        );
        assert_eq!(named("PI", &mut editor), ["Point", "pick"]);
        assert_eq!(named("rn", &mut editor), ["Color.green"]);

        // What isn't written, shown where it would be.
        let hints = editor.request(
            InlayHintRequest::METHOD,
            json!({ "textDocument": document, "range": lines(0, 9) }),
        );
        let shown = |hint: &Value| {
            let position = &hint["position"];
            format!(
                "{}:{} {} {}",
                position["line"], position["character"], hint["label"], hint["kind"]
            )
        };
        let hints: Vec<_> = hints.as_array().unwrap().iter().map(shown).collect();
        assert_eq!(
            hints,
            [
                "2:9 \": Point\" 1",
                "3:11 \": f32\" 1",
                "3:25 \"scale: \" 2"
            ]
        );

        // What an error says is missing, written for it.
        let mends = |start: u32, end: u32, editor: &mut Editor| {
            let params = json!({
                "textDocument": document,
                "range": lines(start, end),
                "context": { "diagnostics": [] },
            });
            editor.request(CodeActionRequest::METHOD, params)
        };
        let arm = mends(4, 5, &mut editor);
        assert_eq!(arm.as_array().unwrap().len(), 1);
        assert_eq!(arm[0]["title"], "Add an arm for `.green`");
        assert_eq!(arm[0]["kind"], "quickfix");
        let edit = json!({
            "range": range(6, 20, 20),
            "newText": "\n        .green:\n            pass",
        });
        assert_eq!(arm[0]["edit"]["changes"][uri(&main)], json!([edit]));
        let cast = mends(7, 8, &mut editor);
        assert_eq!(cast[0]["title"], "Cast to `i32` with `as`");
        let edit = json!({ "range": range(7, 21, 21), "newText": " as i32" });
        assert_eq!(cast[0]["edit"]["changes"][uri(&main)], json!([edit]));
        assert_eq!(mends(2, 3, &mut editor), json!([]));
        editor.stop();
    }

    #[test]
    fn what_is_being_written_is_suggested_by_what_is_expected_of_it() {
        let (dir, mut editor, main, _kit) = picking("server-suggested");
        dir.write(&[("deep/nest.duck", "")]);
        let labels = |completions: &Value| -> Vec<String> {
            let completions = completions.as_array().unwrap().iter();
            completions
                .map(|c| c["label"].as_str().unwrap().to_string())
                .collect()
        };
        // Types a line in place of the last of `pick`, and asks what can
        // be written at the end of it.
        let mut version = 1;
        let mut typed = |line: &str, method: &str, editor: &mut Editor| {
            version += 1;
            let text = PICK.replace("    return n\n", &format!("{line}\n    return n\n"));
            editor.change(&main, version, &text);
            let Message::Notification(_) = editor.receive() else {
                panic!("not the diagnostics of the change")
            };
            let at = project::position(&text, text.find(line).unwrap() + line.len());
            let params = json!({ "textDocument": { "uri": uri(&main) }, "position": at });
            editor.request(method, params)
        };

        // The variants or members of the type expected of a `.name`.
        let expected = typed("    let m: kit.Color = .", Completion::METHOD, &mut editor);
        assert_eq!(labels(&expected), ["red", "green"]);
        let expected = typed("    if c == .gr", Completion::METHOD, &mut editor);
        assert_eq!(labels(&expected), ["red", "green"]);
        // The labels an argument may have come before the names in scope,
        // and are written with what follows a label.
        let argument = typed("    kit.len(p, ", Completion::METHOD, &mut editor);
        assert_eq!(labels(&argument)[..3], ["scale:", "n", "far"]);
        assert_eq!(argument[0]["insertText"], "scale: ");
        assert_eq!(argument[0]["detail"], "scale: f32 = 1.0");
        let field = typed("    kit.Point(y: 1.0, ", Completion::METHOD, &mut editor);
        assert_eq!(labels(&field)[..2], ["x:", "n"]);
        // What a `use` would bring is last of them, with the `use`.
        let named = typed("    le", Completion::METHOD, &mut editor);
        let len = named.as_array().unwrap().iter();
        let len: Vec<_> = len.filter(|c| c["label"] == "len").collect();
        assert_eq!(len.len(), 1);
        assert_eq!(len[0]["detail"], "use kit.len");
        let import = json!({
            "range": {
                "start": { "line": 0, "character": 0 },
                "end": { "line": 0, "character": 0 },
            },
            "newText": "use kit.len\n",
        });
        assert_eq!(len[0]["additionalTextEdits"], json!([import]));

        // A call of what `module` has, and of a `.name`.
        let grow = typed(
            "    module.grow(",
            SignatureHelpRequest::METHOD,
            &mut editor,
        );
        assert_eq!(
            grow["signatures"][0]["label"],
            "module.grow(pages: uint) -> int"
        );
        let some = typed(
            "    let o: option(i32) = .some(",
            SignatureHelpRequest::METHOD,
            &mut editor,
        );
        assert_eq!(some["signatures"][0]["label"], "option(i32).some(i32)");

        // The path of a `use`: what is there to use, and what it has.
        let mut used = |line: &str, typed: Option<&str>, editor: &mut Editor| {
            version += 1;
            let text = PICK.replacen("use kit\n", &format!("use kit\n{line}\n"), 1);
            editor.change(&main, version, &text);
            let Message::Notification(_) = editor.receive() else {
                panic!("not the diagnostics of the change")
            };
            let at = json!({ "line": 1, "character": line.len() });
            let context = match typed {
                Some(typed) => json!({ "triggerKind": 2, "triggerCharacter": typed }),
                None => json!({ "triggerKind": 1 }),
            };
            let params = json!({
                "textDocument": { "uri": uri(&main) },
                "position": at,
                "context": context,
            });
            labels(&editor.request(Completion::METHOD, params))
        };
        assert_eq!(used("use ", None, &mut editor), ["deep", "kit", "main"]);
        assert_eq!(used("use deep.", Some("."), &mut editor), ["nest"]);
        let kit = ["Color", "Point", "len"];
        assert_eq!(used("use kit.", Some("."), &mut editor), kit);
        assert_eq!(used("use kit.{Point, ", None, &mut editor), kit);
        // In a group it is asked for by what is typed there, which asks
        // for nothing anywhere else. Each line leaves its bracket open at
        // another place than the last, for the diagnostics to change.
        assert_eq!(used("use deep.{", Some("{"), &mut editor), ["nest"]);
        assert_eq!(used("use kit.{Point, ", Some(" "), &mut editor), kit);
        assert_eq!(used("use deep.{nest,", Some(","), &mut editor), ["nest"]);
        let none: [&str; 0] = [];
        assert_eq!(used("let far = (1, ", Some(" "), &mut editor), none);
        assert_eq!(used("let near = (1,", Some(","), &mut editor), none);
        assert!(!used("let far = (1, ", None, &mut editor).is_empty());
        editor.stop();
    }

    #[test]
    fn the_editor_is_kept_up_with() {
        let (dir, mut editor, main, _kit) = picking("server-kept-up");
        // A change to part of a file is made to that part.
        let whole = |start: (u32, u32), end: (u32, u32), text: &str| {
            json!({
                "range": {
                    "start": { "line": start.0, "character": start.1 },
                    "end": { "line": end.0, "character": end.1 },
                },
                "text": text,
            })
        };
        let changes = json!([
            whole((7, 17), (7, 21), "2"),
            whole((6, 20), (6, 20), "\n        .green:\n            return 2"),
        ]);
        let document = json!({ "uri": uri(&main), "version": 2 });
        editor.notify(
            DidChangeTextDocument::METHOD,
            json!({ "textDocument": document, "contentChanges": changes }),
        );
        let unused = "3:8 warning: `far` is never used";
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", Some(2), &[unused])
        );
        let hover = editor.request(
            HoverRequest::METHOD,
            json!({
                "textDocument": { "uri": uri(&main) },
                "position": { "line": 9, "character": 8 },
            }),
        );
        assert_eq!(hover["contents"]["value"], "```duck\nlet n: i32\n```");

        // A directory that the editor opens is checked, until it closes it.
        dir.write(&[
            ("other/Duck.toml", "[library]\nentry = \"lib.duck\"\n"),
            ("other/lib.duck", "pub let a: Nope = 1\n"),
        ]);
        let folder = json!({ "uri": uri(&dir.0.join("other")), "name": "other" });
        let event = |added: Value, removed: Value| json!({ "event": { "added": added, "removed": removed } });
        editor.notify(
            DidChangeWorkspaceFolders::METHOD,
            event(json!([folder]), json!([])),
        );
        assert_eq!(
            editor.diagnostics(&dir),
            published("other/lib.duck", None, &["0:11 unknown type `Nope`"])
        );
        editor.notify(
            DidChangeWorkspaceFolders::METHOD,
            event(json!([]), json!([folder])),
        );
        assert_eq!(
            editor.diagnostics(&dir),
            published("other/lib.duck", None, &[])
        );
        editor.stop();
    }

    #[test]
    fn a_request_the_editor_no_longer_waits_for_is_not_answered() {
        let cancel = |id: i32| {
            let params = json!({ "id": id });
            Message::Notification(Notification::new(Cancel::METHOD.to_string(), params))
        };
        let other = Message::Notification(Notification::new("other".to_string(), json!({})));
        let mut waiting: VecDeque<Message> = [other, cancel(7), cancel(9)].into();
        assert!(!cancelled(&mut waiting, &RequestId::from(8)));
        assert!(cancelled(&mut waiting, &RequestId::from(9)));
        // That it was is then forgotten, and the rest is still to answer.
        assert!(!cancelled(&mut waiting, &RequestId::from(9)));
        assert_eq!(waiting.len(), 2);

        // A server that is asked and told at once answers that it was.
        let dir = TempDir::new("server-cancel");
        let mut editor = Editor::start(&dir, json!({}));
        let hover = Request::new(
            RequestId::from(50),
            HoverRequest::METHOD.to_string(),
            json!({}),
        );
        let batch = [Message::Request(hover), cancel(50)];
        // Both wait behind a request that the server is still to read.
        editor.requests += 1;
        let first = RequestId::from(editor.requests);
        let slow = Request::new(
            first.clone(),
            WorkspaceSymbolRequest::METHOD.to_string(),
            json!({ "query": "" }),
        );
        for message in [Message::Request(slow)].into_iter().chain(batch) {
            editor.connection.sender.send(message).unwrap();
        }
        let mut answered = Vec::new();
        while answered.len() < 2 {
            if let Message::Response(response) = editor.receive() {
                answered.push((response.id.clone(), response.response_result.err()));
            }
        }
        assert_eq!(answered[0].0, first);
        assert!(answered[0].1.is_none());
        let (id, error) = &answered[1];
        assert_eq!(*id, RequestId::from(50));
        // Unless it read the request before it was told, which is as well.
        let code = error.as_ref().map(|error| error.code);
        let codes = [
            ErrorCode::RequestCanceled as i32,
            ErrorCode::InvalidParams as i32,
        ];
        assert!(code.is_some_and(|code| codes.contains(&code)), "{error:?}");
        editor.stop();
    }

    #[test]
    fn places_are_answered_of_as_they_are_in_the_editor() {
        let dir = TempDir::new("server-places");
        let geo = "pub struct Point:\n    pub x: f32\n    pub y: f32 = 0.0\npub fn len(p: Point, scale: f32 = 1.0) -> f32:\n    return p.x * scale\npub struct Pixel:\n    use Point\n    pub color: u32\n";
        let saved = "use geo\npub fn main():\n    let p = geo.Point(x: 1.0)\n";
        dir.write(&[
            ("Duck.toml", MODULE),
            ("main.duck", saved),
            ("geo.duck", geo),
        ]);
        let main = dir.0.join("main.duck");
        let mut editor = Editor::start(&dir, json!({}));
        // What is declared and never used is warned of, not an error.
        let unused = "2:8 warning: `p` is never used";
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", None, &[unused])
        );
        let capabilities = editor.capabilities.clone();
        assert_eq!(capabilities["hoverProvider"], true);
        assert_eq!(capabilities["definitionProvider"], true);
        assert_eq!(capabilities["implementationProvider"], true);
        assert_eq!(capabilities["referencesProvider"], true);
        assert_eq!(
            capabilities["completionProvider"]["triggerCharacters"],
            json!([".", "{", ",", " "])
        );
        assert_eq!(
            capabilities["signatureHelpProvider"]["triggerCharacters"],
            json!(["(", ","])
        );
        let at = |line: u32, character: u32| {
            json!({
                "textDocument": { "uri": uri(&main) },
                "position": { "line": line, "character": character },
            })
        };

        // A file is answered of once it is open.
        assert_eq!(editor.request(Completion::METHOD, at(2, 4)), json!([]));
        editor.open(&main, saved);
        let hover = editor.request(HoverRequest::METHOD, at(2, 8));
        assert_eq!(
            hover,
            json!({
                "contents": { "kind": "markdown", "value": "```duck\nlet p: Point\n```" },
                "range": {
                    "start": { "line": 2, "character": 8 },
                    "end": { "line": 2, "character": 9 },
                },
            })
        );
        assert_eq!(editor.request(HoverRequest::METHOD, at(1, 0)), Value::Null);

        // A name is declared in whichever file declares it.
        let located = |line: u32, start: u32, end: u32| {
            json!({
                "uri": uri(&dir.0.join("geo.duck")),
                "range": {
                    "start": { "line": line, "character": start },
                    "end": { "line": line, "character": end },
                },
            })
        };
        let point = editor.request(GotoDefinition::METHOD, at(2, 16));
        assert_eq!(point, located(0, 11, 16));
        let field = editor.request(GotoDefinition::METHOD, at(2, 22));
        assert_eq!(field, located(1, 8, 9));
        let module = editor.request(GotoDefinition::METHOD, at(2, 12));
        assert_eq!(module, located(0, 0, 0));
        assert_eq!(
            editor.request(GotoDefinition::METHOD, at(2, 25)),
            Value::Null
        );
        // It is referred to wherever it is named, and where it is declared
        // if that is asked for.
        let referred = |declared: bool| {
            let mut params = at(2, 16);
            params["context"] = json!({ "includeDeclaration": declared });
            params
        };
        let used = json!({
            "uri": uri(&main),
            "range": {
                "start": { "line": 2, "character": 16 },
                "end": { "line": 2, "character": 21 },
            },
        });
        assert_eq!(
            editor.request(References::METHOD, referred(true)),
            json!([
                used,
                located(0, 11, 16),
                located(3, 14, 19),
                located(6, 8, 13)
            ])
        );
        assert_eq!(
            editor.request(References::METHOD, referred(false)),
            json!([used, located(3, 14, 19), located(6, 8, 13)])
        );
        // A struct is implemented by those that start as it does.
        let pixel = editor.request(GotoImplementation::METHOD, at(2, 16));
        assert_eq!(pixel, json!([located(5, 11, 16)]));
        assert_eq!(
            editor.request(GotoImplementation::METHOD, at(2, 8)),
            json!([])
        );

        // What is being written doesn't parse, and is answered of as it
        // will be.
        let edited = format!("{saved}    let d = geo.len(p, \n    p.\n    le\n");
        editor.change(&main, 2, &edited);
        assert_eq!(
            editor.diagnostics(&dir),
            published("main.duck", Some(2), &["3:19 unclosed '('"])
        );
        let labels = |completions: &Value| -> Vec<String> {
            let completions = completions.as_array().unwrap().iter();
            completions
                .map(|c| c["label"].as_str().unwrap().to_string())
                .collect()
        };
        let fields = editor.request(Completion::METHOD, at(4, 6));
        assert_eq!(labels(&fields), ["*", "x", "y"][1..]);
        assert_eq!(fields[0]["detail"], "f32");
        assert_eq!(fields[0]["kind"], 5);
        let names = editor.request(Completion::METHOD, at(5, 6));
        let names = labels(&names);
        assert_eq!(names[..3], ["p", "geo", "main"]);
        assert!(names.contains(&"let".to_string()), "{names:?}");
        assert!(names.contains(&"uint".to_string()), "{names:?}");

        let help = editor.request(SignatureHelpRequest::METHOD, at(3, 23));
        let signature = &help["signatures"][0];
        assert_eq!(
            signature["label"],
            "fn len(p: Point, scale: f32 = 1.0) -> f32"
        );
        assert_eq!(signature["parameters"][1]["label"], json!([17, 33]));
        assert_eq!(help["activeParameter"], 1);
        // The call goes on to the lines below, as its bracket is open.
        let below = editor.request(SignatureHelpRequest::METHOD, at(4, 6));
        assert_eq!(below, help);
        assert_eq!(
            editor.request(SignatureHelpRequest::METHOD, at(2, 8)),
            Value::Null
        );
        // The lines that parse are described still.
        let hover = editor.request(HoverRequest::METHOD, at(2, 16));
        let point = "```duck\nstruct Point:\n\tpub x: f32\n\tpub y: f32 = 0.0\n```";
        assert_eq!(hover["contents"]["value"], point);
        editor.stop();
    }
}

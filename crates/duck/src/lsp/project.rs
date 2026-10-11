//! Checks a package as `duck build` does, giving each error as a place in a
//! file rather than printing it, and answers what an editor asks of the
//! package as checked.

use std::fs;
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};

use duck::files::{self, Files};
use duck::git::Cache;
use duck::manifest::{MANIFEST, ManifestError};
use duck::package::{self, Packages, ResolveError};
use duck_compiler::file::{FileId, FileManager, Settings};
use duck_compiler::lex::Span;
use duck_compiler::ty::{
    self, Analysis, Completion, CompletionKind, HintKind, Signature, Symbol, SymbolKind,
};
use duck_compiler::{Error, load};
use lsp_types::{Position, Range};

use super::cursor::{self, Completing, Cursor};

/// The text of the file at a canonical path, if the editor has it open.
pub type Buffers<'a> = &'a dyn Fn(&Path) -> Option<&'a str>;

/// A package and every package it depends on, as their manifests were when
/// it was resolved.
pub struct Project {
    /// The directory holding the package's manifest.
    root: PathBuf,
    packages: Result<Packages, ResolveError>,
    /// The package's module and its library, as each was last checked.
    checked: Vec<Checked>,
    /// What was then found to be declared in the package and never used.
    warnings: Vec<Problem>,
}

/// The files of a build, and what checking them found. Of a build with
/// errors that is what loaded of it, which may be none of a file.
struct Checked {
    files: Files,
    analysis: Analysis,
    /// Whether every file loaded whole, so that every name is known.
    whole: bool,
}

/// What writing another name for one changes.
#[derive(Debug, Clone, PartialEq)]
pub struct Renaming {
    /// Where the name is, in its file.
    pub at: Range,
    /// The name as it is written there.
    pub name: String,
    /// Every place that is written so and stands for the same.
    pub places: Vec<Place>,
    /// The file of the module that the name is, if it is one's: writing
    /// another name for a module names its file otherwise.
    pub module: Option<PathBuf>,
}

/// What can be written at a place, and whether it is the names in scope.
#[derive(Debug, Clone, PartialEq)]
pub struct Suggested {
    pub suggestions: Vec<Suggestion>,
    pub names: bool,
}

/// Something that can be written at a place.
#[derive(Debug, Clone, PartialEq)]
pub struct Suggestion {
    pub completion: Completion,
    /// What is written for it, where that is more than its name.
    pub insert: Option<String>,
    /// The line that is written with it to bring it into scope, and where.
    pub import: Option<(Position, String)>,
}

/// Something a file declares, and where.
#[derive(Debug, Clone, PartialEq)]
pub struct Outline {
    pub name: String,
    pub kind: SymbolKind,
    /// The whole of its declaration.
    pub range: Range,
    /// Where it is named in it.
    pub named: Range,
    pub children: Vec<Outline>,
}

/// A change that mends an error: what it is offered as, and what it writes
/// in place of what.
#[derive(Debug, Clone, PartialEq)]
pub struct Mend {
    pub title: String,
    pub edits: Vec<(Place, String)>,
}

/// An error, and where it is.
#[derive(Debug, Clone, PartialEq)]
pub struct Problem {
    pub place: Place,
    pub message: String,
    /// What led to the error, nearest first.
    pub notes: Vec<Note>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Note {
    pub place: Place,
    pub message: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Place {
    /// The canonical path of the file.
    pub path: PathBuf,
    pub range: Range,
}

/// The files of a build, those open in the editor read as they are there
/// rather than as they were saved.
struct Overlay<'f, 'b> {
    files: &'f mut Files,
    buffers: Buffers<'b>,
}

/// Why nothing is renamed in a package that doesn't load.
const UNLOADED: &str =
    "cannot rename in a package that doesn't parse: not every use of a name in it is known";

/// The fuel the constants of one item run on where their errors aren't
/// reported: about a thousandth of a second's worth.
const ASKING_FUEL: u64 = 10_000_000;

impl Project {
    /// Reads the manifest of the package in `root`, then those of its
    /// dependencies, fetching git dependencies into `cache`.
    pub fn resolve(root: PathBuf, cache: &Cache) -> Self {
        let packages = package::resolve(&root, cache);
        Self {
            root,
            packages,
            checked: Vec::new(),
            warnings: Vec::new(),
        }
    }

    /// Every error in the package's module and in its library. Files they
    /// don't use aren't checked. What is asked of the package is then
    /// answered of it as it is now.
    pub fn check(&mut self, buffers: Buffers<'_>) -> Vec<Problem> {
        let (problems, checked) = self.builds(buffers, false);
        self.checked = checked;
        self.warnings = self.unused(buffers);
        problems
    }

    /// What the package declares and never uses, as it was last checked:
    /// nothing is wrong with it, but something was likely meant to use it.
    pub fn warnings(&self) -> &[Problem] {
        &self.warnings
    }

    /// What every build of the package that uses a file agrees is declared
    /// in it and never used, of the files of the package itself. A build
    /// that didn't load whole doesn't know what it uses.
    fn unused(&mut self, buffers: Buffers<'_>) -> Vec<Problem> {
        let root = self.root.clone();
        let mut found: Vec<Vec<Problem>> = Vec::new();
        for checked in &mut self.checked {
            let mut files = Overlay {
                files: &mut checked.files,
                buffers,
            };
            let unused = match checked.whole {
                true => checked.analysis.unused(&mut files),
                false => Vec::new(),
            };
            let problem = |unused: ty::Unused| Problem {
                place: files.place(unused.span),
                message: format!("`{}` is never used", unused.name),
                notes: Vec::new(),
            };
            found.push(unused.into_iter().map(problem).collect());
        }
        let mut warnings: Vec<Problem> = Vec::new();
        for (build, unused) in found.iter().enumerate() {
            for problem in unused {
                let path = &problem.place.path;
                let builds = self.checked.iter().zip(&found).enumerate();
                let mut others = builds.filter(|(other, (checked, _))| {
                    *other != build && checked.files.find(path).is_some()
                });
                let agreed = others.all(|(_, (_, unused))| unused.contains(problem));
                let own = root_of(path).is_some_and(|of| canonical(&of) == canonical(&root));
                if agreed && own && !warnings.contains(problem) {
                    warnings.push(problem.clone());
                }
            }
        }
        warnings
    }

    /// Asks `ask` of the first build that uses the file at the canonical
    /// path `path`, as it was last checked, and that has an answer: of its
    /// analysis, its files, which of them the file is, and its source.
    fn first<T>(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        ask: impl Fn(&Analysis, &mut Overlay, FileId, &str) -> Option<T>,
    ) -> Option<T> {
        self.checked.iter_mut().find_map(|checked| {
            let file = checked.files.find(path)?;
            let mut files = Overlay {
                files: &mut checked.files,
                buffers,
            };
            let src = files.contents(file);
            ask(&checked.analysis, &mut files, file, &src)
        })
    }

    /// Where the type of what is at `position` of the file at the
    /// canonical path `path` is declared, as the package was last checked.
    pub fn type_definition(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        position: Position,
    ) -> Option<Place> {
        self.first(buffers, path, |analysis, files, file, src| {
            let span = analysis.type_definition(file, offset(src, position))?;
            Some(files.place(span))
        })
    }

    /// Where the name at `position` of the file at the canonical path
    /// `path` is written in that file for what it stands for there, as the
    /// package was last checked.
    pub fn highlights(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        position: Position,
    ) -> Vec<Range> {
        let highlights = self.first(buffers, path, |analysis, files, file, src| {
            let spans = analysis.references(files, file, offset(src, position), true);
            let here = spans.into_iter().filter(|span| span.file == file);
            let ranges: Vec<_> = here.map(|span| range(src, span.start, span.end)).collect();
            (!ranges.is_empty()).then_some(ranges)
        });
        highlights.unwrap_or_default()
    }

    /// What the file at the canonical path `path` declares, as the package
    /// was last checked.
    pub fn symbols(&mut self, buffers: Buffers<'_>, path: &Path) -> Vec<Outline> {
        fn outline(src: &str, symbol: Symbol) -> Outline {
            Outline {
                name: symbol.name,
                kind: symbol.kind,
                range: range(src, symbol.span.start, symbol.span.end),
                named: range(src, symbol.name_span.start, symbol.name_span.end),
                children: (symbol.children.into_iter())
                    .map(|child| outline(src, child))
                    .collect(),
            }
        }
        let symbols = self.first(buffers, path, |analysis, _, file, src| {
            let symbols = analysis.symbols(file).into_iter();
            Some(symbols.map(|symbol| outline(src, symbol)).collect())
        });
        symbols.unwrap_or_default()
    }

    /// What each file of the package declares, as it was last checked, with
    /// the canonical path of the file. A dependency's files are its own
    /// package's to tell of.
    pub fn all_symbols(&mut self, buffers: Buffers<'_>) -> Vec<(PathBuf, Vec<Outline>)> {
        let mut paths: Vec<PathBuf> = Vec::new();
        for checked in &self.checked {
            for file in checked.analysis.files() {
                let path = checked.files.path(file);
                let own = root_of(path).is_some_and(|of| canonical(&of) == canonical(&self.root));
                if own && !paths.iter().any(|known| known == path) {
                    paths.push(path.to_path_buf());
                }
            }
        }
        let symbols = paths.into_iter().map(|path| {
            let symbols = self.symbols(buffers, &path);
            (path, symbols)
        });
        symbols.collect()
    }

    /// What to show in `shown` of the file at the canonical path `path` as
    /// if it were written there, as the package was last checked: the types
    /// of the names bound without one, and the parameters that arguments
    /// are given to. Each with where, and whether it is a type.
    pub fn hints(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        shown: Range,
    ) -> Vec<(Position, String, HintKind)> {
        let hints = self.first(buffers, path, |analysis, _, file, src| {
            let within = offset(src, shown.start)..offset(src, shown.end);
            let hints = analysis.hints(file, within).into_iter();
            let placed = hints.map(|hint| (position(src, hint.offset), hint.label, hint.kind));
            Some(placed.collect())
        });
        hints.unwrap_or_default()
    }

    /// What mends the errors in `within` of the file at the canonical path
    /// `path`, as the package was last checked. Nothing does, of a package
    /// that doesn't load: its errors are not those of what it means.
    pub fn mends(&mut self, buffers: Buffers<'_>, path: &Path, within: Range) -> Vec<Mend> {
        let whole = self.checked.iter().all(|checked| checked.whole);
        let mends = self.first(buffers, path, |analysis, files, file, src| {
            let within = offset(src, within.start)..offset(src, within.end);
            let actions = analysis.actions(files, file, within);
            let mend = |action: ty::Action| Mend {
                title: action.title,
                edits: (action.edits.into_iter())
                    .map(|(span, text)| (files.place(span), text))
                    .collect(),
            };
            let mends: Vec<_> = actions.into_iter().map(mend).collect();
            (!mends.is_empty()).then_some(mends)
        });
        mends.filter(|_| whole).unwrap_or_default()
    }

    /// Whether writing `name` for the name at `position` of the file at
    /// the canonical path `path` would give it the name of something else
    /// that is named where it is.
    pub fn collides(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        position: Position,
        name: &str,
    ) -> bool {
        let collides = self.first(buffers, path, |analysis, files, file, src| {
            let collides = analysis.collides(files, file, offset(src, position), name);
            collides.then_some(())
        });
        collides.is_some()
    }

    /// What is written at `position` of the file at the canonical path
    /// `path`, as it was last checked: all of what is described, its
    /// declaration or its type, and the comment on its declaration.
    pub fn hover(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        position: Position,
    ) -> Option<(Range, String, String)> {
        self.first(buffers, path, |analysis, files, file, src| {
            let hover = analysis.hover(files, file, offset(src, position))?;
            let range = range(src, hover.span.start, hover.span.end);
            Some((range, hover.text, hover.docs))
        })
    }

    /// Where what the name at `position` of the file at the canonical path
    /// `path` stands for is declared, as the package was last checked.
    pub fn definition(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        position: Position,
    ) -> Option<Place> {
        self.checked.iter_mut().find_map(|checked| {
            let file = checked.files.find(path)?;
            let mut files = Overlay {
                files: &mut checked.files,
                buffers,
            };
            let offset = offset(&files.contents(file), position);
            let span = checked.analysis.definition(file, offset)?;
            Some(files.place(span))
        })
    }

    /// Where each name is written that stands for what the name at
    /// `position` of the file at the canonical path `path` does, as the
    /// package was last checked: where it is `declared` too, if that is
    /// wanted.
    pub fn references(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        position: Position,
        declared: bool,
    ) -> Vec<Place> {
        let mut places = Vec::new();
        // The module and the library may each use files the other doesn't.
        for checked in &mut self.checked {
            let Some(file) = checked.files.find(path) else {
                continue;
            };
            let mut files = Overlay {
                files: &mut checked.files,
                buffers,
            };
            let offset = offset(&files.contents(file), position);
            let analysis = &checked.analysis;
            for span in analysis.references(&mut files, file, offset, declared) {
                let place = files.place(span);
                if !places.contains(&place) {
                    places.push(place);
                }
            }
        }
        places
    }

    /// What writing another name for the one at `position` of the file at
    /// the canonical path `path` changes, as the package was last checked.
    /// `None` for what has no name to change, and an error for a package
    /// that doesn't load, as not every name in it is known, and for a
    /// module that its package is entered by, as its manifest names it.
    pub fn rename(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        position: Position,
    ) -> Result<Option<Renaming>, String> {
        let mut renaming: Option<Renaming> = None;
        for checked in &mut self.checked {
            let Some(file) = checked.files.find(path) else {
                continue;
            };
            let mut files = Overlay {
                files: &mut checked.files,
                buffers,
            };
            let src = files.contents(file);
            let analysis = &checked.analysis;
            let offset = offset(&src, position);
            let Some((at, spans)) = analysis.rename(&mut files, file, offset) else {
                continue;
            };
            if !checked.whole {
                return Err(UNLOADED.to_string());
            }
            // A module is declared by its file, at no place in it, and is
            // named as the file is unless a `use` names it otherwise.
            let name = &src[at.start..at.end];
            let declared = analysis.definition(file, offset);
            let module = declared.filter(|declared| declared.start == declared.end);
            let module = module.map(|declared| files.files.path(declared.file));
            let named = |module: &&Path| module.file_stem().is_some_and(|stem| stem == name);
            let module = module.filter(named).map(Path::to_path_buf);
            let renaming = renaming.get_or_insert_with(|| Renaming {
                at: range(&src, at.start, at.end),
                name: name.to_string(),
                places: Vec::new(),
                module,
            });
            for span in spans {
                let place = files.place(span);
                if !renaming.places.contains(&place) {
                    renaming.places.push(place);
                }
            }
        }
        let module = renaming
            .as_ref()
            .and_then(|renaming| renaming.module.as_ref());
        if let (Some(module), Ok(packages)) = (module, &self.packages) {
            let entered = packages.iter().any(|package| {
                let manifest = &package.manifest;
                let module_entry = manifest
                    .component
                    .as_ref()
                    .map(|component| &component.entry);
                let library_entry = manifest.library.as_ref().map(|library| &library.entry);
                let mut entries = module_entry.into_iter().chain(library_entry);
                entries.any(|entry| canonical(&package.dir.join(entry)) == *module)
            });
            if entered {
                return Err(format!(
                    "cannot rename {}: its package is entered by it, as its {MANIFEST} says",
                    module.display()
                ));
            }
        }
        Ok(renaming)
    }

    /// Where each type is declared that is given for one bounded by the
    /// type named at `position` of the file at the canonical path `path`,
    /// as the package was last checked.
    pub fn implementations(
        &mut self,
        buffers: Buffers<'_>,
        path: &Path,
        position: Position,
    ) -> Vec<Place> {
        let places = self.checked.iter_mut().find_map(|checked| {
            let file = checked.files.find(path)?;
            let mut files = Overlay {
                files: &mut checked.files,
                buffers,
            };
            let offset = offset(&files.contents(file), position);
            let spans = checked.analysis.implementations(file, offset);
            let places: Vec<_> = spans.into_iter().map(|span| files.place(span)).collect();
            (!places.is_empty()).then_some(places)
        });
        places.unwrap_or_default()
    }

    /// What can be written at `position` of the file at the canonical path
    /// `path`, which holds `text`: the names in scope, with the labels that
    /// an argument there may have and what a `use` would bring; after a
    /// `.`, what the value, type or module before it has, or the type
    /// expected there; and in a `use`, what its path may go on with. Only
    /// that last, if nothing but what is `used` is asked for.
    pub fn complete(
        &self,
        buffers: Buffers<'_>,
        path: &Path,
        text: &str,
        position: Position,
        used: bool,
    ) -> Suggested {
        let at = offset(text, position);
        let plain = |completion| Suggestion {
            completion,
            insert: None,
            import: None,
        };
        let completing = cursor::completing(text, at)
            .filter(|completing| !used || matches!(completing, Completing::Used(..)));
        let completions = match completing {
            None => Vec::new(),
            Some(Completing::Module) => ty::module_members(),
            Some(Completing::Members(cursor)) => {
                let members = self.ask(buffers, path, &cursor, |analysis, files, file| {
                    Some(analysis.members(files, file, cursor.probe))
                });
                members.unwrap_or_default()
            }
            Some(Completing::Expected(cursor)) => {
                let expected = self.ask(buffers, path, &cursor, |analysis, _, file| {
                    Some(analysis.expected(file, cursor.probe))
                });
                expected.unwrap_or_default()
            }
            Some(Completing::Used(names, cursor)) => {
                // The modules that are there to use, and then what the
                // module that the path names so far makes `pub`.
                let mut builds = self.checked.iter();
                let modules = builds.find_map(|checked| {
                    let file = checked.files.find(path)?;
                    Some(checked.files.children(file, &names))
                });
                let module = |name| Completion {
                    name,
                    kind: CompletionKind::Module,
                    detail: String::new(),
                    import: None,
                };
                let modules = modules.unwrap_or_default().into_iter().map(module);
                let mut completions: Vec<_> = modules.collect();
                let items = cursor.and_then(|cursor| {
                    self.ask(buffers, path, &cursor, |analysis, files, file| {
                        Some(analysis.module_items(files, file, cursor.probe))
                    })
                });
                for item in items.unwrap_or_default() {
                    if !completions.iter().any(|known| known.name == item.name) {
                        completions.push(item);
                    }
                }
                completions
            }
            Some(Completing::Names(cursor)) => {
                let names = self.ask(buffers, path, &cursor, |analysis, files, file| {
                    Some(analysis.names(files, file, cursor.probe))
                });
                let mut suggestions = self.labels(buffers, path, text, at);
                for mut completion in names.unwrap_or_default() {
                    // A `use` goes above the line being written, which is
                    // as it was there.
                    let import = match completion.import.take() {
                        Some((at, _)) if at > cursor.probe => continue,
                        Some((at, line)) => Some((self::position(&cursor.source, at), line)),
                        None => None,
                    };
                    suggestions.push(Suggestion {
                        completion,
                        insert: None,
                        import,
                    });
                }
                return Suggested {
                    suggestions,
                    names: true,
                };
            }
        };
        Suggested {
            suggestions: completions.into_iter().map(plain).collect(),
            names: false,
        }
    }

    /// The labels that the argument being written at byte `at` of the file
    /// at `path`, which holds `text`, may be given: those of the parameters
    /// or fields that the call it is in has given no argument yet.
    fn labels(&self, buffers: Buffers<'_>, path: &Path, text: &str, at: usize) -> Vec<Suggestion> {
        let calling = cursor::calling(text, at).filter(|call| call.starts && !call.expected);
        let Some(calling) = calling else {
            return Vec::new();
        };
        let cursor = &calling.cursor;
        let signature = self.ask(buffers, path, cursor, |analysis, files, file| {
            analysis.signature(files, file, cursor.probe)
        });
        let Some(signature) = signature else {
            return Vec::new();
        };
        // Those given by their place come first.
        let placed = calling.index.saturating_sub(calling.labels.len());
        let params = signature.params.iter().enumerate();
        let label = |(i, param): (usize, &ty::Parameter)| {
            let name = param.name.as_ref()?;
            let given = i < placed || calling.labels.contains(name);
            (!given).then(|| Suggestion {
                completion: Completion {
                    name: format!("{name}:"),
                    kind: CompletionKind::Variable,
                    detail: signature.label[param.range.clone()].to_string(),
                    import: None,
                },
                insert: Some(format!("{name}: ")),
                import: None,
            })
        };
        params.filter_map(label).collect()
    }

    /// What the call takes whose arguments `position` is in, of the file at
    /// the canonical path `path`, which holds `text`, and which of its
    /// parameters the argument there is for, if it can be told.
    pub fn signature(
        &self,
        buffers: Buffers<'_>,
        path: &Path,
        text: &str,
        position: Position,
    ) -> Option<(Signature, Option<usize>)> {
        let calling = cursor::calling(text, offset(text, position))?;
        let cursor = &calling.cursor;
        let signature = self.ask(buffers, path, cursor, |analysis, files, file| match calling
            .expected
        {
            true => analysis.expected_signature(file, cursor.probe),
            false => analysis.signature(files, file, cursor.probe),
        })?;
        let active = match &calling.label {
            Some(label) => {
                let mut params = signature.params.iter();
                params.position(|param| param.name.as_ref() == Some(label))
            }
            None => Some(calling.index),
        };
        Some((signature, active))
    }

    /// Checks the package with the file at `path` as `cursor` has it, and
    /// asks what `ask` does of the first build that uses the file.
    fn ask<T>(
        &self,
        buffers: Buffers<'_>,
        path: &Path,
        cursor: &Cursor,
        ask: impl Fn(&Analysis, &mut Overlay, FileId) -> Option<T>,
    ) -> Option<T> {
        let buffers = |other: &Path| match other == path {
            true => Some(cursor.source.as_str()),
            false => buffers(other),
        };
        let (_, checked) = self.builds(&buffers, true);
        checked.into_iter().find_map(|mut checked| {
            let file = checked.files.find(path)?;
            let files = &mut checked.files;
            let buffers = &buffers;
            ask(&checked.analysis, &mut Overlay { files, buffers }, file)
        })
    }

    /// Checks the package's module and its library: every error in them,
    /// and each as checked. If only something is `asked` of them, their
    /// constants run on little fuel.
    fn builds(&self, buffers: Buffers<'_>, asked: bool) -> (Vec<Problem>, Vec<Checked>) {
        let manifest_path = canonical(&self.root.join(MANIFEST));
        let packages = match &self.packages {
            Ok(packages) => packages,
            Err(error) => return (vec![resolve_problem(manifest_path, error)], Vec::new()),
        };
        let manifest = &packages.root().manifest;
        // WIT that can't be read is none, which the build says.
        let wit = files::wit(packages).unwrap_or_default();
        let component = manifest.component.as_ref();
        let module = component.map(|component| (&component.entry, component.settings(wit.clone())));
        let library = manifest.library.as_ref();
        let library = library.map(|library| (&library.entry, library.settings(wit)));

        let mut problems = Vec::new();
        let mut checked = Vec::new();
        for (entry, settings) in module.into_iter().chain(library) {
            let settings = match asked {
                true => brief(settings),
                false => settings,
            };
            let found = match Files::new(packages, self.root.join(entry), settings) {
                Ok(mut files) => {
                    let overlay = Overlay {
                        files: &mut files,
                        buffers,
                    };
                    let (found, analysis) = overlay.problems(&manifest_path);
                    checked.extend(analysis.map(|(analysis, whole)| Checked {
                        files,
                        analysis,
                        whole,
                    }));
                    found
                }
                Err(e) => {
                    let message = format!("cannot read {}: {e}", entry.display());
                    vec![Problem::in_manifest(manifest_path.clone(), message)]
                }
            };
            // A file both use has its errors found twice.
            for problem in found {
                if !problems.contains(&problem) {
                    problems.push(problem);
                }
            }
        }
        (problems, checked)
    }
}

impl Problem {
    /// A problem with the whole of the manifest at `path`.
    fn in_manifest(path: PathBuf, message: String) -> Self {
        Self {
            place: Place {
                path,
                range: Range::default(),
            },
            message,
            notes: Vec::new(),
        }
    }
}

impl Overlay<'_, '_> {
    /// The errors of compiling the files, those that no file holds placed
    /// in the manifest at `manifest_path`, and the files as checked, with
    /// whether they loaded whole, unless the compiler crashed.
    fn problems(mut self, manifest_path: &Path) -> (Vec<Problem>, Option<(Analysis, bool)>) {
        // Half-written code is what the compiler is least tested on, and a
        // bug in it shouldn't end the server.
        let checked = panic::catch_unwind(AssertUnwindSafe(|| self.check()));
        let Ok((errors, analysis)) = checked else {
            let message = "the compiler crashed checking this package".to_string();
            let problem = Problem::in_manifest(manifest_path.to_path_buf(), message);
            return (vec![problem], None);
        };
        let problems = errors.iter().map(|error| {
            let message = error.to_string();
            let Some(span) = error.span() else {
                return Problem::in_manifest(manifest_path.to_path_buf(), message);
            };
            let notes = error.instances().iter().map(|site| Note {
                place: self.place(site.span),
                message: format!("required by `{}` here", site.name),
            });
            Problem {
                notes: notes.collect(),
                place: self.place(span),
                message,
            }
        });
        (problems.collect(), analysis)
    }

    /// Loads and type checks the files, as [`duck_compiler::compile`] does
    /// before emitting them: the errors of the first to fail, and the files
    /// as checked, with whether they loaded whole. Those that don't are
    /// checked for what did load of them, which has no errors to give, and
    /// may be more than the compiler can check.
    fn check(&mut self) -> (Vec<Error>, Option<(Analysis, bool)>) {
        let (program, errors) = load::load_partial(self);
        let settings = self.settings();
        if !errors.is_empty() {
            let settings = brief(settings);
            let analyze = AssertUnwindSafe(|| ty::analyze(program, &settings));
            let analysis = panic::catch_unwind(analyze).ok();
            return (errors, analysis.map(|analysis| (analysis, false)));
        }
        let analysis = ty::analyze(program, &settings);
        let errors = analysis.errors().iter().cloned().map(Error::Type);
        (errors.collect(), Some((analysis, true)))
    }

    fn place(&mut self, span: Span) -> Place {
        let src = self.contents(span.file);
        Place {
            path: self.files.path(span.file).to_path_buf(),
            range: range(&src, span.start, span.end),
        }
    }
}

impl FileManager for Overlay<'_, '_> {
    fn entry_point(&mut self) -> FileId {
        self.files.entry_point()
    }

    fn display_name(&mut self, id: FileId) -> String {
        self.files.display_name(id)
    }

    fn contents(&mut self, id: FileId) -> String {
        match (self.buffers)(self.files.path(id)) {
            Some(text) => text.to_string(),
            None => self.files.contents(id),
        }
    }

    fn open(&mut self, from: FileId, path: &[&str]) -> Option<FileId> {
        self.files.open(from, path)
    }

    fn open_package(&mut self, from: FileId, name: &str) -> Option<FileId> {
        self.files.open_package(from, name)
    }

    fn settings(&mut self) -> Settings {
        self.files.settings()
    }
}

/// `settings` with little fuel for constants, which are run only to ask
/// something of a program that is being written: a loop of one may have no
/// end yet, and what it leaves is never the module's.
fn brief(settings: Settings) -> Settings {
    let fuel = settings
        .fuel
        .map_or(ASKING_FUEL, |fuel| fuel.min(ASKING_FUEL));
    Settings {
        fuel: Some(fuel),
        ..settings
    }
}

/// The directory of the package `path` is in: the nearest directory with a
/// manifest, `path` itself or above it.
pub fn root_of(path: &Path) -> Option<PathBuf> {
    let root = path.ancestors().find(|dir| dir.join(MANIFEST).is_file());
    root.map(Path::to_path_buf)
}

/// The canonical path of `path`, or `path` itself if nothing is there.
pub fn canonical(path: &Path) -> PathBuf {
    fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf())
}

/// Places a failure to resolve the package whose manifest is at
/// `manifest_path`: in the manifest that is wrong if one is, and otherwise in
/// its own.
fn resolve_problem(manifest_path: PathBuf, error: &ResolveError) -> Problem {
    let ResolveError::Manifest { path, error } = error else {
        return Problem::in_manifest(manifest_path, error.to_string());
    };
    let mut problem = Problem::in_manifest(canonical(path), error.to_string());
    if let ManifestError::Toml(error) = error {
        // Without the excerpt of the source that the full message draws.
        problem.message = error.message().to_string();
        if let (Some(span), Ok(src)) = (error.span(), fs::read_to_string(path)) {
            problem.place.range = range(&src, span.start, span.end);
        }
    }
    problem
}

/// Where bytes `start..end` of `src` are, as [`position`] places each.
pub fn range(src: &str, start: usize, end: usize) -> Range {
    Range::new(position(src, start), position(src, end))
}

/// Where byte `offset` of `src` is, with the column in UTF-16 code units, as
/// editors count them unless asked otherwise.
pub fn position(src: &str, offset: usize) -> Position {
    let before = &src[..offset.min(src.len())];
    let line_start = before.rfind('\n').map_or(0, |i| i + 1);
    let line = before.matches('\n').count();
    let column = before[line_start..].encode_utf16().count();
    Position::new(line as u32, column as u32)
}

/// The byte of `src` that `position` is at, which [`position`] gives back.
/// One past the end of its line is the end of the line, and one past the
/// last line is the end of `src`.
pub fn offset(src: &str, position: Position) -> usize {
    let mut lines = src.split_inclusive('\n');
    let before: usize = (lines.by_ref().take(position.line as usize))
        .map(str::len)
        .sum();
    let line = lines.next().unwrap_or_default();
    let line = line.strip_suffix('\n').unwrap_or(line);
    let line = line.strip_suffix('\r').unwrap_or(line);
    let mut units = 0;
    let within = line.char_indices().find(|(_, c)| {
        units += c.len_utf16();
        units > position.character as usize
    });
    before + within.map_or(line.len(), |(at, _)| at)
}

#[cfg(test)]
pub(crate) mod tests {
    use std::collections::HashMap;

    use super::*;

    /// A directory that is removed when dropped.
    pub(crate) struct TempDir(pub(crate) PathBuf);

    impl TempDir {
        pub(crate) fn new(name: &str) -> Self {
            let dir = std::env::temp_dir().join(format!("duck-lsp-{name}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir).unwrap();
            // Canonical, as the paths of problems are.
            Self(fs::canonicalize(dir).unwrap())
        }

        /// Writes each file, at a path relative to the directory.
        pub(crate) fn write(&self, files: &[(&str, &str)]) {
            for (path, contents) in files {
                let path = self.0.join(path);
                fs::create_dir_all(path.parent().unwrap()).unwrap();
                fs::write(path, contents).unwrap();
            }
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    pub(crate) const MODULE: &str = "[component]\nentry = \"main.duck\"\noutput = \"out.wasm\"\nworld = \"wasi:cli/imports@0.3.0\"\n[memory]\nmax = \"16MiB\"\n";

    const LIBRARY: &str = "[library]\nentry = \"lib.duck\"\n";

    /// Checks the package in `dir/app`, with each of `buffers` open in the
    /// editor. Gives each problem as `path:line:column-line:column: message`,
    /// with the path relative to `dir`, followed by its notes.
    fn check(dir: &TempDir, buffers: &[(&str, &str)]) -> Vec<String> {
        let buffers: HashMap<PathBuf, &str> = (buffers.iter())
            .map(|(path, text)| (dir.0.join(path), *text))
            .collect();
        let cache = Cache::new(dir.0.join("no-cache"));
        let mut project = Project::resolve(dir.0.join("app"), &cache);
        let show = |place: &Place, message: &str| {
            let path = place.path.strip_prefix(&dir.0).unwrap().display();
            let Range { start, end } = place.range;
            format!(
                "{path}:{}:{}-{}:{}: {message}",
                start.line, start.character, end.line, end.character
            )
        };
        let problems = project.check(&|path| buffers.get(path).copied());
        let lines = problems.iter().flat_map(|problem| {
            let notes = problem.notes.iter();
            let notes = notes.map(|note| show(&note.place, &note.message));
            std::iter::once(show(&problem.place, &problem.message)).chain(notes)
        });
        lines.collect()
    }

    #[test]
    fn positions_count_utf16_code_units() {
        let src = "let a = 1\nlet s = \"é😀\" @\n";
        let at = |text: &str| {
            let position = position(src, src.find(text).unwrap());
            (position.line, position.character)
        };
        assert_eq!(at("let a"), (0, 0));
        assert_eq!(at("1"), (0, 8));
        assert_eq!(at("é"), (1, 9));
        assert_eq!(at("😀"), (1, 10));
        // `é` is one unit and `😀` two, though they are two bytes and four.
        assert_eq!(at("@"), (1, 14));
        assert_eq!(position(src, src.len()), Position::new(2, 0));
        assert_eq!(position(src, src.len() + 9), Position::new(2, 0));
    }

    #[test]
    fn positions_are_found_again() {
        let src = "let a = 1\r\nlet s = \"é😀\" @\n\nlast";
        for (at, _) in src.char_indices().filter(|(_, c)| *c != '\n') {
            assert_eq!(offset(src, position(src, at)), at);
        }
        assert_eq!(offset(src, position(src, src.len())), src.len());
        // A place past the end of a line is its end, as one in the middle of
        // a character is its start.
        assert_eq!(offset(src, Position::new(0, 99)), src.find('\r').unwrap());
        assert_eq!(offset(src, Position::new(1, 11)), src.find('😀').unwrap());
        assert_eq!(
            offset(src, Position::new(2, 4)),
            src.find("last").unwrap() - 1
        );
        assert_eq!(offset(src, Position::new(9, 0)), src.len());
    }

    /// Where `text` first is in `src`.
    fn at(src: &str, text: &str) -> Position {
        position(src, src.find(text).unwrap())
    }

    /// A package whose module uses a module of its own and a dependency.
    fn package(name: &str) -> (TempDir, Project) {
        let dir = TempDir::new(name);
        dir.write(&[
            (
                "app/Duck.toml",
                &format!("{MODULE}[dependencies]\nutil = {{ path = \"../util\" }}\n"),
            ),
            ("app/main.duck", MAIN),
            (
                "app/geo.duck",
                "pub struct Point:\n    pub x: f32\n    pub y: f32 = 0.0\n    id: i32 = 0\npub fn len(p: Point, scale: f32 = 1.0) -> f32:\n    return p.x * scale\n",
            ),
            ("util/Duck.toml", LIBRARY),
            ("util/lib.duck", "pub fn log(x: f32):\n    pass\n"),
        ]);
        let cache = Cache::new(dir.0.join("no-cache"));
        let project = Project::resolve(dir.0.join("app"), &cache);
        (dir, project)
    }

    const MAIN: &str =
        "use geo\nuse util\nfn main():\n    let p = geo.Point(x: 1.0)\n    util.log(geo.len(p))\n";

    #[test]
    fn a_place_is_described_as_the_package_was_last_checked() {
        let (dir, mut project) = package("hover");
        let main = dir.0.join("app/main.duck");
        let hover = |project: &mut Project, src: &str, text: &str| {
            let (range, text, _) = project.hover(&|_| None, &main, at(src, text))?;
            let Range { start, end } = range;
            Some((start.line, start.character, end.character, text))
        };
        // Nothing is, of one that wasn't.
        assert_eq!(hover(&mut project, MAIN, "p = geo"), None);
        assert_eq!(project.check(&|_| None), []);
        assert_eq!(
            hover(&mut project, MAIN, "p = geo"),
            Some((3, 8, 9, "let p: Point".to_string()))
        );
        assert_eq!(
            hover(&mut project, MAIN, "len(p)"),
            Some((
                4,
                17,
                20,
                "fn len(p: Point, scale: f32 = 1.0) -> f32".to_string()
            ))
        );
        assert_eq!(
            hover(&mut project, MAIN, "log(geo"),
            Some((4, 9, 12, "fn log(x: f32)".to_string()))
        );
        // A name is declared in the file that declares it, which may be of
        // another package.
        let definition = |project: &mut Project, text: &str| {
            let place = project.definition(&|_| None, &main, at(MAIN, text))?;
            let path = place.path.strip_prefix(&dir.0).unwrap().display();
            let Position { line, character } = place.range.start;
            Some(format!("{path}:{line}:{character}"))
        };
        assert_eq!(
            definition(&mut project, "p))"),
            Some("app/main.duck:3:8".into())
        );
        assert_eq!(
            definition(&mut project, "len(p)"),
            Some("app/geo.duck:4:7".into())
        );
        assert_eq!(
            definition(&mut project, "x: 1.0"),
            Some("app/geo.duck:1:8".into())
        );
        assert_eq!(
            definition(&mut project, "log(geo"),
            Some("util/lib.duck:0:7".into())
        );
        assert_eq!(
            definition(&mut project, "util.log"),
            Some("util/lib.duck:0:0".into())
        );
        assert_eq!(definition(&mut project, "1.0"), None);
        let point = at(MAIN, "Point(x");
        assert_eq!(project.implementations(&|_| None, &main, point), []);
        // A file of the package that the module doesn't use is no part of it.
        let unused = dir.0.join("app/unused.duck");
        assert_eq!(project.hover(&|_| None, &unused, Position::new(0, 0)), None);
        assert_eq!(
            project.definition(&|_| None, &unused, Position::new(0, 0)),
            None
        );

        // What is open in the editor is described as it is there, even
        // where a line of it doesn't parse.
        let edited = "use geo\nfn main():\n    let p = geo.Point(x: 1.0)\n    let d = geo.len(p,\n    let q = (p, 2)\n";
        let buffers = |path: &Path| (path == main).then_some(edited);
        assert_eq!(project.check(&buffers).len(), 1);
        let (range, text, _) = project
            .hover(&buffers, &main, at(edited, "q = (p"))
            .unwrap();
        assert_eq!(range.start, Position::new(4, 8));
        assert_eq!(text, "let q: tuple(Point, i32)");
    }

    #[test]
    fn what_can_be_written_is_suggested_of_a_line_that_does_not_parse() {
        let (dir, project) = package("complete");
        let main = dir.0.join("app/main.duck");
        let complete = |src: &str, text: &str| {
            let buffers = |path: &Path| (path == main).then_some(src);
            let position = position(src, src.find(text).unwrap() + text.len());
            let suggested = project.complete(&buffers, &main, src, position, false);
            let kind = match suggested.names {
                true => "names",
                false => "members",
            };
            let suggestions = suggested.suggestions.into_iter();
            let names: Vec<_> = suggestions.map(|s| s.completion.name).collect();
            (names, kind)
        };
        let fields = |names: &[&str]| (names.iter().map(|n| n.to_string()).collect(), "members");
        let src = "use geo\nfn main():\n    let p = geo.Point(x: 1.0)\n    let d = geo.len(p.\n";
        // A field that the module of the struct keeps to itself is none.
        assert_eq!(complete(src, "len(p."), fields(&["x", "y"]));
        assert_eq!(complete(src, "let d = geo."), fields(&["Point", "len"]));
        assert_eq!(
            complete(src, "main():\n    let p = geo."),
            fields(&["Point", "len"])
        );
        let src = "use geo\nfn main():\n    let p = geo.Point(x: 1.0)\n    if p.x < 1.0:\n        let near = (p, 1)\n        ne\n    return nea\n";
        let (names, kind) = complete(src, "        ne");
        assert_eq!(
            (&names[..4], kind),
            (&["near", "p", "geo", "main"].map(String::from)[..], "names")
        );
        let (names, _) = complete(src, "return nea");
        assert_eq!(names[..3], ["p", "geo", "main"]);
        let src = src.replace("        ne\n", "        g(near.0.\n");
        assert_eq!(complete(&src, "g(near.0."), fields(&["x", "y"]));
        assert_eq!(complete(&src, "g(near.0"), (Vec::new(), "members"));

        let signature = |src: &str, text: &str| {
            let buffers = |path: &Path| (path == main).then_some(src);
            let position = position(src, src.find(text).unwrap() + text.len());
            let (signature, active) = project.signature(&buffers, &main, src, position)?;
            Some((signature.label, active))
        };
        let len = "fn len(p: Point, scale: f32 = 1.0) -> f32".to_string();
        let src = "use geo\nfn main():\n    let p = geo.Point(x: 1.0, y: \n    let d = geo.len(p, \n    geo.len(scale: 2.0, p\n";
        assert_eq!(signature(src, "geo.len(p, "), Some((len.clone(), Some(1))));
        assert_eq!(
            signature(src, "geo.len(scale: 2"),
            Some((len.clone(), Some(1)))
        );
        assert_eq!(
            signature(src, "geo.len(scale: 2.0, p"),
            Some((len, Some(1)))
        );
        let point = "Point(x: f32, y: f32 = 0.0, id: i32 = 0)".to_string();
        assert_eq!(signature(src, "Point(x: 1.0, y: "), Some((point, Some(1))));
        assert_eq!(signature(src, "let p = "), None);
        // A generic struct takes its type arguments, and then its fields.
        let src = "struct(K, V = K) Entry:\n    key: K\n    value: V\nfn main():\n    let e = Entry(u8, V: \n    let f = Entry(u8)(key: 1, \n";
        let params = "Entry(K, V = K)".to_string();
        assert_eq!(signature(src, "Entry("), Some((params.clone(), Some(0))));
        assert_eq!(signature(src, "Entry(u8, V: "), Some((params, Some(1))));
        let fields = "Entry(key: K, value: V)".to_string();
        assert_eq!(
            signature(src, "Entry(u8)(key: 1, "),
            Some((fields, Some(1)))
        );
    }

    #[test]
    fn errors_are_placed_in_the_files_they_are_in() {
        let dir = TempDir::new("placed");
        dir.write(&[
            (
                "app/Duck.toml",
                &format!("{MODULE}[dependencies]\nutil = {{ path = \"../util\" }}\n"),
            ),
            ("app/main.duck", "use src.a\nuse util\nlet x: Nope = 1\n"),
            ("app/src/a.duck", "let ok = 1\nlet y = @\n"),
            ("app/src/unused.duck", "let z = @\n"),
            ("util/Duck.toml", LIBRARY),
            ("util/lib.duck", "fn f(: i32):\n    pass\n"),
        ]);
        assert_eq!(
            check(&dir, &[]),
            [
                "app/src/a.duck:1:8-1:9: unexpected character '@'",
                "util/lib.duck:0:5-0:6: expected identifier, found `:`",
            ]
        );

        dir.write(&[
            ("app/src/a.duck", ""),
            ("util/lib.duck", "pub let one = 1\n"),
        ]);
        assert_eq!(
            check(&dir, &[]),
            ["app/main.duck:2:7-2:11: unknown type `Nope`"]
        );
    }

    #[test]
    fn open_files_are_read_as_they_are_in_the_editor() {
        let dir = TempDir::new("buffers");
        dir.write(&[
            ("app/Duck.toml", MODULE),
            ("app/main.duck", "use a\nlet x = a.y\n"),
            ("app/a.duck", "pub let y = 1\n"),
        ]);
        assert_eq!(check(&dir, &[]), [] as [&str; 0]);
        assert_eq!(
            check(&dir, &[("app/a.duck", "\n\npub let y: Nope = 1\n")]),
            ["app/a.duck:2:11-2:15: unknown type `Nope`"]
        );
        assert_eq!(
            check(&dir, &[("app/main.duck", "let x = nope\n")]),
            ["app/main.duck:0:8-0:12: unknown name `nope`"]
        );
    }

    #[test]
    fn modules_and_libraries_are_both_checked() {
        let dir = TempDir::new("both");
        dir.write(&[
            ("app/Duck.toml", &format!("{MODULE}{LIBRARY}")),
            ("app/main.duck", "use shared\nlet a: A = 1\n"),
            ("app/lib.duck", "use shared\nlet b: B = 1\n"),
            ("app/shared.duck", "let s: S = 1\n"),
        ]);
        assert_eq!(
            check(&dir, &[]),
            [
                "app/shared.duck:0:7-0:8: unknown type `S`",
                "app/main.duck:1:7-1:8: unknown type `A`",
                "app/lib.duck:1:7-1:8: unknown type `B`",
            ]
        );
    }

    #[test]
    fn errors_in_instances_note_the_instances_that_led_to_them() {
        let dir = TempDir::new("instances");
        dir.write(&[
            ("app/Duck.toml", MODULE),
            (
                "app/main.duck",
                "fn(T) nest(x: T):\n    nest((x, x))\nfn f():\n    nest(true)\n",
            ),
        ]);
        // Each instance of `nest` needs another, without end.
        let problems = check(&dir, &[]);
        assert!(problems.len() > 2, "{problems:?}");
        assert!(
            problems[0].starts_with("app/main.duck:3:4-3:14: "),
            "{problems:?}"
        );
        assert_eq!(
            problems[1],
            "app/main.duck:1:4-1:16: required by `nest(bool)` here"
        );
    }

    #[test]
    fn errors_no_file_holds_are_placed_in_the_manifest() {
        let dir = TempDir::new("manifest");
        // A program, which is what a component is of no other world.
        let start = MODULE.replace("world = \"wasi:cli/imports@0.3.0\"", "start = \"main\"");
        dir.write(&[("app/Duck.toml", &start), ("app/main.duck", "")]);
        assert_eq!(
            check(&dir, &[]),
            ["app/Duck.toml:0:0-0:0: no function named `main` to start"]
        );

        fs::remove_file(dir.0.join("app/main.duck")).unwrap();
        let problems = check(&dir, &[]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("app/Duck.toml:0:0-0:0: cannot read main.duck: "),
            "{problems:?}"
        );
    }

    #[test]
    fn manifests_that_cannot_be_resolved() {
        let dir = TempDir::new("unresolved");
        dir.write(&[(
            "app/Duck.toml",
            "[library]\nentry = \"lib.duck\"\nnope = 1\n",
        )]);
        let problems = check(&dir, &[]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("app/Duck.toml:2:0-2:4: unknown field `nope`"),
            "{problems:?}"
        );

        dir.write(&[("app/Duck.toml", "[dependencies]\n")]);
        assert_eq!(
            check(&dir, &[]),
            ["app/Duck.toml:0:0-0:0: needs a [component] or [library] table"]
        );

        // A dependency's manifest holds what is wrong with it.
        dir.write(&[
            (
                "app/Duck.toml",
                &format!("{LIBRARY}[dependencies]\nutil = {{ path = \"../util\" }}\n"),
            ),
            ("app/lib.duck", ""),
            ("util/Duck.toml", "[library]\n"),
        ]);
        let problems = check(&dir, &[]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("util/Duck.toml:0:0-0:9: missing field `entry`"),
            "{problems:?}"
        );

        // But one that is missing is a problem with the package wanting it.
        fs::remove_file(dir.0.join("util/Duck.toml")).unwrap();
        let problems = check(&dir, &[]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("app/Duck.toml:0:0-0:0: cannot read "),
            "{problems:?}"
        );
    }

    #[test]
    fn a_crash_of_the_compiler_is_a_problem_of_the_package() {
        let dir = TempDir::new("crash");
        dir.write(&[("app/Duck.toml", MODULE), ("app/main.duck", "")]);
        let cache = Cache::new(dir.0.join("no-cache"));
        let mut project = Project::resolve(dir.0.join("app"), &cache);
        let problems = project.check(&|_| panic!("as a bug in the compiler would"));
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert_eq!(problems[0].place.path, dir.0.join("app/Duck.toml"));
        assert_eq!(
            problems[0].message,
            "the compiler crashed checking this package"
        );
    }

    #[test]
    fn packages_are_found_from_the_files_in_them() {
        let dir = TempDir::new("root");
        dir.write(&[
            ("app/Duck.toml", MODULE),
            ("app/src/deep/a.duck", ""),
            ("app/libs/util/Duck.toml", LIBRARY),
            ("app/libs/util/lib.duck", ""),
        ]);
        let root = |path: &str| root_of(&dir.0.join(path));
        assert_eq!(root("app"), Some(dir.0.join("app")));
        assert_eq!(root("app/src/deep/a.duck"), Some(dir.0.join("app")));
        assert_eq!(root("app/src/deep/unsaved.duck"), Some(dir.0.join("app")));
        assert_eq!(
            root("app/libs/util/lib.duck"),
            Some(dir.0.join("app/libs/util"))
        );
        assert_eq!(root("other.duck"), None);
    }
}

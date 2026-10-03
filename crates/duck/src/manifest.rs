//! `Duck.toml`, the metadata of a duck package: the module it builds, the
//! library it offers other packages, and the packages it depends on.

use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::path::PathBuf;

use duck_compiler::file::{MemoryLimits, Settings, StaticSection};
use duck_compiler::lex;
use serde::Deserialize;

/// The name of the manifest file at the root of every module.
pub const MANIFEST: &str = "Duck.toml";

/// The size of a wasm page, which every memory size is a whole number of.
const PAGE_SIZE: u64 = 64 * 1024;

/// The most pages a 32-bit wasm memory can hold: 4 GiB.
pub const MAX_PAGES: u32 = 1 << 16;

/// A validated `Duck.toml`. It has a module, a library, or both.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    pub module: Option<Module>,
    pub library: Option<Library>,
    /// Each package this one can import, by the name it imports it as.
    pub dependencies: BTreeMap<String, Dependency>,
}

/// The wasm module a package builds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    /// The file the module is compiled from, relative to the manifest.
    pub entry: PathBuf,
    /// Where the wasm module is written, relative to the manifest.
    pub output: PathBuf,
    /// The function run when the module is instantiated.
    pub start: Option<String>,
    pub memory: MemoryLimits,
    pub static_section: StaticSection,
}

/// What a package offers the packages that depend on it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Library {
    /// The file other packages import, relative to the manifest.
    pub entry: PathBuf,
}

/// Where a dependency is found.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Dependency {
    /// The directory holding its manifest, relative to this manifest.
    Path(PathBuf),
    /// A commit of a git repository.
    Git {
        url: String,
        reference: GitRef,
        /// The directory in the repository holding its manifest, if not the
        /// top.
        path: Option<PathBuf>,
    },
}

/// What names a commit of a git dependency.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GitRef {
    /// A tag, taken never to move.
    Tag(String),
    /// A commit hash, or a prefix of one.
    Rev(String),
}

#[derive(Debug)]
pub enum ManifestError {
    /// Not TOML, or not shaped like a manifest.
    Toml(toml::de::Error),
    Size {
        key: &'static str,
        value: String,
        kind: SizeErrorKind,
    },
    MinExceedsMax {
        min: String,
        max: String,
    },
    StaticStartExceedsEnd {
        start: String,
        end: String,
    },
    /// Neither a `[module]` nor a `[library]`.
    Empty,
    /// A `[module]` without a `[memory]`.
    MissingMemory,
    /// A `[memory]` without a `[module]` to give it to.
    MemoryWithoutModule,
    /// A dependency named something that can't be imported.
    DependencyName(String),
    /// A dependency with neither a `path` nor a `git`.
    NoSource(String),
    /// A git dependency without exactly one of `tag` and `rev`.
    GitRef(String),
    /// A git dependency on a branch, which moves.
    Branch(String),
    /// A dependency that names a commit without a `git` to find it in.
    RefWithoutGit(String),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SizeErrorKind {
    /// Not a number followed by a unit.
    Malformed,
    NotPageMultiple,
    TooLarge,
    /// An address that 32-bit memory can't hold an array at.
    NotAnAddress,
}

/// `Duck.toml` as written, before sizes are checked.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Raw {
    module: Option<RawModule>,
    memory: Option<RawMemory>,
    library: Option<RawLibrary>,
    #[serde(default)]
    dependencies: BTreeMap<String, RawDependency>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawModule {
    entry: PathBuf,
    output: PathBuf,
    start: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawMemory {
    min: String,
    max: Option<String>,
    #[serde(rename = "static")]
    static_section: RawStaticSection,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawStaticSection {
    start: String,
    end: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawLibrary {
    entry: PathBuf,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawDependency {
    path: Option<PathBuf>,
    git: Option<String>,
    tag: Option<String>,
    rev: Option<String>,
    /// Only read to be refused.
    branch: Option<String>,
}

impl Manifest {
    pub fn parse(src: &str) -> Result<Self, ManifestError> {
        let raw: Raw = toml::from_str(src).map_err(ManifestError::Toml)?;
        let module = match (raw.module, raw.memory) {
            (Some(module), Some(memory)) => Some(Module::parse(module, memory)?),
            (Some(_), None) => return Err(ManifestError::MissingMemory),
            (None, Some(_)) => return Err(ManifestError::MemoryWithoutModule),
            (None, None) => None,
        };
        let library = raw.library.map(|library| Library {
            entry: library.entry,
        });
        if module.is_none() && library.is_none() {
            return Err(ManifestError::Empty);
        }
        let mut dependencies = BTreeMap::new();
        for (name, dependency) in raw.dependencies {
            if !lex::is_identifier(&name) {
                return Err(ManifestError::DependencyName(name));
            }
            let dependency = dependency.validate(&name)?;
            dependencies.insert(name, dependency);
        }
        Ok(Self {
            module,
            library,
            dependencies,
        })
    }

    /// The directory holding the manifest nearest the working directory: the
    /// working directory itself or one of its ancestors. It is given relative
    /// to the working directory, so paths under it read as they were written.
    pub fn find() -> io::Result<Option<PathBuf>> {
        let cwd = std::env::current_dir()?;
        let found = cwd
            .ancestors()
            .position(|dir| dir.join(MANIFEST).is_file())
            .map(|depth| (0..depth).map(|_| "..").collect());
        Ok(found)
    }
}

impl RawDependency {
    fn validate(self, name: &str) -> Result<Dependency, ManifestError> {
        let error = |make: fn(String) -> ManifestError| Err(make(name.to_string()));
        let Some(url) = self.git else {
            if self.tag.is_some() || self.rev.is_some() || self.branch.is_some() {
                return error(ManifestError::RefWithoutGit);
            }
            return match self.path {
                Some(path) => Ok(Dependency::Path(path)),
                None => error(ManifestError::NoSource),
            };
        };
        let reference = match (self.tag, self.rev, self.branch) {
            (_, _, Some(_)) => return error(ManifestError::Branch),
            (Some(tag), None, None) => GitRef::Tag(tag),
            (None, Some(rev), None) => GitRef::Rev(rev),
            _ => return error(ManifestError::GitRef),
        };
        Ok(Dependency::Git {
            url,
            reference,
            path: self.path,
        })
    }
}

impl Module {
    /// How the module is compiled.
    pub fn settings(&self) -> Settings {
        Settings {
            memory: self.memory,
            static_section: self.static_section,
            start: self.start.clone(),
        }
    }

    fn parse(module: RawModule, memory: RawMemory) -> Result<Self, ManifestError> {
        let RawMemory {
            min,
            max,
            static_section,
        } = memory;
        let min_pages = pages("memory.min", &min)?;
        let max_pages = max
            .as_deref()
            .map(|max| pages("memory.max", max))
            .transpose()?;
        if let Some(max) = max
            && max_pages.is_some_and(|max_pages| min_pages > max_pages)
        {
            return Err(ManifestError::MinExceedsMax { min, max });
        }
        let RawStaticSection { start, end } = static_section;
        let static_section = StaticSection {
            start: address("memory.static.start", &start)?,
            end: address("memory.static.end", &end)?,
        };
        if static_section.start > static_section.end {
            return Err(ManifestError::StaticStartExceedsEnd { start, end });
        }
        Ok(Self {
            entry: module.entry,
            output: module.output,
            start: module.start,
            memory: MemoryLimits {
                min_pages,
                max_pages,
            },
            static_section,
        })
    }
}

impl Library {
    /// How the library is checked on its own: with room for any data, as
    /// the memory is that of whichever module imports it.
    pub fn settings(&self) -> Settings {
        Settings {
            memory: MemoryLimits {
                min_pages: MAX_PAGES,
                max_pages: None,
            },
            static_section: StaticSection {
                start: 0,
                end: u32::MAX,
            },
            start: None,
        }
    }
}

/// The number of wasm pages in `value`, a size such as `64KiB` or `2pgs`.
fn pages(key: &'static str, value: &str) -> Result<u32, ManifestError> {
    let bytes = bytes(key, value)?;
    if bytes % PAGE_SIZE != 0 {
        return Err(size_error(key, value, SizeErrorKind::NotPageMultiple));
    }
    Ok((bytes / PAGE_SIZE) as u32)
}

/// The address `value`, a size such as `1024B` or `4KiB` from the start of
/// memory.
fn address(key: &'static str, value: &str) -> Result<u32, ManifestError> {
    u32::try_from(bytes(key, value)?)
        .map_err(|_| size_error(key, value, SizeErrorKind::NotAnAddress))
}

/// The number of bytes in `value`, a size such as `64KiB` or `2pgs`, which
/// is at most 4GiB.
fn bytes(key: &'static str, value: &str) -> Result<u64, ManifestError> {
    let error = |kind| size_error(key, value, kind);
    let digits = value.find(|c: char| !c.is_ascii_digit()).unwrap_or(0);
    let (number, unit) = value.split_at(digits);
    let unit_size = match unit {
        "B" => 1,
        "KiB" => 1 << 10,
        "MiB" => 1 << 20,
        "GiB" => 1 << 30,
        "pgs" => PAGE_SIZE,
        _ => return Err(error(SizeErrorKind::Malformed)),
    };
    if number.is_empty() {
        return Err(error(SizeErrorKind::Malformed));
    }
    // Only digits are left, so the number can fail to parse only by overflowing.
    let bytes = number
        .parse::<u64>()
        .ok()
        .and_then(|number| number.checked_mul(unit_size))
        .ok_or(error(SizeErrorKind::TooLarge))?;
    if bytes > u64::from(MAX_PAGES) * PAGE_SIZE {
        return Err(error(SizeErrorKind::TooLarge));
    }
    Ok(bytes)
}

fn size_error(key: &'static str, value: &str, kind: SizeErrorKind) -> ManifestError {
    ManifestError::Size {
        key,
        value: value.to_string(),
        kind,
    }
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Toml(e) => write!(f, "{}", e.to_string().trim_end()),
            Self::Size { key, value, kind } => write!(f, "{key} \"{value}\" {kind}"),
            Self::MinExceedsMax { min, max } => {
                write!(f, "memory.min \"{min}\" exceeds memory.max \"{max}\"")
            }
            Self::StaticStartExceedsEnd { start, end } => write!(
                f,
                "memory.static.start \"{start}\" exceeds memory.static.end \"{end}\""
            ),
            Self::Empty => write!(f, "needs a [module] or [library] table"),
            Self::MissingMemory => write!(f, "[module] needs a [memory] table"),
            Self::MemoryWithoutModule => write!(f, "[memory] needs a [module] table"),
            Self::DependencyName(name) => {
                write!(f, "dependency name `{name}` is not an identifier")
            }
            Self::NoSource(name) => write!(f, "dependency `{name}` needs a `path` or a `git`"),
            Self::GitRef(name) => {
                write!(f, "git dependency `{name}` needs one of `tag` and `rev`")
            }
            Self::Branch(name) => write!(
                f,
                "git dependency `{name}` can't follow a branch; pin a `tag` or a `rev`"
            ),
            Self::RefWithoutGit(name) => write!(
                f,
                "dependency `{name}` has a `tag`, `rev`, or `branch` but no `git`"
            ),
        }
    }
}

impl std::error::Error for ManifestError {}

impl fmt::Display for SizeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed => {
                write!(f, "is not a number followed by B, KiB, MiB, GiB, or pgs")
            }
            Self::NotPageMultiple => write!(f, "is not a multiple of 64KiB"),
            Self::TooLarge => write!(f, "exceeds 4GiB"),
            Self::NotAnAddress => write!(f, "is not below 4GiB"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const STATIC: &str = "static = { start = \"0B\", end = \"64KiB\" }\n";

    /// A module whose `[memory]` has `memory` and then [`STATIC`].
    fn with_memory(memory: &str) -> Result<Manifest, ManifestError> {
        with_static(&format!("{memory}{STATIC}"))
    }

    /// A module whose `[memory]` is `memory`.
    fn with_static(memory: &str) -> Result<Manifest, ManifestError> {
        Manifest::parse(&format!(
            "[module]\nentry = \"src/main.duck\"\noutput = \"build/out.wasm\"\n\n[memory]\n{memory}"
        ))
    }

    fn size(value: &str) -> Result<u32, String> {
        pages("memory.min", value).map_err(|e| e.to_string())
    }

    #[test]
    fn sizes() {
        assert_eq!(size("0KiB"), Ok(0));
        assert_eq!(size("64KiB"), Ok(1));
        assert_eq!(size("1MiB"), Ok(16));
        assert_eq!(size("4GiB"), Ok(65536));
        assert_eq!(size("3pgs"), Ok(3));
        assert_eq!(size("65536pgs"), Ok(65536));
        assert_eq!(size("65536B"), Ok(1));
    }

    #[test]
    fn addresses() {
        let address = |value| address("memory.static.end", value).map_err(|e| e.to_string());
        assert_eq!(address("0B"), Ok(0));
        assert_eq!(address("1025B"), Ok(1025));
        assert_eq!(address("4KiB"), Ok(4096));
        assert_eq!(address("4294967295B"), Ok(u32::MAX));
        assert_eq!(
            address("4GiB"),
            Err("memory.static.end \"4GiB\" is not below 4GiB".to_string())
        );
        assert_eq!(
            address("5GiB"),
            Err("memory.static.end \"5GiB\" exceeds 4GiB".to_string())
        );
    }

    #[test]
    fn size_errors() {
        let malformed = "is not a number followed by B, KiB, MiB, GiB, or pgs";
        for value in [
            "", "64", "KiB", "64 KiB", "64kib", "64KB", "1pg", "-1pgs", "1.5MiB", "B", "8b",
        ] {
            assert_eq!(
                size(value),
                Err(format!("memory.min \"{value}\" {malformed}")),
                "{value:?}"
            );
        }
        assert_eq!(
            size("100KiB"),
            Err("memory.min \"100KiB\" is not a multiple of 64KiB".to_string())
        );
        assert_eq!(
            size("65537pgs"),
            Err("memory.min \"65537pgs\" exceeds 4GiB".to_string())
        );
        for value in ["18446744073709551615GiB", "99999999999999999999pgs"] {
            assert_eq!(
                size(value),
                Err(format!("memory.min \"{value}\" exceeds 4GiB")),
                "{value:?}"
            );
        }
    }

    #[test]
    fn parses() {
        let manifest = with_memory("min = \"1pgs\"\nmax = \"16MiB\"\n").unwrap();
        assert_eq!(
            manifest,
            Manifest {
                module: Some(Module {
                    entry: "src/main.duck".into(),
                    output: "build/out.wasm".into(),
                    start: None,
                    memory: MemoryLimits {
                        min_pages: 1,
                        max_pages: Some(256),
                    },
                    static_section: StaticSection {
                        start: 0,
                        end: 64 * 1024,
                    },
                }),
                library: None,
                dependencies: BTreeMap::new(),
            }
        );
        let manifest = with_memory("min = \"64KiB\"\n").unwrap();
        assert_eq!(manifest.module.unwrap().memory.max_pages, None);
        let manifest =
            with_static("min = \"1pgs\"\nstatic.start = \"1KiB\"\nstatic.end = \"1025B\"\n")
                .unwrap();
        assert_eq!(
            manifest.module.unwrap().static_section,
            StaticSection {
                start: 1024,
                end: 1025
            }
        );
        let manifest = Manifest::parse(&format!(
            "[module]\nentry = \"a.duck\"\noutput = \"a.wasm\"\nstart = \"init\"\n\n[memory]\nmin = \"1pgs\"\n{STATIC}",
        ))
        .unwrap();
        assert_eq!(manifest.module.unwrap().start.as_deref(), Some("init"));
    }

    #[test]
    fn libraries_and_dependencies() {
        let manifest = Manifest::parse(
            "[library]\nentry = \"src/lib.duck\"\n\n[dependencies]\nmath = { path = \"../math\" }\nutil = { path = \"/abs/util\" }\n",
        )
        .unwrap();
        assert_eq!(
            manifest,
            Manifest {
                module: None,
                library: Some(Library {
                    entry: "src/lib.duck".into(),
                }),
                dependencies: BTreeMap::from([
                    ("math".to_string(), Dependency::Path("../math".into())),
                    ("util".to_string(), Dependency::Path("/abs/util".into())),
                ]),
            }
        );
        let both = Manifest::parse(&format!(
            "[module]\nentry = \"a.duck\"\noutput = \"a.wasm\"\n[memory]\nmin = \"1pgs\"\n{STATIC}[library]\nentry = \"lib.duck\"\n",
        ))
        .unwrap();
        assert!(both.module.is_some() && both.library.is_some());
    }

    #[test]
    fn git_dependencies() {
        let manifest = Manifest::parse(
            "[library]\nentry = \"a.duck\"\n[dependencies]\na = { git = \"https://x.org/a\", tag = \"v1\" }\nb = { git = \"../b\", rev = \"abc123\", path = \"libs/b\" }\n",
        )
        .unwrap();
        assert_eq!(
            manifest.dependencies,
            BTreeMap::from([
                (
                    "a".to_string(),
                    Dependency::Git {
                        url: "https://x.org/a".to_string(),
                        reference: GitRef::Tag("v1".to_string()),
                        path: None,
                    }
                ),
                (
                    "b".to_string(),
                    Dependency::Git {
                        url: "../b".to_string(),
                        reference: GitRef::Rev("abc123".to_string()),
                        path: Some("libs/b".into()),
                    }
                ),
            ])
        );
    }

    #[test]
    fn dependency_errors() {
        let error = |dependency: &str| {
            let src = format!("[library]\nentry = \"a.duck\"\n[dependencies]\nd = {dependency}\n");
            Manifest::parse(&src).unwrap_err().to_string()
        };
        assert_eq!(error("{}"), "dependency `d` needs a `path` or a `git`");
        assert_eq!(
            error("{ git = \"u\" }"),
            "git dependency `d` needs one of `tag` and `rev`"
        );
        assert_eq!(
            error("{ git = \"u\", tag = \"v1\", rev = \"abc\" }"),
            "git dependency `d` needs one of `tag` and `rev`"
        );
        assert_eq!(
            error("{ git = \"u\", branch = \"main\" }"),
            "git dependency `d` can't follow a branch; pin a `tag` or a `rev`"
        );
        assert_eq!(
            error("{ path = \"p\", tag = \"v1\" }"),
            "dependency `d` has a `tag`, `rev`, or `branch` but no `git`"
        );
    }

    #[test]
    fn package_errors() {
        let error = |src: &str| Manifest::parse(src).unwrap_err().to_string();
        assert_eq!(error(""), "needs a [module] or [library] table");
        assert_eq!(
            error("[module]\nentry = \"a.duck\"\noutput = \"a.wasm\"\n"),
            "[module] needs a [memory] table"
        );
        assert_eq!(
            error(&format!(
                "[library]\nentry = \"a.duck\"\n[memory]\nmin = \"1pgs\"\n{STATIC}"
            )),
            "[memory] needs a [module] table"
        );
        assert_eq!(
            error("[library]\nentry = \"a.duck\"\n[dependencies]\nmy-lib = { path = \"x\" }\n"),
            "dependency name `my-lib` is not an identifier"
        );
        assert!(
            error("[library]\nentry = \"a.duck\"\n[dependencies]\nx = { route = \"x\" }\n")
                .contains("unknown field `route`")
        );
    }

    #[test]
    fn memory_errors() {
        let error = |memory| with_memory(memory).unwrap_err().to_string();
        assert_eq!(
            error("min = \"2MiB\"\nmax = \"1MiB\"\n"),
            "memory.min \"2MiB\" exceeds memory.max \"1MiB\""
        );
        assert!(error("max = \"1MiB\"\n").contains("missing field `min`"));
        assert!(
            error("min = \"1pgs\"\nmax_pages = \"1pgs\"\n").contains("unknown field `max_pages`")
        );
        assert!(error("min = 1\n").contains("invalid type"));
    }

    #[test]
    fn static_section_errors() {
        let error = |memory| with_static(memory).unwrap_err().to_string();
        assert_eq!(
            error("min = \"1pgs\"\nstatic = { start = \"2KiB\", end = \"1KiB\" }\n"),
            "memory.static.start \"2KiB\" exceeds memory.static.end \"1KiB\""
        );
        assert_eq!(
            error("min = \"1pgs\"\nstatic = { start = \"0B\", end = \"1kb\" }\n"),
            "memory.static.end \"1kb\" is not a number followed by B, KiB, MiB, GiB, or pgs"
        );
        assert!(error("min = \"1pgs\"\n").contains("missing field `static`"));
        assert!(
            error("min = \"1pgs\"\nstatic = { start = \"0B\" }\n").contains("missing field `end`")
        );
        assert!(
            error("min = \"1pgs\"\nstatic = { start = \"0B\", end = \"1B\", size = \"1B\" }\n")
                .contains("unknown field `size`")
        );
    }
}

//! `Duck.toml`, the metadata of a duck package: the component it builds, the
//! library it offers other packages, the directory of its tests, and the
//! packages it depends on.

use std::collections::BTreeMap;
use std::fmt;
use std::io;
use std::ops::Range;
use std::path::{Component as Part, Path, PathBuf};

use duck_compiler::file::{Settings, Wit};
use duck_compiler::lex;
use duck_compiler::world::COMMAND;
use serde::Deserialize;
use toml::de::DeTable;

/// The name of the manifest file at the root of every package.
pub const MANIFEST: &str = "Duck.toml";

/// The table of a manifest that holds its dependencies, each by the name
/// the package uses it as.
pub const DEPENDENCIES: &str = "dependencies";

/// The table of a manifest that says what component the package builds.
pub const COMPONENT: &str = "component";

/// The table of a manifest that says what the package offers others.
pub const LIBRARY: &str = "library";

/// The key of [`COMPONENT`] and of [`LIBRARY`] that names the file each is
/// entered by.
pub const ENTRY: &str = "entry";

/// The table of a manifest that says where the tests of the package are.
pub const TEST: &str = "test";

/// The key of [`TEST`] that names the test directory.
pub const DIR: &str = "dir";

/// The test directory of a package that names none, relative to its
/// manifest.
pub const DEFAULT_TEST_DIR: &str = "tests";

/// The size of a wasm page, which every memory size is a whole number of.
const PAGE_SIZE: u64 = 64 * 1024;

/// The most pages a 32-bit wasm memory can hold: 4 GiB.
pub const MAX_PAGES: u64 = 1 << 16;

/// A validated `Duck.toml`. It has a component, a library, or both.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    pub component: Option<Component>,
    pub library: Option<Library>,
    /// The directory whose source files are the test modules of the
    /// package, relative to the manifest: [`DEFAULT_TEST_DIR`] where none is
    /// named. `None` where none is named and that one is in the directory
    /// of an entry, whose files are modules of the package already.
    pub tests: Option<PathBuf>,
    /// Each package this one can use, by the name it uses it as.
    pub dependencies: BTreeMap<String, Dependency>,
}

/// The WebAssembly component a package builds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Component {
    /// The file the component is compiled from, relative to the manifest.
    pub entry: PathBuf,
    /// Where the component is written, relative to the manifest.
    pub output: PathBuf,
    /// The function that the `run` of `wasi:cli/run` calls, which is the
    /// program.
    pub start: Option<String>,
    /// The world the component is one of: [`COMMAND`] where none is named.
    pub world: String,
    /// The most pages memory may grow to. `None` lets it grow without
    /// limit.
    pub max_pages: Option<u64>,
    /// The address literals are placed from.
    pub static_start: u64,
    /// The bytes of the return area, which holds what a function passes
    /// the host in memory. `None` is as many as the most that one passes.
    pub return_area: Option<u32>,
    /// The fuel that the code run to evaluate the constants of one item
    /// has. `None` is the compiler's own.
    pub fuel: Option<u64>,
}

/// What a package offers the packages that depend on it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Library {
    /// The file other packages use, relative to the manifest.
    pub entry: PathBuf,
    /// The fuel that the code run to evaluate the constants of one item
    /// has, where the library is checked on its own. `None` is the
    /// compiler's own.
    pub fuel: Option<u64>,
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
    /// A `min` for memory, which starts as the constants leave it.
    Min,
    /// A `memory64`, which no component's memory is.
    Memory64,
    /// An `end` for the literals, which end where the last is placed.
    StaticEnd,
    /// Neither a `[component]` nor a `[library]`.
    Empty,
    /// A `[memory]` without a `[component]` to give it to.
    MemoryWithoutComponent,
    /// A test directory that is in the directory of an entry, or that
    /// `holds` it: a file of both would be a module of the package twice.
    TestDir {
        dir: PathBuf,
        entry: PathBuf,
        holds: bool,
    },
    /// A dependency named something that can't be used.
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
    /// More than memory holds.
    TooLarge,
    /// As much as memory holds, which is past every address in it.
    NotAnAddress,
}

/// `Duck.toml` as written, before sizes are checked.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Raw {
    component: Option<RawComponent>,
    memory: Option<RawMemory>,
    library: Option<RawLibrary>,
    #[serde(default, rename = "const")]
    constants: RawConstants,
    #[serde(default)]
    test: RawTest,
    #[serde(default)]
    dependencies: BTreeMap<String, RawDependency>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawComponent {
    entry: PathBuf,
    output: PathBuf,
    start: Option<String>,
    world: Option<String>,
}

#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawMemory {
    /// Only read to be refused.
    memory64: Option<bool>,
    /// Only read to be refused.
    min: Option<String>,
    max: Option<String>,
    #[serde(rename = "static")]
    literals: Option<RawStatic>,
    #[serde(rename = "return")]
    return_area: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawStatic {
    start: String,
    /// Only read to be refused.
    end: Option<String>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RawLibrary {
    entry: PathBuf,
}

#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawConstants {
    fuel: Option<u64>,
}

#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct RawTest {
    dir: Option<PathBuf>,
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
        let fuel = raw.constants.fuel;
        let component = match (raw.component, raw.memory) {
            (Some(component), memory) => {
                let component = Component::parse(component, memory.unwrap_or_default())?;
                Some(Component { fuel, ..component })
            }
            (None, Some(_)) => return Err(ManifestError::MemoryWithoutComponent),
            (None, None) => None,
        };
        let library = raw.library.map(|library| Library {
            entry: library.entry,
            fuel,
        });
        if component.is_none() && library.is_none() {
            return Err(ManifestError::Empty);
        }
        let entries = [
            component.as_ref().map(|component| &component.entry),
            library.as_ref().map(|library| &library.entry),
        ];
        let tests = test_dir(raw.test.dir, entries.into_iter().flatten())?;
        let mut dependencies = BTreeMap::new();
        for (name, dependency) in raw.dependencies {
            if !lex::is_identifier(&name) {
                return Err(ManifestError::DependencyName(name));
            }
            let dependency = dependency.validate(&name)?;
            dependencies.insert(name, dependency);
        }
        Ok(Self {
            component,
            library,
            tests,
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

impl Component {
    /// How the component is compiled, with `wit` as the WIT of its package.
    pub fn settings(&self, wit: Wit) -> Settings {
        Settings {
            max_pages: self.max_pages,
            static_start: self.static_start,
            start: self.start.clone(),
            fuel: self.fuel,
            world: Some(self.world.clone()),
            wit,
            return_area: self.return_area,
        }
    }

    fn parse(component: RawComponent, memory: RawMemory) -> Result<Self, ManifestError> {
        let RawMemory {
            memory64,
            min,
            max,
            literals,
            return_area,
        } = memory;
        if min.is_some() {
            return Err(ManifestError::Min);
        }
        if memory64.is_some() {
            return Err(ManifestError::Memory64);
        }
        let max_pages = max
            .as_deref()
            .map(|max| pages("memory.max", max))
            .transpose()?;
        let static_start = match literals {
            Some(RawStatic { end: Some(_), .. }) => return Err(ManifestError::StaticEnd),
            Some(RawStatic { start, end: None }) => address("memory.static.start", &start)?,
            None => 0,
        };
        let return_area = return_area
            .as_deref()
            .map(|size| {
                let bytes = bytes("memory.return", size)?;
                let kind = SizeErrorKind::TooLarge;
                u32::try_from(bytes).map_err(|_| size_error("memory.return", size, kind))
            })
            .transpose()?;
        Ok(Self {
            entry: component.entry,
            output: component.output,
            start: component.start,
            world: component.world.unwrap_or_else(|| COMMAND.to_string()),
            max_pages,
            static_start,
            return_area,
            fuel: None,
        })
    }
}

impl Library {
    /// How the library is checked on its own: with room for any data, as
    /// the memory is that of whichever component it is built into, and as
    /// a component of no world, with `wit` as the WIT of its package.
    pub fn settings(&self, wit: Wit) -> Settings {
        Settings {
            max_pages: None,
            static_start: 0,
            start: None,
            fuel: self.fuel,
            world: None,
            wit,
            return_area: None,
        }
    }
}

/// The test directory of a package that names `dir` as it, or none, and
/// is entered by `entries`: `dir`, or [`DEFAULT_TEST_DIR`]. Neither it nor
/// the directory of an entry holds the other, as the paths are written:
/// one that is named so is an error, and the default is then none.
fn test_dir<'e>(
    dir: Option<PathBuf>,
    entries: impl Iterator<Item = &'e PathBuf>,
) -> Result<Option<PathBuf>, ManifestError> {
    let named = dir.is_some();
    let dir = dir.unwrap_or_else(|| DEFAULT_TEST_DIR.into());
    for entry in entries {
        let modules = entry.parent().unwrap_or(Path::new(""));
        let inside = within(&dir, modules);
        let holds = !inside && within(modules, &dir);
        if !inside && !holds {
            continue;
        }
        let entry = entry.clone();
        return match named {
            true => Err(ManifestError::TestDir { dir, entry, holds }),
            false => Ok(None),
        };
    }
    Ok(Some(dir))
}

/// Whether the directory `inner` is `outer` or under it, as the two are
/// written: each from the same directory, or from the root of the file
/// system.
fn within(inner: &Path, outer: &Path) -> bool {
    let (inner, outer) = (parts(inner), parts(outer));
    let rest = inner.strip_prefix(&outer[..]);
    rest.is_some_and(|rest| !rest.contains(&Part::ParentDir))
}

/// The names that lead to `path`, without those that lead nowhere: a `.`,
/// and a name with the `..` that leaves it.
fn parts(path: &Path) -> Vec<Part<'_>> {
    let mut parts = Vec::new();
    for part in path.components() {
        match (part, parts.last()) {
            (Part::CurDir, _) => {}
            (Part::ParentDir, Some(Part::Normal(_))) => {
                parts.pop();
            }
            _ => parts.push(part),
        }
    }
    parts
}

/// Where the manifest `src` writes the key that `keys` lead to, each the
/// name of a table of the one before, with the value it is given: of a
/// table that heads lines of its own, the heading. The nearest table that
/// is written, where the rest of them isn't, and `None` where none of them
/// is, or `src` is no TOML.
pub fn locate(src: &str, keys: &[&str]) -> Option<Range<usize>> {
    let document = DeTable::parse(src).ok()?;
    let mut table = Some(document.get_ref());
    let mut written = None;
    for key in keys {
        let Some((name, value)) = table.and_then(|table| table.get_key_value(*key)) else {
            break;
        };
        let (name, given) = (name.span(), value.span());
        written = Some(name.start.min(given.start)..name.end.max(given.end));
        table = value.get_ref().as_table();
    }
    written
}

/// The number of wasm pages in `value`, a size such as `64KiB` or `2pgs`.
fn pages(key: &'static str, value: &str) -> Result<u64, ManifestError> {
    let bytes = bytes(key, value)?;
    if bytes % u128::from(PAGE_SIZE) != 0 {
        return Err(size_error(key, value, SizeErrorKind::NotPageMultiple));
    }
    Ok((bytes / u128::from(PAGE_SIZE)) as u64)
}

/// The address `value`, a size such as `1024B` or `4KiB` from the start of
/// memory.
fn address(key: &'static str, value: &str) -> Result<u64, ManifestError> {
    let bytes = bytes(key, value)?;
    if bytes == max_bytes() {
        let kind = SizeErrorKind::NotAnAddress;
        return Err(size_error(key, value, kind));
    }
    Ok(bytes as u64)
}

/// The most bytes memory can hold: 4 GiB.
fn max_bytes() -> u128 {
    u128::from(MAX_PAGES) * u128::from(PAGE_SIZE)
}

/// The number of bytes in `value`, a size such as `64KiB` or `2pgs`, which
/// is at most what memory can hold.
fn bytes(key: &'static str, value: &str) -> Result<u128, ManifestError> {
    let error = |kind| size_error(key, value, kind);
    let digits = value.find(|c: char| !c.is_ascii_digit()).unwrap_or(0);
    let (number, unit) = value.split_at(digits);
    let unit_size: u64 = match unit {
        "B" => 1,
        "KiB" => 1 << 10,
        "MiB" => 1 << 20,
        "GiB" => 1 << 30,
        "TiB" => 1 << 40,
        "pgs" => PAGE_SIZE,
        _ => return Err(error(SizeErrorKind::Malformed)),
    };
    if number.is_empty() {
        return Err(error(SizeErrorKind::Malformed));
    }
    // Only digits are left, so the number can fail to parse only by overflowing.
    let bytes = number.parse::<u64>().ok();
    bytes
        .map(|number| u128::from(number) * u128::from(unit_size))
        .filter(|bytes| *bytes <= max_bytes())
        .ok_or(error(SizeErrorKind::TooLarge))
}

fn size_error(key: &'static str, value: &str, kind: SizeErrorKind) -> ManifestError {
    ManifestError::Size {
        key,
        value: value.to_string(),
        kind,
    }
}

impl ManifestError {
    /// The key of the manifest that the error is about: the tables that
    /// lead to it, and then its name. `None` for one that TOML places
    /// itself, and for a manifest that lacks what it needs, which is about
    /// no key of it.
    pub fn key(&self) -> Option<Vec<&str>> {
        Some(match self {
            Self::Toml(_) | Self::Empty => return None,
            Self::Size { key, .. } => key.split('.').collect(),
            Self::Min => vec!["memory", "min"],
            Self::Memory64 => vec!["memory", "memory64"],
            Self::StaticEnd => vec!["memory", "static", "end"],
            Self::MemoryWithoutComponent => vec!["memory"],
            Self::TestDir { .. } => vec![TEST, DIR],
            Self::DependencyName(name)
            | Self::NoSource(name)
            | Self::GitRef(name)
            | Self::RefWithoutGit(name) => vec![DEPENDENCIES, name],
            Self::Branch(name) => vec![DEPENDENCIES, name, "branch"],
        })
    }
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Toml(e) => write!(f, "{}", e.to_string().trim_end()),
            Self::Size { key, value, kind } => write!(f, "{key} \"{value}\" {kind}"),
            Self::Min => write!(
                f,
                "memory has no `min`: it starts with the pages its constants leave it, \
                 so call `module.grow` in one for more"
            ),
            Self::StaticEnd => write!(
                f,
                "memory.static has no `end`: literals end where the last is placed"
            ),
            Self::Memory64 => write!(
                f,
                "memory has no `memory64`: a component addresses it with 32 bits"
            ),
            Self::Empty => write!(f, "needs a [component] or [library] table"),
            Self::MemoryWithoutComponent => write!(f, "[memory] needs a [component] table"),
            Self::TestDir {
                dir,
                entry,
                holds: false,
            } => write!(
                f,
                "the test directory `{}` is in the directory of the entry `{}`, whose files \
                 are modules of the package already",
                dir.display(),
                entry.display()
            ),
            Self::TestDir {
                dir,
                entry,
                holds: true,
            } => write!(
                f,
                "the test directory `{}` holds the entry `{}`, which is no test module",
                dir.display(),
                entry.display()
            ),
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
                write!(
                    f,
                    "is not a number followed by B, KiB, MiB, GiB, TiB, or pgs"
                )
            }
            Self::NotPageMultiple => write!(f, "is not a multiple of 64KiB"),
            Self::TooLarge => write!(f, "exceeds 4GiB, which is all a component addresses"),
            Self::NotAnAddress => write!(f, "is not below 4GiB"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A component whose `[memory]` is `memory`.
    fn with_memory(memory: &str) -> Result<Manifest, ManifestError> {
        Manifest::parse(&format!(
            "[component]\nentry = \"src/main.duck\"\noutput = \"build/out.wasm\"\n\n[memory]\n{memory}"
        ))
    }

    fn size(value: &str) -> Result<u64, String> {
        pages("memory.max", value).map_err(|e| e.to_string())
    }

    #[test]
    fn a_key_is_where_the_manifest_writes_it() {
        let src = "[component]\nentry = \"main.duck\"\noutput = \"o.wasm\"\n[memory]\nmax = \"1KiB\"\n[memory.static]\nstart = \"4KiB\"\n[dependencies]\nutil = { path = \"../util\" }\n[dependencies.far]\ngit = \"url\"\n";
        let written = |keys: &[&str]| locate(src, keys).map(|written| &src[written]);
        assert_eq!(
            written(&["component", "entry"]),
            Some("entry = \"main.duck\"")
        );
        assert_eq!(
            written(&["memory", "static", "start"]),
            Some("start = \"4KiB\"")
        );
        assert_eq!(
            written(&["dependencies", "util"]),
            Some("util = { path = \"../util\" }")
        );
        assert_eq!(
            written(&["dependencies", "util", "path"]),
            Some("path = \"../util\"")
        );
        // A table that heads lines of its own is its heading.
        assert_eq!(written(&["memory"]), Some("[memory]"));
        assert_eq!(
            written(&["dependencies", "far"]),
            Some("[dependencies.far]")
        );
        // The nearest table that is written, where the rest isn't.
        assert_eq!(written(&["memory", "min"]), Some("[memory]"));
        assert_eq!(
            written(&["dependencies", "util", "tag"]),
            written(&["dependencies", "util"])
        );
        assert_eq!(written(&["library", "entry"]), None);
        assert_eq!(written(&[]), None);
        assert_eq!(locate("[component", &["component"]), None);

        // An error is about the key that it names.
        let key = |src: &str| {
            let error = Manifest::parse(src).unwrap_err();
            let key = error.key()?.into_iter().map(str::to_string);
            Some(key.collect::<Vec<_>>().join("."))
        };
        assert_eq!(
            key("[component]\nentry = \"a\"\noutput = \"b\"\n[memory]\nmax = \"1\"\n"),
            Some("memory.max".to_string())
        );
        assert_eq!(
            key("[library]\nentry = \"a\"\n[dependencies]\nutil = {}\n"),
            Some("dependencies.util".to_string())
        );
        assert_eq!(key("[dependencies]\n"), None);
        assert_eq!(key("[library]\n"), None);
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
        let address = |value| address("memory.static.start", value).map_err(|e| e.to_string());
        assert_eq!(address("0B"), Ok(0));
        assert_eq!(address("1025B"), Ok(1025));
        assert_eq!(address("4KiB"), Ok(4096));
        assert_eq!(address("4294967295B"), Ok(u32::MAX.into()));
        assert_eq!(
            address("4GiB"),
            Err("memory.static.start \"4GiB\" is not below 4GiB".to_string())
        );
        assert_eq!(
            address("5GiB"),
            Err(
                "memory.static.start \"5GiB\" exceeds 4GiB, which is all a component addresses"
                    .to_string()
            )
        );
    }

    #[test]
    fn memory_is_addressed_with_32_bits() {
        let module = |memory: &str| with_memory(memory).map(|manifest| manifest.component.unwrap());
        assert_eq!(
            module("max = \"4GiB\"\n").unwrap().max_pages,
            Some(MAX_PAGES)
        );
        assert_eq!(
            module("max = \"8GiB\"\n").unwrap_err().to_string(),
            "memory.max \"8GiB\" exceeds 4GiB, which is all a component addresses"
        );
        for memory in ["memory64 = true\n", "memory64 = false\n"] {
            assert_eq!(
                module(memory).unwrap_err().to_string(),
                "memory has no `memory64`: a component addresses it with 32 bits"
            );
        }
    }

    #[test]
    fn size_errors() {
        let malformed = "is not a number followed by B, KiB, MiB, GiB, TiB, or pgs";
        for value in [
            "", "64", "KiB", "64 KiB", "64kib", "64KB", "1pg", "-1pgs", "1.5MiB", "B", "8b",
        ] {
            assert_eq!(
                size(value),
                Err(format!("memory.max \"{value}\" {malformed}")),
                "{value:?}"
            );
        }
        assert_eq!(
            size("100KiB"),
            Err("memory.max \"100KiB\" is not a multiple of 64KiB".to_string())
        );
        for value in [
            "65537pgs",
            "1TiB",
            "18446744073709551615GiB",
            "99999999999999999999pgs",
        ] {
            assert_eq!(
                size(value),
                Err(format!(
                    "memory.max \"{value}\" exceeds 4GiB, which is all a component addresses"
                )),
                "{value:?}"
            );
        }
    }

    #[test]
    fn parses() {
        let manifest = with_memory("max = \"16MiB\"\nstatic = { start = \"1025B\" }\n").unwrap();
        assert_eq!(
            manifest,
            Manifest {
                component: Some(Component {
                    entry: "src/main.duck".into(),
                    output: "build/out.wasm".into(),
                    start: None,
                    world: COMMAND.to_string(),
                    max_pages: Some(256),
                    static_start: 1025,
                    return_area: None,
                    fuel: None,
                }),
                library: None,
                tests: Some("tests".into()),
                dependencies: BTreeMap::new(),
            }
        );
        let manifest = with_memory("static.start = \"1KiB\"\n").unwrap();
        let module = manifest.component.unwrap();
        assert_eq!((module.max_pages, module.static_start), (None, 1024));
        let manifest = Manifest::parse(
            "[component]\nentry = \"a.duck\"\noutput = \"a.wasm\"\nstart = \"init\"\n\n[memory]\nmax = \"1pgs\"\n",
        )
        .unwrap();
        assert_eq!(manifest.component.unwrap().start.as_deref(), Some("init"));
    }

    #[test]
    fn the_return_area_is_as_large_as_it_is_said_to_be() {
        let area = |memory: &str| {
            with_memory(memory).map(|manifest| manifest.component.unwrap().return_area)
        };
        assert_eq!(area("").unwrap(), None);
        assert_eq!(area("return = \"256B\"\n").unwrap(), Some(256));
        assert_eq!(area("return = \"1KiB\"\n").unwrap(), Some(1024));
        let settings = |memory: &str| {
            let component = with_memory(memory).unwrap().component.unwrap();
            component.settings(Wit::default()).return_area
        };
        assert_eq!(settings("return = \"0B\"\n"), Some(0));
        assert_eq!(settings("max = \"1pgs\"\n"), None);
        assert_eq!(
            area("return = \"256\"\n").unwrap_err().to_string(),
            "memory.return \"256\" is not a number followed by B, KiB, MiB, GiB, TiB, or pgs"
        );
        assert!(area("return = \"4GiB\"\n").is_err());
    }

    #[test]
    fn a_component_is_one_of_the_world_it_names() {
        let component = |world: &str| {
            let src = format!("[component]\nentry = \"a.duck\"\noutput = \"a.wasm\"\n{world}");
            Manifest::parse(&src).unwrap().component.unwrap()
        };
        // Without one it is a program, which `duck run` runs.
        assert_eq!(component("").world, "wasi:cli/command@0.3.0");
        let named = component("world = \"my:pkg/app\"\n");
        assert_eq!(named.world, "my:pkg/app");
        let settings = named.settings(Wit::default());
        assert_eq!(settings.world.as_deref(), Some("my:pkg/app"));

        // A library is built into the components that use it.
        let library = Manifest::parse("[library]\nentry = \"lib.duck\"\n").unwrap();
        let settings = library.library.unwrap().settings(Wit::default());
        assert_eq!(settings.world, None);
    }

    #[test]
    fn fuel_is_given_to_the_component_and_the_library() {
        let src = "[component]\nentry = \"a.duck\"\noutput = \"a.wasm\"\n\n\
                   [library]\nentry = \"lib.duck\"\n\n[const]\nfuel = 5000\n";
        let manifest = Manifest::parse(src).unwrap();
        assert_eq!(
            manifest.component.unwrap().settings(Wit::default()).fuel,
            Some(5000)
        );
        assert_eq!(
            manifest.library.unwrap().settings(Wit::default()).fuel,
            Some(5000)
        );

        let unset = Manifest::parse("[library]\nentry = \"lib.duck\"\n").unwrap();
        assert_eq!(unset.library.unwrap().settings(Wit::default()).fuel, None);
        let error = |src: &str| Manifest::parse(src).unwrap_err().to_string();
        let library = "[library]\nentry = \"lib.duck\"\n\n[const]\n";
        assert!(error(&format!("{library}fuel = -1\n")).contains("fuel"));
        assert!(error(&format!("{library}time = 1\n")).contains("unknown field `time`"));
    }

    #[test]
    fn tests_are_in_the_directory_that_is_named() {
        let tests = |src: &str| Manifest::parse(src).map(|manifest| manifest.tests);
        let component = "[component]\nentry = \"src/main.duck\"\noutput = \"a.wasm\"\n";
        let library = "[library]\nentry = \"lib/lib.duck\"\n";
        let named = |manifest: &str, dir: &str| {
            let src = format!("{manifest}[test]\ndir = \"{dir}\"\n");
            tests(&src).map_err(|e| e.to_string())
        };
        // In `tests` beside the manifest, where none is.
        for table in ["", "[test]\n"] {
            let src = format!("{component}{table}");
            assert_eq!(tests(&src).unwrap(), Some("tests".into()), "{table:?}");
        }
        assert_eq!(
            named(component, "checks/unit"),
            Ok(Some("checks/unit".into()))
        );
        assert_eq!(named(component, "../checks"), Ok(Some("../checks".into())));
        assert_eq!(
            named(component, "src/../checks"),
            Ok(Some("src/../checks".into()))
        );
        assert_eq!(
            named(library, "/abs/checks"),
            Ok(Some("/abs/checks".into()))
        );

        // A file of the directory of an entry is a module of the package
        // already, wherever under it the file is and however it is named.
        let inside = |dir: &str, entry: &str| {
            Err(format!(
                "the test directory `{dir}` is in the directory of the entry `{entry}`, whose \
                 files are modules of the package already"
            ))
        };
        for dir in ["src", "src/tests", "./src/deep/../tests", "tests/../src"] {
            assert_eq!(named(component, dir), inside(dir, "src/main.duck"), "{dir}");
        }
        let both = format!("{component}{library}");
        assert_eq!(
            named(&both, "lib/tests"),
            inside("lib/tests", "lib/lib.duck")
        );
        // And the entry is no test module.
        let holds = |dir: &str, entry: &str| {
            Err(format!(
                "the test directory `{dir}` holds the entry `{entry}`, which is no test module"
            ))
        };
        assert_eq!(named(component, "."), holds(".", "src/main.duck"));
        assert_eq!(named(library, "lib/.."), holds("lib/..", "lib/lib.duck"));
        let deep = "[library]\nentry = \"tests/unit/lib.duck\"\n";
        assert_eq!(named(deep, "tests"), holds("tests", "tests/unit/lib.duck"));

        // A package whose entry is beside its manifest has every directory
        // of its own under that one, so it has no tests unless it names a
        // directory elsewhere.
        let beside = "[library]\nentry = \"lib.duck\"\n";
        assert_eq!(tests(beside).unwrap(), None);
        assert_eq!(named(beside, "tests"), inside("tests", "lib.duck"));
        assert_eq!(named(beside, "../tests"), Ok(Some("../tests".into())));
        assert_eq!(tests(deep).unwrap(), None);

        // The error is about the key that names the directory.
        let error = Manifest::parse(&format!("{beside}[test]\ndir = \"tests\"\n")).unwrap_err();
        assert_eq!(error.key(), Some(vec!["test", "dir"]));
        let error = |test: &str| Manifest::parse(&format!("{component}{test}")).unwrap_err();
        let unknown = error("[test]\ndirectory = \"tests\"\n").to_string();
        assert!(unknown.contains("unknown field `directory`"), "{unknown}");
        assert!(
            error("[test]\ndir = 1\n")
                .to_string()
                .contains("invalid type")
        );
        assert!(
            error("[tests]\n")
                .to_string()
                .contains("unknown field `tests`")
        );
    }

    #[test]
    fn memory_is_optional() {
        let module = |memory: &str| {
            let src = format!("[component]\nentry = \"a.duck\"\noutput = \"a.wasm\"\n{memory}");
            Manifest::parse(&src).unwrap().component.unwrap()
        };
        for memory in ["", "[memory]\n"] {
            let module = module(memory);
            assert_eq!(module.max_pages, None, "{memory:?}");
            assert_eq!(module.static_start, 0, "{memory:?}");
        }
        let module = module("[memory]\nmax = \"2pgs\"\n");
        assert_eq!(module.max_pages, Some(2));
        assert_eq!(module.settings(Wit::default()).max_pages, Some(2));
        assert_eq!(module.settings(Wit::default()).static_start, 0);
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
                component: None,
                library: Some(Library {
                    entry: "src/lib.duck".into(),
                    fuel: None,
                }),
                tests: Some("tests".into()),
                dependencies: BTreeMap::from([
                    ("math".to_string(), Dependency::Path("../math".into())),
                    ("util".to_string(), Dependency::Path("/abs/util".into())),
                ]),
            }
        );
        let both = Manifest::parse(
            "[component]\nentry = \"a.duck\"\noutput = \"a.wasm\"\n[memory]\nmax = \"1pgs\"\n[library]\nentry = \"lib.duck\"\n",
        )
        .unwrap();
        assert!(both.component.is_some() && both.library.is_some());
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
        assert_eq!(error(""), "needs a [component] or [library] table");
        assert_eq!(
            error("[library]\nentry = \"a.duck\"\n[memory]\nmax = \"1pgs\"\n"),
            "[memory] needs a [component] table"
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
        assert!(error("max_pages = \"1pgs\"\n").contains("unknown field `max_pages`"));
        assert!(error("max = 1\n").contains("invalid type"));
        // Memory starts with what the constants leave it, and no more.
        assert_eq!(
            error("min = \"1pgs\"\nmax = \"1MiB\"\n"),
            "memory has no `min`: it starts with the pages its constants leave it, \
             so call `module.grow` in one for more"
        );
    }

    #[test]
    fn static_errors() {
        let error = |memory| with_memory(memory).unwrap_err().to_string();
        assert_eq!(
            error("static = { start = \"1kb\" }\n"),
            "memory.static.start \"1kb\" is not a number followed by B, KiB, MiB, GiB, TiB, or pgs"
        );
        assert!(error("static = {}\n").contains("missing field `start`"));
        assert!(
            error("static = { start = \"0B\", size = \"1B\" }\n").contains("unknown field `size`")
        );
        // Literals end where the last is placed.
        assert_eq!(
            error("static = { start = \"0B\", end = \"64KiB\" }\n"),
            "memory.static has no `end`: literals end where the last is placed"
        );
    }
}

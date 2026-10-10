//! The WIT a component is made of: the world that says what it imports and
//! exports, and the packages that world is written in.
//!
//! WASI 0.3 is always among the packages. A package adds its own, and those
//! they use, in [`Settings::wit`].

use std::fmt;
use std::sync::LazyLock;

use wit_component::{ComponentEncoder, StringEncoding};
use wit_parser::{PackageId, Resolve, SourceMap, UnresolvedPackageGroup, WorldId, WorldItem};

use crate::file::{Settings, WitFile};

/// The world a component is made of where its package names none.
pub const COMMAND: &str = "wasi:cli/command@0.3.0";

/// The interface whose `run` is a program: a world that exports it is one
/// that `duck run` runs.
pub const RUN_INTERFACE: &str = "wasi:cli/run@0.3.0";

/// The name a module exports the `run` of [`RUN_INTERFACE`] as.
pub const RUN_EXPORT: &str = "wasi:cli/run@0.3.0#run";

/// The module a core module imports the functions of the world itself
/// from, which no interface has.
pub const ROOT: &str = "$root";

/// The function that allocates what the host passes in memory, which a
/// module exports by this name and no other.
pub const REALLOC: &str = "cabi_realloc";

/// The WIT of WASI 0.3 as Wasmtime implements it, each package after those
/// it uses. The packages are copied from `src/p3/wit/deps` of the
/// `wasmtime-wasi` that `duck run` depends on, and change when it does.
const WASI: [(&str, &str); 5] = [
    ("wasi/clocks.wit", include_str!("../wit/clocks.wit")),
    ("wasi/random.wit", include_str!("../wit/random.wit")),
    ("wasi/filesystem.wit", include_str!("../wit/filesystem.wit")),
    ("wasi/sockets.wit", include_str!("../wit/sockets.wit")),
    ("wasi/cli.wit", include_str!("../wit/cli.wit")),
];

/// Why there is no world to make a component of.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WorldError {
    /// The package's WIT doesn't parse, or uses what no package has.
    Wit(String),
    /// The WIT has no such world.
    Missing { world: String, error: String },
    /// A library, which is built into the components that use it.
    Library,
    /// Memory addressed with 64 bits, as no component's is.
    Memory64,
    /// A start function, which only the `run` of [`RUN_INTERFACE`] calls,
    /// in a world that doesn't export it.
    Start { world: String },
}

/// The packages a component's WIT is written in, and the world of them
/// that it is made of.
#[derive(Debug, Clone)]
pub struct World {
    resolve: Resolve,
    /// `None` for a library, which is checked as a component of no world.
    world: Option<WorldId>,
    /// The world as [`Settings::world`] names it.
    name: Option<String>,
}

/// What a world exports, which a component of it defines.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Exports {
    /// The functions of the world itself, by name.
    pub functions: Vec<String>,
    pub interfaces: Vec<InterfaceExport>,
}

/// An interface a world exports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InterfaceExport {
    /// Its name in full, as in `wasi:cli/run@0.3.0`.
    pub name: String,
    /// Its functions, by the name a module exports each as after the
    /// interface's and a `#`.
    pub functions: Vec<String>,
}

/// WASI 0.3, resolved once, and the package of it that has
/// [`COMMAND`].
static BASE: LazyLock<(Resolve, PackageId)> = LazyLock::new(|| {
    let mut resolve = Resolve::default();
    let mut main = None;
    for (path, contents) in WASI {
        main = Some(resolve.push_str(path, contents).expect("WASI is valid"));
    }
    (resolve, main.expect("WASI has packages"))
});

impl fmt::Display for WorldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wit(e) => write!(f, "cannot read the WIT of the package: {e}"),
            Self::Missing { world, error } => write!(f, "no world `{world}`: {error}"),
            Self::Library => write!(f, "a library is no component: it has no world"),
            Self::Memory64 => write!(
                f,
                "`memory64` builds no component: one addresses memory with 32 bits"
            ),
            Self::Start { world } => write!(
                f,
                "`start` needs a world that exports `{RUN_INTERFACE}`, whose `run` calls it: \
                 `{world}` doesn't"
            ),
        }
    }
}

impl std::error::Error for WorldError {}

/// The world of a library: none, with WASI 0.3 as its only WIT.
impl Default for World {
    fn default() -> Self {
        Self {
            resolve: BASE.0.clone(),
            world: None,
            name: None,
        }
    }
}

impl World {
    /// Reads the WIT of `settings`, after that of WASI 0.3, and finds the
    /// world it names.
    pub fn load(settings: &Settings) -> Result<Self, WorldError> {
        let (mut resolve, mut main) = BASE.clone();
        if !settings.wit.package.is_empty() {
            let package = group(&settings.wit.package)?;
            let deps = settings.wit.deps.iter().map(|dep| group(dep));
            let deps = deps.collect::<Result<_, _>>()?;
            let pushed = resolve.push_groups(package, deps);
            // Where in the WIT the error is, which only the files it has
            // read say.
            let located = |e: wit_parser::ResolveError| e.render(&resolve.source_map);
            main = pushed.map_err(|e| WorldError::Wit(located(e)))?;
        }
        let world = match &settings.world {
            Some(name) => {
                let found = resolve.select_world(&[main], Some(name));
                Some(found.map_err(|e| WorldError::Missing {
                    world: name.clone(),
                    error: format!("{e:#}"),
                })?)
            }
            None => None,
        };
        Ok(Self {
            resolve,
            world,
            name: settings.world.clone(),
        })
    }

    /// Whether there is no world, as there is none for a library.
    pub fn is_library(&self) -> bool {
        self.world.is_none()
    }

    /// What the world exports. A library has no world to export anything.
    pub fn exports(&self) -> Exports {
        let mut exports = Exports::default();
        let Some(world) = self.world else {
            return exports;
        };
        for (key, item) in &self.resolve.worlds[world].exports {
            match item {
                WorldItem::Function(function) => exports.functions.push(function.name.clone()),
                WorldItem::Interface { id, .. } => {
                    let functions = self.resolve.interfaces[*id].functions.keys();
                    exports.interfaces.push(InterfaceExport {
                        name: self.resolve.name_world_key(key),
                        functions: functions.cloned().collect(),
                    });
                }
                WorldItem::Type { .. } => {}
            }
        }
        exports
    }

    /// Whether the world exports [`RUN_INTERFACE`], whose `run` is what
    /// calls a start function.
    pub fn exports_run(&self) -> bool {
        let exports = self.exports();
        exports.interfaces.iter().any(|i| i.name == RUN_INTERFACE)
    }

    /// Why a start function has nothing to call it, as it has in a world
    /// that doesn't export [`RUN_INTERFACE`].
    pub fn start_error(&self) -> WorldError {
        match &self.name {
            Some(world) => WorldError::Start {
                world: world.clone(),
            },
            None => WorldError::Library,
        }
    }

    /// Encodes `module`, a core module that imports and exports what the
    /// world has, as a component of it.
    pub fn encode(&self, mut module: Vec<u8>) -> Result<Vec<u8>, String> {
        let world = self.world.ok_or_else(|| WorldError::Library.to_string())?;
        let encoding = StringEncoding::UTF8;
        wit_component::embed_component_metadata(&mut module, &self.resolve, world, encoding)
            .and_then(|()| ComponentEncoder::default().module(&module)?.encode())
            .map_err(|e| {
                // The causes before the last two say only that the module
                // was read.
                let causes: Vec<_> = e.chain().map(ToString::to_string).collect();
                causes[causes.len().saturating_sub(2)..].join(": ")
            })
    }
}

/// The WIT package that `files` are, before it is resolved.
fn group(files: &[WitFile]) -> Result<UnresolvedPackageGroup, WorldError> {
    let mut map = SourceMap::new();
    for file in files {
        map.push_str(&file.path, file.contents.as_str());
    }
    let parsed = map.parse();
    parsed.map_err(|(map, e)| WorldError::Wit(e.render(&map)))
}

/// The name `name` has in WIT, where one is words of lowercase letters or of
/// capitals, joined by `-`: its own with each `_` a `-`. `None` if that is
/// no name there, as it isn't for one that starts or ends with a `_`, has
/// two together, or has a word of both cases.
pub fn kebab(name: &str) -> Option<String> {
    let word = |(index, word): (usize, &str)| {
        let mut chars = word.chars();
        let first = chars.next()?;
        // Only a word after the first starts with a digit.
        let lower = |c: char| c.is_ascii_lowercase() || c.is_ascii_digit();
        let upper = |c: char| c.is_ascii_uppercase() || c.is_ascii_digit();
        let letters = word.trim_start_matches(|c: char| c.is_ascii_digit() && index > 0);
        let cased = letters.chars().all(lower) || letters.chars().all(upper);
        (cased && (first.is_ascii_alphabetic() || index > 0)).then_some(())
    };
    let words = name.split('_').enumerate().map(word);
    words.collect::<Option<Vec<_>>>()?;
    Some(name.replace('_', "-"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_name_is_its_own_in_wit_with_hyphens() {
        let names = [
            ("tick", Some("tick")),
            ("get_stdout", Some("get-stdout")),
            ("parse_URL", Some("parse-URL")),
            ("utf8_len", Some("utf8-len")),
            ("to_2d", Some("to-2d")),
            ("LIMIT", Some("LIMIT")),
            ("_hidden", None),
            ("trailing_", None),
            ("two__under", None),
            ("getHttp", None),
            ("Point", None),
            ("größe", None),
            ("_", None),
        ];
        for (name, expected) in names {
            assert_eq!(kebab(name).as_deref(), expected, "{name}");
        }
    }

    #[test]
    fn a_world_exports_its_functions_and_those_of_its_interfaces() {
        let command = Settings {
            world: Some(COMMAND.to_string()),
            ..Settings::default()
        };
        let world = World::load(&command).unwrap();
        let run = InterfaceExport {
            name: RUN_INTERFACE.to_string(),
            functions: vec!["run".to_string()],
        };
        assert_eq!(world.exports().interfaces, [run]);
        assert!(world.exports().functions.is_empty());
        assert!(world.exports_run() && !world.is_library());

        let wit = "package my:pkg@0.1.0;\ninterface math {\n  add: func(a: s32, b: s32) -> s32;\n  \
                   neg: func(a: s32) -> s32;\n}\nworld app {\n  export math;\n  \
                   export tick-now: func();\n}\n";
        let settings = Settings {
            world: Some("app".to_string()),
            wit: crate::file::Wit {
                package: vec![WitFile {
                    path: "app.wit".to_string(),
                    contents: wit.to_string(),
                }],
                deps: Vec::new(),
            },
            ..Settings::default()
        };
        let exports = World::load(&settings).unwrap().exports();
        assert_eq!(exports.functions, ["tick-now"]);
        let math = InterfaceExport {
            name: "my:pkg/math@0.1.0".to_string(),
            functions: vec!["add".to_string(), "neg".to_string()],
        };
        assert_eq!(exports.interfaces, [math]);

        // A library has no world, so nothing is exported.
        let library = World::load(&Settings::default()).unwrap();
        assert!(library.is_library() && !library.exports_run());
        assert_eq!(library.exports(), Exports::default());
    }
}

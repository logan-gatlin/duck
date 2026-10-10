//! The WIT a component is made of: the world that says what it imports and
//! exports, and the packages that world is written in.
//!
//! WASI 0.3 is always among the packages. A package adds its own, and those
//! they use, in [`Settings::wit`].

use std::fmt;

use wit_component::{ComponentEncoder, StringEncoding};
use wit_parser::{Resolve, SourceMap, UnresolvedPackageGroup, WorldId, WorldKey};

use crate::file::{Settings, WitFile};

/// The world a component is made of where its package names none.
pub const COMMAND: &str = "wasi:cli/command@0.3.0";

/// The interface whose `run` is a program: a world that exports it is one
/// that `duck run` runs.
pub const RUN_INTERFACE: &str = "wasi:cli/run@0.3.0";

/// The name a module exports the `run` of [`RUN_INTERFACE`] as.
pub const RUN_EXPORT: &str = "wasi:cli/run@0.3.0#run";

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

impl World {
    /// Reads the WIT of `settings`, after that of WASI 0.3, and finds the
    /// world it names.
    pub fn load(settings: &Settings) -> Result<Self, WorldError> {
        let mut resolve = Resolve::default();
        let mut main = None;
        for (path, contents) in WASI {
            main = Some(resolve.push_str(path, contents).expect("WASI is valid"));
        }
        if !settings.wit.package.is_empty() {
            let package = group(&settings.wit.package)?;
            let deps = settings.wit.deps.iter().map(|dep| group(dep));
            let deps = deps.collect::<Result<_, _>>()?;
            let pushed = resolve.push_groups(package, deps);
            // Where in the WIT the error is, which only the files it has
            // read say.
            let located = |e: wit_parser::ResolveError| e.render(&resolve.source_map);
            main = Some(pushed.map_err(|e| WorldError::Wit(located(e)))?);
        }
        let main = main.expect("WASI has packages");
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

    /// Whether the world exports [`RUN_INTERFACE`], whose `run` is what
    /// calls a start function.
    pub fn exports_run(&self) -> bool {
        let Some(world) = self.world else {
            return false;
        };
        let exports = self.resolve.worlds[world].exports.keys();
        exports
            .filter_map(|key| match key {
                WorldKey::Interface(id) => self.resolve.id_of(*id),
                WorldKey::Name(_) => None,
            })
            .any(|id| id == RUN_INTERFACE)
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

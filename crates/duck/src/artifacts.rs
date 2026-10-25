//! What the packages a package uses compile to, kept from one build to the
//! next: the artifact of each, in a store under the cache directory, by a
//! hash of all that it is compiled from. A package whose source, settings
//! and dependencies are as they were when it was last compiled isn't
//! compiled again, by this build or by any other that uses it.

use std::cell::RefCell;
use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use duck_compiler::file::Settings;
use duck_compiler::ty::{ARTIFACT_VERSION, Artifact};

use crate::files::{self, Files, sources};
use crate::package::{Package, Packages};

/// Where artifacts are kept.
pub struct Store {
    /// `None` when the environment gives no place for one: nothing is
    /// kept, and every package is compiled.
    dir: Option<PathBuf>,
    /// Those read or written since the store was opened, by key: a language
    /// server reads the same ones for every check.
    memo: RefCell<HashMap<String, Rc<Artifact>>>,
}

/// Why the packages a package uses aren't all compiled.
pub enum Failed {
    /// A package that didn't compile: its files, which the errors are in,
    /// its errors, and its manifest, for an error in no file to be placed
    /// in.
    Compile {
        files: Box<Files>,
        errors: Vec<duck_compiler::Error>,
        manifest: PathBuf,
    },
    /// A file that couldn't be read.
    Read { path: PathBuf, error: io::Error },
}

/// What an artifact is kept as.
const EXTENSION: &str = "duckart";

/// What a key hashes first, which changes with the format of an artifact
/// and whenever what a package compiles to may.
const SALT: &str = "duck-artifact";

impl Store {
    pub fn new(dir: PathBuf) -> Self {
        Self {
            dir: Some(dir),
            memo: RefCell::new(HashMap::new()),
        }
    }

    /// The store under `$XDG_CACHE_HOME`, or else `$HOME/.cache`.
    pub fn from_env() -> Self {
        let xdg = std::env::var_os("XDG_CACHE_HOME").filter(|dir| !dir.is_empty());
        let base = xdg
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".cache")));
        Self {
            dir: base.map(|base| base.join("duck").join("artifacts")),
            memo: RefCell::new(HashMap::new()),
        }
    }

    /// A store that keeps nothing beyond what it is given while it is open.
    pub fn none() -> Self {
        Self {
            dir: None,
            memo: RefCell::new(HashMap::new()),
        }
    }

    fn path(&self, key: &str) -> Option<PathBuf> {
        let dir = self.dir.as_ref()?;
        Some(dir.join(format!("{key}.{EXTENSION}")))
    }

    /// The artifact kept by `key`, if one is and it reads as one.
    pub fn read(&self, key: &str) -> Option<Rc<Artifact>> {
        if let Some(artifact) = self.memo.borrow().get(key) {
            return Some(artifact.clone());
        }
        let bytes = fs::read(self.path(key)?).ok()?;
        let artifact = Rc::new(Artifact::decode(&bytes).ok()?);
        self.memo
            .borrow_mut()
            .insert(key.to_string(), artifact.clone());
        Some(artifact)
    }

    /// Keeps `artifact` by `key`. Nothing is kept on disk where it can't
    /// be, as the next build compiles the package again.
    pub fn write(&self, key: &str, artifact: &Artifact) {
        self.memo
            .borrow_mut()
            .insert(key.to_string(), Rc::new(artifact.clone()));
        let Some(path) = self.path(key) else {
            return;
        };
        let written = || -> io::Result<()> {
            if let Some(dir) = path.parent() {
                fs::create_dir_all(dir)?;
            }
            // Whole or not at all: another build may read it meanwhile.
            let partial = path.with_extension(format!("{EXTENSION}.{}", std::process::id()));
            fs::write(&partial, artifact.encode())?;
            fs::rename(partial, &path)
        };
        let _ = written();
    }
}

/// Compiles each package that the package at `built` of `packages` uses,
/// those it uses first, unless `store` has what it compiled to, which it
/// is given, and gives the files of the package at `built`, entered by
/// `entry`, with each of them: compiling those files then compiles nothing
/// of the other packages. A package that doesn't compile is given back
/// with its files, for its errors to be reported with.
pub fn prepare(
    packages: &Packages,
    built: usize,
    entry: &Path,
    settings: Settings,
    store: &Store,
) -> Result<Files, Failed> {
    let mut keys: HashMap<usize, String> = HashMap::new();
    let mut compiled: HashMap<usize, Rc<Artifact>> = HashMap::new();
    let mut order = Vec::new();
    depends_first(packages, built, &mut Vec::new(), &mut order);
    let read = |path: &Path, error: io::Error| Failed::Read {
        path: path.to_path_buf(),
        error,
    };
    for index in order {
        if index == built {
            break;
        }
        let package = packages
            .iter()
            .nth(index)
            .expect("the package is among them");
        let Some(library) = &package.manifest.library else {
            // A component is used by nothing: only the package that is
            // built is one.
            continue;
        };
        let key = key(package, &keys).map_err(|e| read(&package.dir, e))?;
        let artifact = match store.read(&key) {
            Some(artifact) => artifact,
            None => {
                let wit = files::wit_of(packages, index).unwrap_or_default();
                let library_entry = package.dir.join(&library.entry);
                let settings = library.settings(wit);
                // One whose library isn't there is left to the package that
                // uses it to report, where it uses it.
                let Ok(mut files) = Files::of(packages, index, &library_entry, settings) else {
                    continue;
                };
                for (used, key) in &keys {
                    files.with_compiled(*used, key.clone(), compiled.get(used).cloned());
                }
                // The artifact names its package as those that use it do.
                files.with_compiled(index, key.clone(), None);
                let artifact = duck_compiler::compile_package(&mut files);
                let artifact = artifact.map_err(|errors| Failed::Compile {
                    files: Box::new(files),
                    errors,
                    manifest: package.dir.join(crate::manifest::MANIFEST),
                })?;
                store.write(&key, &artifact);
                Rc::new(artifact)
            }
        };
        compiled.insert(index, artifact);
        keys.insert(index, key);
    }
    let mut files = Files::of(packages, built, entry, settings).map_err(|e| read(entry, e))?;
    for (used, key) in &keys {
        files.with_compiled(*used, key.clone(), compiled.get(used).cloned());
    }
    let own = packages
        .iter()
        .nth(built)
        .expect("the package is among them");
    if own.manifest.library.is_some() {
        let key = key(own, &keys).map_err(|e| read(&own.dir, e))?;
        files.with_compiled(built, key, None);
    }
    Ok(files)
}

/// What names what the package at `built` of `packages` compiles to, with
/// the packages it uses as `prepare` compiled them: see [`key`].
pub fn key_of(packages: &Packages, built: usize) -> io::Result<String> {
    let mut keys: HashMap<usize, String> = HashMap::new();
    let mut order = Vec::new();
    depends_first(packages, built, &mut Vec::new(), &mut order);
    for index in order {
        let package = packages
            .iter()
            .nth(index)
            .expect("the package is among them");
        let key = key(package, &keys)?;
        keys.insert(index, key);
    }
    Ok(keys.remove(&built).expect("the package is keyed"))
}

/// Adds the package at `index` to `order` after each it uses, which are
/// added first, unless it is there or is being added, as one that uses
/// itself through others is.
fn depends_first(
    packages: &Packages,
    index: usize,
    adding: &mut Vec<usize>,
    order: &mut Vec<usize>,
) {
    if order.contains(&index) || adding.contains(&index) {
        return;
    }
    adding.push(index);
    let package = packages
        .iter()
        .nth(index)
        .expect("the package is among them");
    for used in package.dependencies.values() {
        depends_first(packages, *used, adding, order);
    }
    adding.pop();
    order.push(index);
}

/// What names what `package` compiles to: a hash of the artifact format,
/// the compiler, every source file of the package, its WIT, what its
/// manifest says of compiling it, and the key of each package it uses,
/// which `keys` has by index. An error names a file that can't be read.
pub fn key(package: &Package, keys: &HashMap<usize, String>) -> io::Result<String> {
    let mut hash = Sha256::default();
    let mut feed = |bytes: &[u8]| {
        hash.update(&(bytes.len() as u64).to_le_bytes());
        hash.update(bytes);
    };
    feed(SALT.as_bytes());
    feed(&ARTIFACT_VERSION.to_le_bytes());
    feed(env!("CARGO_PKG_VERSION").as_bytes());
    let library = package.manifest.library.as_ref();
    let entry = library
        .map(|library| library.entry.clone())
        .unwrap_or_default();
    let root = package.dir.join(&entry);
    let root = root.parent().unwrap_or(&package.dir).to_path_buf();
    feed(entry.to_string_lossy().as_bytes());
    feed(
        &library
            .and_then(|library| library.fuel)
            .unwrap_or(0)
            .to_le_bytes(),
    );
    let mut paths = Vec::new();
    sources(&root, &mut paths)?;
    let tests = package
        .manifest
        .tests
        .as_ref()
        .map(|tests| package.dir.join(tests));
    for path in paths {
        if tests.as_ref().is_some_and(|tests| path.starts_with(tests)) {
            continue;
        }
        let name = path.strip_prefix(&root).unwrap_or(&path);
        feed(name.to_string_lossy().as_bytes());
        feed(&fs::read(&path)?);
    }
    let wit = files::wit_in(&package.dir)?;
    for file in wit.package.iter().chain(wit.deps.iter().flatten()) {
        feed(file.path.as_bytes());
        feed(file.contents.as_bytes());
    }
    for (name, used) in &package.dependencies {
        feed(name.as_bytes());
        feed(keys.get(used).map_or("", String::as_str).as_bytes());
    }
    Ok(hash.finish())
}

/// SHA-256, as FIPS 180-4 gives it: a key is to be the same on every
/// machine, and to tell one package from another however many there are.
struct Sha256 {
    state: [u32; 8],
    buffer: Vec<u8>,
    length: u64,
}

const ROUND: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

impl Default for Sha256 {
    fn default() -> Self {
        Self {
            state: [
                0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
                0x5be0cd19,
            ],
            buffer: Vec::new(),
            length: 0,
        }
    }
}

impl Sha256 {
    fn update(&mut self, bytes: &[u8]) {
        self.length += bytes.len() as u64;
        self.buffer.extend_from_slice(bytes);
        let blocks = self.buffer.len() / 64;
        for block in 0..blocks {
            let chunk: [u8; 64] = self.buffer[block * 64..block * 64 + 64].try_into().unwrap();
            self.block(&chunk);
        }
        self.buffer.drain(..blocks * 64);
    }

    fn block(&mut self, chunk: &[u8; 64]) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes(word.try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = self.state;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(ROUND[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (state, add) in self.state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *state = state.wrapping_add(add);
        }
    }

    /// The hash of all that was fed, as hexadecimal.
    fn finish(mut self) -> String {
        let bits = self.length * 8;
        let mut tail = vec![0x80u8];
        while (self.buffer.len() + tail.len()) % 64 != 56 {
            tail.push(0);
        }
        tail.extend_from_slice(&bits.to_be_bytes());
        self.length = 0;
        self.update(&tail);
        debug_assert!(self.buffer.is_empty());
        let mut hex = String::with_capacity(64);
        for word in self.state {
            hex.push_str(&format!("{word:08x}"));
        }
        hex
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_is_as_published() {
        let hash = |bytes: &[u8]| {
            let mut hash = Sha256::default();
            hash.update(bytes);
            hash.finish()
        };
        assert_eq!(
            hash(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            hash(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        let long = b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq";
        assert_eq!(
            hash(long),
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
        );
        // Fed in pieces, it is the same.
        let mut pieces = Sha256::default();
        pieces.update(&long[..10]);
        pieces.update(&long[10..]);
        assert_eq!(pieces.finish(), hash(long));
    }
}

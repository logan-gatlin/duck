//! `Duck.toml`, the metadata of a duck module.

use std::fmt;
use std::io;
use std::path::PathBuf;

use duck_compiler::file::MemoryLimits;
use serde::Deserialize;

/// The name of the manifest file at the root of every module.
pub const MANIFEST: &str = "Duck.toml";

/// The size of a wasm page, which every memory size is a whole number of.
const PAGE_SIZE: u64 = 64 * 1024;

/// The most pages a 32-bit wasm memory can hold: 4 GiB.
const MAX_PAGES: u64 = 1 << 16;

/// A validated `Duck.toml`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    /// The file the module is compiled from, relative to the manifest.
    pub entry: PathBuf,
    /// Where the wasm module is written, relative to the manifest.
    pub output: PathBuf,
    /// The function run when the module is instantiated.
    pub start: Option<String>,
    pub memory: MemoryLimits,
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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SizeErrorKind {
    /// Not a number followed by a unit.
    Malformed,
    NotPageMultiple,
    TooLarge,
}

/// `Duck.toml` as written, before sizes are checked.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Raw {
    module: RawModule,
    memory: RawMemory,
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
}

impl Manifest {
    pub fn parse(src: &str) -> Result<Self, ManifestError> {
        let raw: Raw = toml::from_str(src).map_err(ManifestError::Toml)?;
        let RawMemory { min, max } = raw.memory;
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
        Ok(Self {
            entry: raw.module.entry,
            output: raw.module.output,
            start: raw.module.start,
            memory: MemoryLimits {
                min_pages,
                max_pages,
            },
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

/// The number of wasm pages in `value`, a size such as `64KiB` or `2pgs`.
fn pages(key: &'static str, value: &str) -> Result<u32, ManifestError> {
    let error = |kind| ManifestError::Size {
        key,
        value: value.to_string(),
        kind,
    };
    let digits = value.find(|c: char| !c.is_ascii_digit()).unwrap_or(0);
    let (number, unit) = value.split_at(digits);
    let unit_size = match unit {
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
    if bytes % PAGE_SIZE != 0 {
        return Err(error(SizeErrorKind::NotPageMultiple));
    }
    let pages = bytes / PAGE_SIZE;
    if pages > MAX_PAGES {
        return Err(error(SizeErrorKind::TooLarge));
    }
    Ok(pages as u32)
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Toml(e) => write!(f, "{}", e.to_string().trim_end()),
            Self::Size { key, value, kind } => write!(f, "{key} \"{value}\" {kind}"),
            Self::MinExceedsMax { min, max } => {
                write!(f, "memory.min \"{min}\" exceeds memory.max \"{max}\"")
            }
        }
    }
}

impl std::error::Error for ManifestError {}

impl fmt::Display for SizeErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Malformed => {
                write!(f, "is not a number followed by KiB, MiB, GiB, or pgs")
            }
            Self::NotPageMultiple => write!(f, "is not a multiple of 64KiB"),
            Self::TooLarge => write!(f, "exceeds 4GiB"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with_memory(memory: &str) -> Result<Manifest, ManifestError> {
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
    }

    #[test]
    fn size_errors() {
        let malformed = "is not a number followed by KiB, MiB, GiB, or pgs";
        for value in [
            "", "64", "KiB", "64 KiB", "64kib", "64KB", "1pg", "-1pgs", "1.5MiB",
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
                entry: "src/main.duck".into(),
                output: "build/out.wasm".into(),
                start: None,
                memory: MemoryLimits {
                    min_pages: 1,
                    max_pages: Some(256),
                },
            }
        );
        let manifest = with_memory("min = \"64KiB\"\n").unwrap();
        assert_eq!(manifest.memory.max_pages, None);
        let manifest = Manifest::parse(
            "[module]\nentry = \"a.duck\"\noutput = \"a.wasm\"\nstart = \"init\"\n\n[memory]\nmin = \"1pgs\"\n",
        )
        .unwrap();
        assert_eq!(manifest.start.as_deref(), Some("init"));
    }

    #[test]
    fn errors() {
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
}

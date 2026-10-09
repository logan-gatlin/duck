//! Git dependencies, fetched by the `git` command into a cache that builds
//! read without the network once a commit is in it.
//!
//! The cache holds a bare repository per URL, which tags and commits are
//! resolved in, and a checkout per commit, which is never changed once made.
//! Tags are taken never to move, so one is only fetched when it's missing.

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::manifest::GitRef;

/// Where git dependencies are fetched to.
#[derive(Debug, Clone)]
pub struct Cache {
    /// `None` when the environment gives no place for one.
    dir: Option<PathBuf>,
}

#[derive(Debug)]
pub enum GitError {
    /// Neither `XDG_CACHE_HOME` nor `HOME` is set.
    NoCache,
    Io(io::Error),
    /// A `git` command that failed, and what it wrote to stderr.
    Command {
        command: String,
        stderr: String,
    },
    /// A tag or rev that names no commit of the repository.
    UnknownRef {
        url: String,
        reference: GitRef,
    },
}

impl fmt::Display for GitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoCache => write!(
                f,
                "no directory to fetch git dependencies to: set XDG_CACHE_HOME or HOME"
            ),
            Self::Io(e) => e.fmt(f),
            Self::Command { command, stderr } => write!(f, "`{command}` failed: {stderr}"),
            Self::UnknownRef { url, reference } => match reference {
                GitRef::Tag(tag) => write!(f, "{url} has no tag `{tag}`"),
                GitRef::Rev(rev) => write!(f, "{url} has no commit `{rev}`"),
            },
        }
    }
}

impl std::error::Error for GitError {}

impl From<io::Error> for GitError {
    fn from(e: io::Error) -> Self {
        Self::Io(e)
    }
}

impl Cache {
    pub fn new(dir: PathBuf) -> Self {
        Self { dir: Some(dir) }
    }

    /// The cache under `$XDG_CACHE_HOME`, or else `$HOME/.cache`.
    pub fn from_env() -> Self {
        let xdg = std::env::var_os("XDG_CACHE_HOME").filter(|dir| !dir.is_empty());
        let base = xdg
            .map(PathBuf::from)
            .or_else(|| std::env::var_os("HOME").map(|home| Path::new(&home).join(".cache")));
        match base {
            Some(base) => Self::new(base.join("duck").join("git")),
            None => Self { dir: None },
        }
    }

    /// Whether `path` is in the cache: a file of a dependency it fetched.
    pub fn holds(&self, path: &Path) -> bool {
        let dir = self.dir.as_ref();
        dir.is_some_and(|dir| {
            path.starts_with(dir) || fs::canonicalize(dir).is_ok_and(|dir| path.starts_with(dir))
        })
    }

    /// The commit `reference` names in the repository at `url`, and the
    /// directory holding it, fetching whatever the cache lacks.
    pub fn checkout(&self, url: &str, reference: &GitRef) -> Result<(String, PathBuf), GitError> {
        let dir = self.dir.as_ref().ok_or(GitError::NoCache)?;
        let key = key(url);
        let db = dir.join("db").join(&key);
        if !db.exists() {
            fs::create_dir_all(&db)?;
            git(&db, &["init", "--quiet", "--bare"])?;
        }
        let commit = match resolve(&db, reference) {
            Some(commit) => commit,
            None => {
                fetch(&db, url, reference)?;
                resolve(&db, reference).ok_or_else(|| GitError::UnknownRef {
                    url: url.to_string(),
                    reference: reference.clone(),
                })?
            }
        };
        let checkouts = dir.join("checkouts").join(&key);
        let checkout = checkouts.join(&commit);
        if !checkout.exists() {
            // Checked out aside and moved into place, so that a checkout
            // that exists is complete.
            let partial = checkouts.join(format!(".{commit}-{}", std::process::id()));
            let _ = fs::remove_dir_all(&partial);
            fs::create_dir_all(&checkouts)?;
            let db = db.to_string_lossy();
            let partial_str = partial.to_string_lossy();
            git(
                &checkouts,
                &[
                    "clone",
                    "--quiet",
                    "--shared",
                    "--no-checkout",
                    &db,
                    &partial_str,
                ],
            )?;
            git(&partial, &["checkout", "--quiet", "--detach", &commit])?;
            if fs::rename(&partial, &checkout).is_err() {
                // Another build made it first.
                let _ = fs::remove_dir_all(&partial);
            }
        }
        Ok((commit, checkout))
    }
}

/// Names the cache's directories for the repository at `url`: its last
/// part, to be readable, and a hash of the rest, to be unique.
fn key(url: &str) -> String {
    let url = url.trim_end_matches('/');
    let name = url.rsplit(['/', ':', '\\']).next().unwrap_or("");
    let name = name.trim_end_matches(".git");
    let name: String = name
        .chars()
        .map(
            |c| match c.is_ascii_alphanumeric() || c == '-' || c == '_' {
                true => c,
                false => '_',
            },
        )
        .collect();
    format!("{name}-{:016x}", fnv1a(url.as_bytes()))
}

/// The 64-bit FNV-1a hash, which unlike std's hashers never changes.
fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf29ce484222325, |hash, byte| {
        (hash ^ u64::from(*byte)).wrapping_mul(0x100000001b3)
    })
}

/// The commit `reference` names in the repository `db`, if it has it.
fn resolve(db: &Path, reference: &GitRef) -> Option<String> {
    let spec = match reference {
        GitRef::Tag(tag) => format!("refs/tags/{tag}^{{commit}}"),
        GitRef::Rev(rev) => format!("{rev}^{{commit}}"),
    };
    git(
        db,
        &[
            "rev-parse",
            "--verify",
            "--quiet",
            "--end-of-options",
            &spec,
        ],
    )
    .ok()
}

/// Fetches every branch and tag of the repository at `url` into `db`, and
/// `reference` itself if it may be a commit no branch or tag holds.
fn fetch(db: &Path, url: &str, reference: &GitRef) -> Result<(), GitError> {
    let refspecs = ["+refs/heads/*:refs/heads/*", "+refs/tags/*:refs/tags/*"];
    git(
        db,
        &[
            "fetch",
            "--quiet",
            "--end-of-options",
            url,
            refspecs[0],
            refspecs[1],
        ],
    )?;
    if let GitRef::Rev(rev) = reference
        && resolve(db, reference).is_none()
        && rev.len() == 40
    {
        // Servers may refuse to send commits by hash, which is then
        // reported as unknown.
        let _ = git(db, &["fetch", "--quiet", "--end-of-options", url, rev]);
    }
    Ok(())
}

/// Runs `git args` in `dir`, returning what it writes to stdout, trimmed.
fn git(dir: &Path, args: &[&str]) -> Result<String, GitError> {
    let output = Command::new("git")
        // These would point the command at another repository than `dir`.
        .env_remove("GIT_DIR")
        .env_remove("GIT_WORK_TREE")
        .env_remove("GIT_INDEX_FILE")
        .arg("-C")
        .arg(dir)
        .args(args)
        .output()?;
    if !output.status.success() {
        return Err(GitError::Command {
            command: format!("git {}", args.join(" ")),
            stderr: String::from_utf8_lossy(&output.stderr).trim().to_string(),
        });
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keys_are_readable_and_unique() {
        assert_eq!(
            key("https://github.com/duck/json.git"),
            format!("json-{:016x}", fnv1a(b"https://github.com/duck/json.git"))
        );
        assert_eq!(key("git@host:duck/json").split('-').next(), Some("json"));
        assert_ne!(key("https://a.org/json"), key("https://b.org/json"));
        assert_eq!(key("https://a.org/json/"), key("https://a.org/json"));
    }
}

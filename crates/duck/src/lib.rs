//! What `duck` knows of packages, for tools other than the cli to share:
//! their manifests, the packages they depend on, and their source files.

pub mod files;
pub mod git;
pub mod manifest;
pub mod package;

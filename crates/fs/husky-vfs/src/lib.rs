#![feature(iter_advance_by)]
#![allow(incomplete_features)]
#![feature(absolute_path)]
#![feature(let_chains)]
#![feature(path_add_extension)]
mod cache;
pub mod error;
mod file;
pub mod jar;
#[cfg(feature = "lsp_support")]
mod lsp_support;
pub mod path;
pub mod script;
#[cfg(feature = "test_helpers")]
pub mod test_helpers;
#[cfg(test)]
mod tests;
pub mod toolchain;
pub mod toolchain_config;
mod watch;

pub use self::cache::VfsCache;
#[cfg(feature = "lsp_support")]
pub use self::lsp_support::*;

use self::error::*;
use self::file::*;
use self::jar::{VfsJar as Jar, *};
use self::path::*;
#[cfg(feature = "test_helpers")]
use self::test_helpers::*;
use self::toolchain::*;
use dashmap::{mapref::entry::Entry, DashMap};
use husky_coword::*;
use std::path::{Path, PathBuf};
#[cfg(test)]
use tests::*;

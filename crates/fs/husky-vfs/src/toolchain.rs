mod date;
mod error;
#[cfg(test)]
mod tests;

pub use self::error::*;

use super::*;
use date::*;
use husky_platform::Platform;

#[salsa::interned(db = VfsDb)]
pub struct Toolchain {
    #[return_ref]
    pub data: ToolchainData,
}

impl Toolchain {
    pub fn library_path(self, db: &::salsa::Db) -> &Path {
        match self.data(db) {
            ToolchainData::Published(_) => todo!(),
            ToolchainData::Local { library_path } => library_path.data(),
        }
    }

    pub fn library_abs_path(self, db: &::salsa::Db) -> PathBuf {
        match self.data(db) {
            ToolchainData::Published(_) => todo!(),
            ToolchainData::Local { library_path } => library_path.abs_path(db).unwrap(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
#[salsa::derive_debug_with_db]
pub enum ToolchainData {
    Published(PublishedToolchain),
    Local { library_path: VirtualPath },
}

#[salsa::interned]
pub struct PublishedToolchain {
    channel: ToolchainChannel,
    date: ToolchainDate,
    platform: Platform,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum ToolchainChannel {
    Nightly,
    Stable,
}

impl ToolchainChannel {
    pub fn new_ad_hoc() -> Self {
        ToolchainChannel::Nightly
    }
}

#[salsa::tracked(return_ref)]
pub(crate) fn published_toolchain_library_path(
    _db: &::salsa::Db,
    _toolchain: PublishedToolchain,
) -> PathBuf {
    todo!()
}

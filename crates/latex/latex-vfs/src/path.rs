use crate::*;
use std::path::PathBuf;

#[interned::interned]
pub struct LxFilePath {
    #[return_ref]
    data: PathBuf,
}

impl std::fmt::Debug for LxFilePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("LxFilePath").field(self.data()).finish()
    }
}

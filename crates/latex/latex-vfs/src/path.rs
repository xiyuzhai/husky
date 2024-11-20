use crate::*;
use std::path::PathBuf;

#[salsa::interned]
pub struct LxFilePath {
    #[return_ref]
    data: PathBuf,
}

use husky_text_protocol::range::TextPositionRange;
use husky_vfs::{jar::VfsDb, path::module_path::ModulePath};

use crate::*;

use std::{error::Error, fmt::Display, path::PathBuf};

pub(crate) fn path_from_url(url: &lsp_types::Url) -> Result<PathBuf> {
    Ok(url
        .to_file_path()
        .map_err(|()| Box::new(PathConversionError::default()))?)
}

#[derive(Debug, Default)]
pub struct PathConversionError {}
impl Display for PathConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PathConversionError").finish()
    }
}
impl Error for PathConversionError {}

pub trait LspExt {
    type LspType;

    fn from_lsp(t: Self::LspType) -> Self;
    fn into_lsp(self) -> Self::LspType;
}

impl LspExt for PathBuf {
    type LspType = lsp_types::Url;

    fn from_lsp(_t: Self::LspType) -> Self {
        todo!()
    }

    fn into_lsp(self) -> Self::LspType {
        todo!()
    }
}

pub(crate) fn module_path_and_range(
    db: &::salsa::Db,
    document_uri: &lsp_types::Url,
    range: lsp_types::Range,
) -> Result<(ModulePath, TextPositionRange)> {
    let path = path_from_url(document_uri)?;
    let module_path = db.resolve_module_path_and_update_live_packages(&path)?;
    Ok((module_path, range.into()))
}

pub mod error;
pub mod inlay_hints;
pub mod jar;
#[cfg(feature = "lsp_support")]
pub mod lsp_support;
#[cfg(test)]
mod tests;

use self::error::*;
use self::inlay_hints::*;
use self::jar::InlayHintsJar as Jar;
#[cfg(test)]
use self::tests::*;
use husky_text_protocol::range::TextPositionRange;
use husky_vfs::path::module_path::ModulePath;
use is::Is;

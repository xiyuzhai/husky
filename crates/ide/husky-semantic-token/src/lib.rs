mod collect;
mod convert;
mod ext;
mod jar;
mod specs;
#[cfg(test)]
mod tests;
pub mod token;

pub use self::jar::*;
pub use self::specs::*;

use self::collect::*;
use self::convert::*;
use self::jar::SemanticTokenJar as Jar;
use self::token::*;
use husky_entity_tree::error::EntityTreeResult;
use husky_text_protocol::range::TextPositionRange;
use husky_token::*;
use husky_token_info::*;
use husky_vfs::path::module_path::ModulePath;

#[salsa::tracked(jar = SemanticTokenJar, return_ref)]
fn semantic_tokens(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> EntityTreeResult<Vec<SemanticToken>> {
    collect_semantic_tokens(db, module_path)
}

#[salsa::tracked(jar = SemanticTokenJar, return_ref)]
fn semantic_tokens_ext_without_range(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> EntityTreeResult<Vec<ext::SemanticToken>> {
    let tokens = semantic_tokens(db, module_path)
        .as_ref()
        .map_err(|e| e.clone())?;
    Ok(to_semantic_tokens(tokens))
}

fn semantic_tokens_ext_within_range(
    db: &::salsa::Db,
    module_path: ModulePath,
    range: &TextPositionRange,
) -> EntityTreeResult<Vec<ext::SemanticToken>> {
    let tokens = semantic_tokens(db, module_path)
        .as_ref()
        .map_err(|e| e.clone())?
        .iter()
        .filter(|token| token.range.is_within(range));
    Ok(to_semantic_tokens(tokens))
}

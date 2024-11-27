use husky_token_data::TokenData;
use husky_token_protocol::TokenClass;

use crate::*;

pub(crate) fn collect_semantic_tokens(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> EntityTreeResult<Vec<SemanticToken>> {
    let ranged_token_sheet = db.ranged_token_sheet(module_path);
    let _token_sheet_data = db.token_sheet_data(module_path);
    let token_infer_sheet = db.token_info_sheet(module_path)?;
    let iter0 = token_infer_sheet
        .informative_ranged_token_iter(ranged_token_sheet, db)
        .filter_map(|(infos, (range, token))| token_to_semantic_token(db, infos, token, range));
    let iter1 = ranged_token_sheet
        .comments()
        .iter()
        .map(|comment| comment_to_semantic_token(comment));
    Ok(itertools::merge(iter0, iter1).collect())
}

fn token_to_semantic_token(
    db: &::salsa::Db,
    infos: &[TokenInfo],
    token_data: &TokenData,
    range: &husky_text_protocol::range::TextPositionRange,
) -> Option<SemanticToken> {
    Some(SemanticToken {
        token_class: match infos.last() {
            Some(info) => info.data().token_class(db),
            None => token_data.default_token_class(),
        },
        range: *range,
    })
}

fn comment_to_semantic_token(comment: &Comment) -> SemanticToken {
    SemanticToken {
        token_class: TokenClass::Comment,
        range: comment.range(),
    }
}

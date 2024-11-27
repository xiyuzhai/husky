use dashmap::mapref::entry::Entry;
use lsp_types::{SemanticToken, SemanticTokens, SemanticTokensEdit, Url};

use super::*;
use std::sync::atomic::AtomicU32;

pub(crate) fn handle_semantic_tokens_full(
    snapshot: AnalyzerDBSnapshot,
    params: SemanticTokensParams,
) -> Result<Option<SemanticTokensResult>> {
    let _p = husky_profile_utils::span("handle_semantic_tokens_full");
    let semantic_tokens = semantic_tokens(&snapshot, &params.text_document.uri, None)?;
    // Unconditionally cache the tokens
    snapshot.cache_semantic_tokens(params.text_document.uri, semantic_tokens.clone());
    Ok(Some(SemanticTokensResult::Tokens(semantic_tokens)))
}

pub(crate) fn handle_semantic_tokens_full_delta(
    snapshot: AnalyzerDBSnapshot,
    params: SemanticTokensDeltaParams,
) -> Result<Option<SemanticTokensFullDeltaResult>> {
    let current = semantic_tokens(&snapshot, &params.text_document.uri, None)?;
    match snapshot.cached_semantic_tokens_entry(params.text_document.uri) {
        Entry::Occupied(mut entry) => {
            let cached_tokens = entry.get();
            if let Some(ref prev_id) = cached_tokens.result_id {
                if prev_id == &params.previous_result_id {
                    let delta = semantic_token_delta(&cached_tokens, &current);
                    entry.insert(current);
                    return Ok(Some(delta.into()));
                }
            }
            entry.insert(current.clone());
        }
        Entry::Vacant(entry) => {
            entry.insert(current.clone());
        }
    }
    Ok(Some(SemanticTokensFullDeltaResult::Tokens(current)))
}

pub(crate) fn handle_semantic_tokens_range(
    snapshot: AnalyzerDBSnapshot,
    params: SemanticTokensRangeParams,
) -> Result<Option<SemanticTokensRangeResult>> {
    // ad hoc
    let path = from_proto::path_from_url(&params.text_document.uri)?;
    let module_path = snapshot.resolve_module_path_and_update_live_packages(&path)?;
    let _semantic_tokens_ext =
        snapshot.semantic_tokens_ext(module_path, Some(params.range.into()))?;
    Ok(Some(SemanticTokensRangeResult::Tokens(semantic_tokens(
        &snapshot,
        &params.text_document.uri,
        Some(params.range.into()),
    )?)))
}

fn semantic_tokens(
    snapshot: &AnalyzerDBSnapshot,
    uri: &Url,
    range: Option<TextPositionRange>,
) -> Result<SemanticTokens> {
    static SEMANTIC_TOKENS_RESULT_ID_NEXT: AtomicU32 = AtomicU32::new(1);
    fn new_result_id() -> u32 {
        SEMANTIC_TOKENS_RESULT_ID_NEXT.fetch_add(1, Ordering::SeqCst)
    }
    let path = from_proto::path_from_url(uri)?;
    let module_path = snapshot.resolve_module_path_and_update_live_packages(&path)?;
    let semantic_tokens = SemanticTokens {
        result_id: Some(new_result_id().to_string()),
        data: snapshot.semantic_tokens_ext(module_path, range)?.to_vec(),
    };
    Ok(semantic_tokens)
}

fn semantic_token_delta(
    previous: &SemanticTokens,
    current: &SemanticTokens,
) -> lsp_types::SemanticTokensDelta {
    let edits = diff_tokens(&previous.data, &current.data);
    lsp_types::SemanticTokensDelta {
        result_id: current.result_id.clone(),
        edits,
    }
}

fn diff_tokens(old: &[SemanticToken], new: &[SemanticToken]) -> Vec<SemanticTokensEdit> {
    let offset = new
        .iter()
        .zip(old.iter())
        .take_while(|&(n, p)| n == p)
        .count();

    let (_, old) = old.split_at(offset);
    let (_, new) = new.split_at(offset);

    let offset_from_end = new
        .iter()
        .rev()
        .zip(old.iter().rev())
        .take_while(|&(n, p)| n == p)
        .count();

    let (old, _) = old.split_at(old.len() - offset_from_end);
    let (new, _) = new.split_at(new.len() - offset_from_end);

    if old.is_empty() && new.is_empty() {
        vec![]
    } else {
        // The lsp data field is actually a byte-diff but we
        // travel in tokens so `start` and `delete_count` are in multiples of the
        // serialized size of `SemanticToken`.
        vec![lsp_types::SemanticTokensEdit {
            start: 5 * offset as u32,
            delete_count: 5 * old.len() as u32,
            data: Some(new.into()),
        }]
    }
}

use crate::*;
use husky_entity_tree::{
    node::script::ScriptSynNodePath, prelude::PreludeResult, region_path::SynNodeRegionPath,
    symbol::ModuleSymbolContext,
};
use husky_token::TokenDb;
use husky_vfs::{path::crate_path::CratePath, script::Script};

#[cfg(test)]
pub(crate) fn try_parse_snippet_in_decl<T>(
    input: &str,
    db: &::salsa::Db,
) -> SynExprResult<Option<T>>
where
    T: for<'a> parsec::TryParseOptionFromStream<
        parser::StandaloneSynExprParser<'a>,
        Error = SynExprError,
    >,
{
    use husky_entity_tree::{region_path::SynNodeRegionPath, symbol::ModuleSymbolContext};
    use husky_vfs::{jar::VfsDb, test_helpers::VfsTestUtilsDb};
    use parsec::IsStreamParser;

    // "" wouldn't work
    assert!(input.len() > 0);
    let script = Script::new_dev_snippet(input, db);
    let toolchain = db.dev_toolchain().unwrap();
    let path_menu = db.vfs_path_menu(toolchain);
    let crate_path = path_menu.core_library();
    let token_sheet_data = db.chunk_token_sheet_data(script);
    let expr_context = SynExprContext::new2(
        db,
        SynNodeRegionPath::ItemDefn(ScriptSynNodePath::new(script, db).into()),
        ModuleSymbolContext::new_default(db, crate_path).unwrap(),
        None,
        AllowSelfType::False,
        AllowSelfValue::False,
        None,
    )
    .unwrap();
    let token_stream =
        RegionalTokenStream::new_snippet_regional_token_stream(token_sheet_data.tokens());
    let mut expr_parser = expr_context.token_stream_expr_parser(None, token_stream);
    expr_parser.try_parse_option()
}

#[salsa::tracked(return_ref)]
pub fn parse_expr_from_script(
    db: &::salsa::Db,
    crate_path: CratePath,
    script: Script,
) -> PreludeResult<(SynExprRegion, Option<SynExprIdx>)> {
    let token_sheet_data = db.chunk_token_sheet_data(script);
    let expr_context = SynExprContext::new2(
        db,
        SynNodeRegionPath::ItemDefn(ScriptSynNodePath::new(script, db).into()),
        ModuleSymbolContext::new_default(db, crate_path)?,
        None,
        AllowSelfType::False,
        AllowSelfValue::False,
        None,
    )
    .unwrap();
    let token_stream =
        RegionalTokenStream::new_snippet_regional_token_stream(token_sheet_data.tokens());
    let mut expr_parser = expr_context.token_stream_expr_parser(None, token_stream);
    let expr = expr_parser.parse_expr_root(None, SynExprRootKind::Snippet);
    Ok((expr_parser.finish(), expr))
}

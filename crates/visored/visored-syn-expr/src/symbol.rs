pub(crate) mod builder;
pub mod local_defn;
pub mod resolution;
pub mod scope;

use self::{builder::*, local_defn::*, resolution::*};
use crate::{
    clause::VdSynClauseArenaRef, division::VdSynDivisionArenaRef, expr::VdSynExprArenaRef,
    phrase::VdSynPhraseArenaRef, range::*, sentence::VdSynSentenceArenaRef,
    stmt::VdSynStmtArenaRef, *,
};
use latex_math_letter::letter::LxMathLetter;
use stmt::VdSynStmtIdxRange;

pub enum VdSynSymbol {
    Letter(LxMathLetter),
}

pub struct VdSynExprVariableIdx {}

pub struct VdSynExprVariableData {}

pub(crate) fn build_all_symbol_defns_and_resolutions_in_expr_or_stmts(
    db: &::salsa::Db,
    token_storage: &LxTokenStorage,
    ast_arena: LxAstArenaRef,
    ast_token_idx_range_map: &LxAstTokenIdxRangeMap,
    annotations: &VdAnnotations,
    default_resolution_table: &VdDefaultGlobalResolutionTable,
    expr_arena: VdSynExprArenaRef,
    phrase_arena: VdSynPhraseArenaRef,
    clause_arena: VdSynClauseArenaRef,
    sentence_arena: VdSynSentenceArenaRef,
    stmt_arena: VdSynStmtArenaRef,
    division_arena: VdSynDivisionArenaRef,
    expr_range_map: &VdSynExprTokenIdxRangeMap,
    phrase_range_map: &VdSynPhraseTokenIdxRangeMap,
    clause_range_map: &VdSynClauseTokenIdxRangeMap,
    sentence_range_map: &VdSynSentenceTokenIdxRangeMap,
    stmt_range_map: &VdSynStmtTokenIdxRangeMap,
    division_range_map: &VdSynDivisionTokenIdxRangeMap,
    expr_or_stmts: Either<VdSynExprIdx, VdSynStmtIdxRange>,
) -> (VdSynSymbolLocalDefnTable, VdSynSymbolResolutionsTable) {
    let mut symbol_builder = VdSynSymbolBuilder::new(
        db,
        &token_storage,
        ast_arena,
        ast_token_idx_range_map,
        annotations,
        default_resolution_table,
        expr_arena,
        phrase_arena,
        clause_arena,
        sentence_arena,
        stmt_arena,
        division_arena,
        expr_range_map,
        phrase_range_map,
        clause_range_map,
        sentence_range_map,
        stmt_range_map,
        division_range_map,
    );
    match expr_or_stmts {
        Left(expr) => symbol_builder.build_expr(expr),
        Right(stmts) => symbol_builder.build_stmts(stmts),
    };
    symbol_builder.finish()
}

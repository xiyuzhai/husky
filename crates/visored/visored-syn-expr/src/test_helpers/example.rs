use super::*;
use crate::{
    builder::VdSynExprBuilder,
    clause::VdSynClauseArena,
    expr::VdSynExprArena,
    phrase::VdSynPhraseArena,
    range::{
        VdSynClauseTokenIdxRangeMap, VdSynExprTokenIdxRangeMap, VdSynPhraseTokenIdxRangeMap,
        VdSynSentenceTokenIdxRangeMap,
    },
    sentence::VdSynSentenceArena,
};
use division::VdSynDivisionArena;
use expr::VdSynExprIdx;
use helpers::show::display_tree::VdSynExprDisplayTreeBuilder;
use latex_ast::{
    ast::{parse_latex_input_into_asts, rose::LxRoseAstIdxRange, LxAstArena, LxAstIdxRange},
    range::{calc_ast_token_idx_range_map, LxAstTokenIdxRangeMap},
};
use latex_command::signature::table::LxCommandSignatureTable;
use latex_environment::signature::table::LxEnvironmentSignatureTable;
use latex_prelude::mode::LxMode;
use latex_token::{idx::LxTokenIdxRange, storage::LxTokenStorage};
use range::{calc_expr_range_map, VdSynDivisionTokenIdxRangeMap, VdSynStmtTokenIdxRangeMap};
use stmt::{VdSynStmtArena, VdSynStmtIdxRange};
use symbol::{local_defn::VdSynSymbolLocalDefnTable, resolution::VdSynSymbolResolutionsTable};
use visored_annotation::{
    annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation},
    annotations::VdAnnotations,
};
use visored_global_resolution::table::VdDefaultGlobalResolutionTable;

pub struct VdSynExprExample {
    pub input: String,
    pub root_mode: LxMode,
    pub annotations: VdAnnotations,
    pub default_resolution_table: VdDefaultGlobalResolutionTable,
    pub token_storage: LxTokenStorage,
    pub ast_arena: LxAstArena,
    pub asts: LxAstIdxRange,
    pub ast_token_idx_range_map: LxAstTokenIdxRangeMap,
    pub result: Either<VdSynExprIdx, VdSynStmtIdxRange>,
    pub expr_arena: VdSynExprArena,
    pub phrase_arena: VdSynPhraseArena,
    pub clause_arena: VdSynClauseArena,
    pub sentence_arena: VdSynSentenceArena,
    pub stmt_arena: VdSynStmtArena,
    pub division_arena: VdSynDivisionArena,
    pub expr_range_map: VdSynExprTokenIdxRangeMap,
    pub phrase_range_map: VdSynPhraseTokenIdxRangeMap,
    pub clause_range_map: VdSynClauseTokenIdxRangeMap,
    pub sentence_range_map: VdSynSentenceTokenIdxRangeMap,
    pub stmt_range_map: VdSynStmtTokenIdxRangeMap,
    pub division_range_map: VdSynDivisionTokenIdxRangeMap,
    pub symbol_defns: VdSynSymbolLocalDefnTable,
    pub symbol_resolution_table: VdSynSymbolResolutionsTable,
}

impl VdSynExprExample {
    // TODO: reuse LxAstExample
    pub fn new(
        input: &str,
        root_mode: LxMode,
        token_annotations: &[((&str, &str), VdTokenAnnotation)],
        space_annotations: &[((&str, &str), VdSpaceAnnotation)],
        db: &salsa::Db,
    ) -> Self {
        let mut ast_arena = LxAstArena::default();
        let mut token_storage = LxTokenStorage::default();
        let command_signature_table = LxCommandSignatureTable::new_default(db);
        let environment_signature_table = LxEnvironmentSignatureTable::new_default(db);
        let asts = parse_latex_input_into_asts(
            db,
            &command_signature_table,
            &environment_signature_table,
            input,
            root_mode,
            &mut token_storage,
            &mut ast_arena,
        );
        let whole_token_range = token_storage.whole_token_idx_range();
        let ast_token_idx_range_map = calc_ast_token_idx_range_map(db, &ast_arena);
        let annotations = VdAnnotations::from_sparse(
            input,
            token_annotations.iter().copied(),
            space_annotations.iter().copied(),
            &token_storage,
        );
        let default_resolution_table = VdDefaultGlobalResolutionTable::new_standard(db);
        let mut builder = VdSynExprBuilder::new(
            db,
            &token_storage,
            ast_arena.as_arena_ref(),
            &ast_token_idx_range_map,
            &annotations,
            &default_resolution_table,
        );
        let result = (whole_token_range, asts).to_vd_syn(&mut builder);
        let (
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
            symbol_defns,
            symbol_resolutions,
        ) = builder.finish_with_expr_or_stmts(result);
        Self {
            input: input.to_string(),
            root_mode,
            annotations,
            default_resolution_table,
            token_storage,
            ast_arena,
            asts,
            ast_token_idx_range_map,
            result,
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
            symbol_defns,
            symbol_resolution_table: symbol_resolutions,
        }
    }

    pub(crate) fn show_display_tree(&self, db: &salsa::Db) -> String {
        let builder = VdSynExprDisplayTreeBuilder::new(
            db,
            &self.input,
            &self.token_storage,
            self.ast_arena.as_arena_ref(),
            &self.ast_token_idx_range_map,
            self.expr_arena.as_arena_ref(),
            self.phrase_arena.as_arena_ref(),
            self.clause_arena.as_arena_ref(),
            self.sentence_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.division_arena.as_arena_ref(),
            &self.expr_range_map,
            &self.phrase_range_map,
            &self.clause_range_map,
            &self.sentence_range_map,
            &self.stmt_range_map,
            &self.division_range_map,
        );
        match self.result {
            Left(expr) => builder.render_expr(expr).show(&Default::default()),
            Right(stmts) => builder.render_all_stmts(stmts).show(&Default::default()),
        }
    }
}

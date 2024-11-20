use super::*;
use crate::range::{calc_expr_range_map, VdSemStmtTokenIdxRangeMap};
use crate::stmt::{VdSemStmtArena, VdSemStmtIdxRange};
use crate::{
    builder::VdSemExprBuilder,
    clause::VdSemClauseArena,
    expr::VdSemExprArena,
    phrase::VdSemPhraseArena,
    range::{
        VdSemClauseTokenIdxRangeMap, VdSemExprTokenIdxRangeMap, VdSemPhraseTokenIdxRangeMap,
        VdSemSentenceTokenIdxRangeMap,
    },
    sentence::VdSemSentenceArena,
};
use crate::{division::VdSemDivisionArena, expr::VdSemExprIdx};
use crate::{
    helpers::show::display_tree::VdSemExprDisplayTreeBuilder, range::VdSemDivisionTokenIdxRangeMap,
};
use division::VdSemDivisionIdxRange;
use either::*;
use husky_tree_utils::display::DisplayTree;
use latex_ast::{
    ast::{parse_latex_input_into_asts, rose::LxRoseAstIdxRange, LxAstArena, LxAstIdxRange},
    range::{calc_ast_token_idx_range_map, LxAstTokenIdxRangeMap},
};
use latex_command::signature::table::LxCommandSignatureTable;
use latex_prelude::{
    helper::tracker::{LxDocumentBodyInput, LxDocumentInput, LxFormulaInput, LxPageInput},
    mode::LxMode,
};
use latex_token::{idx::LxTokenIdxRange, storage::LxTokenStorage};
use symbol::local_defn::storage::VdSemSymbolLocalDefnStorage;
use visored_annotation::{
    annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation},
    annotations::VdAnnotations,
};
use visored_global_dispatch::default_table::VdDefaultGlobalDispatchTable;
use visored_global_resolution::default_table::VdDefaultGlobalResolutionTable;
use visored_item_path::module::VdModulePath;
use visored_syn_expr::{
    clause::VdSynClauseArena,
    division::VdSynDivisionArena,
    expr::VdSynExprArena,
    helpers::tracker::{IsVdSynExprInput, VdSynExprTracker},
    phrase::VdSynPhraseArena,
    range::{
        VdSynClauseTokenIdxRangeMap, VdSynDivisionTokenIdxRangeMap, VdSynExprTokenIdxRangeMap,
        VdSynPhraseTokenIdxRangeMap, VdSynSentenceTokenIdxRangeMap, VdSynStmtTokenIdxRangeMap,
    },
    sentence::VdSynSentenceArena,
    stmt::VdSynStmtArena,
};
use visored_term::ty::table::VdItemPathZfcTypeTable;

pub struct VdSemExprTracker<'a, Input: IsVdSemExprInput<'a>> {
    pub input: Input,
    pub root_module_path: VdModulePath,
    pub annotations: VdAnnotations,
    pub default_resolution_table: VdDefaultGlobalResolutionTable,
    pub token_storage: LxTokenStorage,
    pub ast_arena: LxAstArena,
    pub ast_token_idx_range_map: LxAstTokenIdxRangeMap,
    pub expr_arena: VdSemExprArena,
    pub phrase_arena: VdSemPhraseArena,
    pub clause_arena: VdSemClauseArena,
    pub sentence_arena: VdSemSentenceArena,
    pub stmt_arena: VdSemStmtArena,
    pub division_arena: VdSemDivisionArena,
    pub expr_range_map: VdSemExprTokenIdxRangeMap,
    pub phrase_range_map: VdSemPhraseTokenIdxRangeMap,
    pub clause_range_map: VdSemClauseTokenIdxRangeMap,
    pub sentence_range_map: VdSemSentenceTokenIdxRangeMap,
    pub stmt_range_map: VdSemStmtTokenIdxRangeMap,
    pub division_range_map: VdSemDivisionTokenIdxRangeMap,
    pub symbol_local_defn_storage: VdSemSymbolLocalDefnStorage,
    pub output: Input::VdSemExprOutput,
}

pub trait IsVdSemExprInput<'a>: IsVdSynExprInput<'a> {
    type VdSemExprOutput: IsVdSemExprOutput + FromToVdSem<Self::VdSynExprOutput>;
}

pub trait FromToVdSem<S>: Sized {
    fn from_to_vd_sem(s: S, builder: &mut VdSemExprBuilder) -> Self;
}

impl<S, T> FromToVdSem<S> for T
where
    S: ToVdSem<T>,
{
    fn from_to_vd_sem(s: S, builder: &mut VdSemExprBuilder) -> Self {
        s.to_vd_sem(builder)
    }
}

pub trait IsVdSemExprOutput: std::fmt::Debug + Copy {
    fn show(self, builder: &VdSemExprDisplayTreeBuilder) -> String;
}

impl<'a, Input: IsVdSemExprInput<'a>> VdSemExprTracker<'a, Input> {
    pub fn new(
        input: Input,
        token_annotations: &[((&str, &str), VdTokenAnnotation)],
        space_annotations: &[((&str, &str), VdSpaceAnnotation)],
        db: &salsa::Db,
    ) -> Self {
        let VdSynExprTracker {
            input,
            token_storage,
            ast_arena,
            ast_token_idx_range_map,
            annotations,
            default_resolution_table,
            expr_arena: syn_expr_arena,
            phrase_arena: syn_phrase_arena,
            clause_arena: syn_clause_arena,
            sentence_arena: syn_sentence_arena,
            stmt_arena: syn_stmt_arena,
            division_arena: syn_division_arena,
            expr_range_map: syn_expr_range_map,
            phrase_range_map: syn_phrase_range_map,
            clause_range_map: syn_clause_range_map,
            sentence_range_map: syn_sentence_range_map,
            stmt_range_map: syn_stmt_range_map,
            division_range_map: syn_division_range_map,
            symbol_local_defn_storage: syn_symbol_local_defn_storage,
            symbol_resolution_table: syn_symbol_resolution_table,
            root_entity_tree_node,
            stmt_entity_tree_node_map: syn_stmt_entity_tree_node_map,
            division_entity_tree_node_map: syn_division_entity_tree_node_map,
            output: syn_output,
        } = VdSynExprTracker::new(input, token_annotations, space_annotations, db);
        let item_path_zfc_ty_table = VdItemPathZfcTypeTable::new_standard(db);
        let default_global_dispatch_table = VdDefaultGlobalDispatchTable::new_standard(db);
        let mut builder = VdSemExprBuilder::new(
            db,
            &token_storage,
            &annotations,
            &default_resolution_table,
            syn_expr_arena.as_arena_ref(),
            syn_phrase_arena.as_arena_ref(),
            syn_clause_arena.as_arena_ref(),
            syn_sentence_arena.as_arena_ref(),
            syn_stmt_arena.as_arena_ref(),
            syn_division_arena.as_arena_ref(),
            &syn_symbol_local_defn_storage,
            &syn_symbol_resolution_table,
            &item_path_zfc_ty_table,
            &default_global_dispatch_table,
            &syn_stmt_entity_tree_node_map,
            &syn_division_entity_tree_node_map,
        );
        let output = FromToVdSem::from_to_vd_sem(syn_output, &mut builder);
        let (
            expr_arena,
            phrase_arena,
            clause_arena,
            sentence_arena,
            stmt_arena,
            division_arena,
            symbol_local_defn_storage,
        ) = builder.finish();
        let (
            expr_range_map,
            phrase_range_map,
            clause_range_map,
            sentence_range_map,
            stmt_range_map,
            division_range_map,
        ) = calc_expr_range_map(
            db,
            &expr_arena,
            &phrase_arena,
            &clause_arena,
            &sentence_arena,
            &stmt_arena,
            &division_arena,
        );
        Self {
            input,
            root_module_path: root_entity_tree_node.module_path(),
            annotations,
            default_resolution_table,
            token_storage,
            ast_arena,
            ast_token_idx_range_map,
            expr_arena,
            phrase_arena,
            clause_arena,
            sentence_arena,
            stmt_arena,
            division_arena,
            symbol_local_defn_storage,
            expr_range_map,
            phrase_range_map,
            clause_range_map,
            sentence_range_map,
            stmt_range_map,
            division_range_map,
            output,
        }
    }

    pub(crate) fn show_display_tree(&self, db: &salsa::Db) -> String {
        let builder = VdSemExprDisplayTreeBuilder::new(
            db,
            self.input.content(),
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
        self.output.show(&builder)
        // match self.result {
        //     Left(expr) => builder.render_expr(expr).show(&Default::default()),
        //     Right(stmts) => builder.render_all_stmts(stmts).show(&Default::default()),
        // }
    }
}

impl<'a> IsVdSemExprInput<'a> for LxDocumentInput<'a> {
    type VdSemExprOutput = VdSemDivisionIdxRange;
}

impl<'a> IsVdSemExprInput<'a> for LxDocumentBodyInput<'a> {
    type VdSemExprOutput = VdSemDivisionIdxRange;
}

impl<'a> IsVdSemExprInput<'a> for LxPageInput<'a> {
    type VdSemExprOutput = VdSemStmtIdxRange;
}

impl<'a> IsVdSemExprInput<'a> for LxFormulaInput<'a> {
    type VdSemExprOutput = VdSemExprIdx;
}

impl IsVdSemExprOutput for VdSemDivisionIdxRange {
    fn show(self, builder: &VdSemExprDisplayTreeBuilder) -> String {
        DisplayTree::show_trees(&builder.render_divisions(self), &Default::default())
    }
}

impl IsVdSemExprOutput for VdSemStmtIdxRange {
    fn show(self, builder: &VdSemExprDisplayTreeBuilder) -> String {
        builder.render_all_stmts(self).show(&Default::default())
    }
}

impl IsVdSemExprOutput for VdSemExprIdx {
    fn show(self, builder: &VdSemExprDisplayTreeBuilder) -> String {
        builder.render_expr(self).show(&Default::default())
    }
}

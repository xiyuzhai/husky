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
use builder::FromToVdSyn;
use clause::VdSynClauseIdx;
use division::{VdSynDivisionArena, VdSynDivisionIdxRange, VdSynDivisionMap};
use entity_tree::{builder::VdSynExprEntityTreeBuilder, VdSynExprEntityTreeNode};
use expr::VdSynExprIdx;
use helpers::show::display_tree::VdSynExprDisplayTreeBuilder;
use husky_tree_utils::display::DisplayTree;
use latex_ast::{
    ast::{
        parse_latex_input_into_asts, root::LxRootAstIdxRange, rose::LxRoseAstIdxRange, LxAstArena,
        LxAstIdxRange,
    },
    helpers::tracker::{IsLxAstInput, LxAstTracker},
    range::{calc_ast_token_idx_range_map, LxAstTokenIdxRangeMap},
};
use latex_command::signature::table::LxCommandSignatureTable;
use latex_environment::signature::table::LxEnvironmentSignatureTable;
use latex_prelude::{
    helper::tracker::{LxDocumentBodyInput, LxDocumentInput, LxFormulaInput, LxPageInput},
    mode::LxMode,
};
use latex_token::{idx::LxTokenIdxRange, lane::LxTokenLane, storage::LxTokenStorage};
use phrase::VdSynPhraseIdx;
use range::{calc_expr_range_map, VdSynDivisionTokenIdxRangeMap, VdSynStmtTokenIdxRangeMap};
use sealed::*;
use sentence::VdSynSentenceIdx;
use stmt::{VdSynStmtArena, VdSynStmtIdx, VdSynStmtIdxRange, VdSynStmtMap};
use symbol::{
    builder::VdSynSymbolBuilder, local_defn::VdSynSymbolLocalDefnStorage,
    resolution::VdSynSymbolResolutionsTable,
};
use visored_annotation::{
    annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation},
    annotations::VdAnnotations,
};
use visored_entity_path::module::VdModulePath;
use visored_global_resolution::default_table::VdDefaultGlobalResolutionTable;

pub struct VdSynExprTracker<'a, Input: IsVdSynExprInput<'a>> {
    pub input: Input,
    pub annotations: VdAnnotations,
    pub default_resolution_table: VdDefaultGlobalResolutionTable,
    pub token_storage: LxTokenStorage,
    pub ast_arena: LxAstArena,
    pub ast_token_idx_range_map: LxAstTokenIdxRangeMap,
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
    pub symbol_local_defn_storage: VdSynSymbolLocalDefnStorage,
    pub symbol_resolution_table: VdSynSymbolResolutionsTable,
    pub root_entity_tree_node: VdSynExprEntityTreeNode,
    pub stmt_entity_tree_node_map: VdSynStmtMap<VdSynExprEntityTreeNode>,
    pub division_entity_tree_node_map: VdSynDivisionMap<VdSynExprEntityTreeNode>,
    pub output: Input::VdSynExprOutput,
}

// #[sealed]
pub trait IsVdSynExprInput<'a>: IsLxAstInput<'a> {
    type VdSynExprOutput: IsVdSynOutput + FromToVdSyn<(LxTokenIdxRange, Self::LxAstOutput)>;
}

pub trait IsVdSynOutput: std::fmt::Debug + Copy {
    fn build_entity_tree_root_node(
        self,
        builder: &mut VdSynExprEntityTreeBuilder,
    ) -> VdSynExprEntityTreeNode;
    fn build_all_symbols(self, builder: &mut VdSynSymbolBuilder);
    fn show(&self, builder: &VdSynExprDisplayTreeBuilder) -> String;
}

// #[sealed]
impl<'a, Input: IsVdSynExprInput<'a>> VdSynExprTracker<'a, Input> {
    pub fn new(
        input: Input,
        token_annotations: &[((&str, &str), VdTokenAnnotation)],
        space_annotations: &[((&str, &str), VdSpaceAnnotation)],
    ) -> Self {
        let LxAstTracker {
            command_signature_table,
            input,
            token_storage,
            ast_arena,
            ast_token_idx_range_map,
            output: lx_ast_output,
        } = LxAstTracker::new(input);
        // ad hoc
        let whole_token_range = token_storage.whole_token_idx_range(LxTokenLane::Main);
        let annotations = VdAnnotations::from_sparse(
            input.content(),
            token_annotations.iter().copied(),
            space_annotations.iter().copied(),
            &token_storage,
        );
        let default_resolution_table = VdDefaultGlobalResolutionTable::new_standard();
        let mut builder = VdSynExprBuilder::new(
            input.file_path(),
            &token_storage,
            ast_arena.as_arena_ref(),
            &ast_token_idx_range_map,
            &annotations,
            &default_resolution_table,
        );
        let output = FromToVdSyn::from_to_vd_syn((whole_token_range, lx_ast_output), &mut builder);
        //  = (whole_token_range, asts).to_vd_syn(&mut builder);
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
            root_entity_tree_node,
            stmt_entity_tree_node_map,
            division_entity_tree_node_map,
            symbol_defns,
            symbol_resolutions,
        ) = builder.finish_with(output);
        Self {
            input,
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
            expr_range_map,
            phrase_range_map,
            clause_range_map,
            sentence_range_map,
            stmt_range_map,
            division_range_map,
            symbol_local_defn_storage: symbol_defns,
            symbol_resolution_table: symbol_resolutions,
            root_entity_tree_node,
            stmt_entity_tree_node_map,
            division_entity_tree_node_map,
            output,
        }
    }

    fn display_tree_builder<'b>(&'b self) -> VdSynExprDisplayTreeBuilder<'b> {
        VdSynExprDisplayTreeBuilder::new(
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
        )
    }

    pub(crate) fn show_display_tree(&self) -> String {
        let builder = self.display_tree_builder();
        self.output.show(&builder)
    }
}

impl<'a> IsVdSynExprInput<'a> for LxDocumentInput<'a> {
    type VdSynExprOutput = VdSynDivisionIdxRange;
}

impl<'a> IsVdSynExprInput<'a> for LxDocumentBodyInput<'a> {
    type VdSynExprOutput = VdSynDivisionIdxRange;
}

impl<'a> IsVdSynExprInput<'a> for LxPageInput<'a> {
    type VdSynExprOutput = VdSynStmtIdxRange;
}

impl<'a> IsVdSynExprInput<'a> for LxFormulaInput<'a> {
    type VdSynExprOutput = VdSynExprIdx;
}

impl IsVdSynOutput for VdSynDivisionIdxRange {
    fn build_entity_tree_root_node(
        self,
        builder: &mut VdSynExprEntityTreeBuilder,
    ) -> VdSynExprEntityTreeNode {
        builder.build_root_divisions(self)
    }

    fn build_all_symbols(self, builder: &mut VdSynSymbolBuilder) {
        builder.build_divisions(self)
    }

    fn show(&self, builder: &VdSynExprDisplayTreeBuilder) -> String {
        DisplayTree::show_trees(&builder.render_divisions(*self), &Default::default())
    }
}

impl IsVdSynOutput for VdSynStmtIdxRange {
    fn build_entity_tree_root_node(
        self,
        builder: &mut VdSynExprEntityTreeBuilder,
    ) -> VdSynExprEntityTreeNode {
        builder.build_root_stmts(self)
    }

    fn build_all_symbols(self, builder: &mut VdSynSymbolBuilder) {
        builder.build_stmts(self);
    }

    fn show(&self, builder: &VdSynExprDisplayTreeBuilder) -> String {
        builder.render_all_stmts(*self).show(&Default::default())
    }
}

impl IsVdSynOutput for VdSynExprIdx {
    fn build_entity_tree_root_node(
        self,
        builder: &mut VdSynExprEntityTreeBuilder,
    ) -> VdSynExprEntityTreeNode {
        VdSynExprEntityTreeNode::new(VdModulePath::new_root(builder.file_path()), vec![])
    }

    fn build_all_symbols(self, builder: &mut VdSynSymbolBuilder) {
        builder.build_expr(self);
    }

    fn show(&self, builder: &VdSynExprDisplayTreeBuilder) -> String {
        builder.render_expr(*self).show(&Default::default())
    }
}

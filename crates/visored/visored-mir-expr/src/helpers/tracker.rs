use crate::{
    builder::VdMirExprBuilder,
    expr::{VdMirExprArena, VdMirExprIdx},
    stmt::{VdMirStmtArena, VdMirStmtIdxRange},
    *,
};
use either::*;
use expr::{application::VdMirFunc, VdMirExprData};
use helpers::show::display_tree::VdMirExprDisplayTreeBuilder;
use husky_tree_utils::display::DisplayTree;
use latex_prelude::{
    helper::tracker::{LxDocumentBodyInput, LxDocumentInput, LxFormulaInput, LxPageInput},
    mode::LxMode,
};
use symbol::local_defn::storage::VdMirSymbolLocalDefnStorage;
use visored_annotation::annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation};
use visored_entity_path::module::VdModulePath;
use visored_sem_expr::helpers::tracker::{IsVdSemExprInput, VdSemExprTracker};

pub struct VdMirExprTracker<'a, Input: IsVdMirExprInput<'a>> {
    pub root_module_path: VdModulePath,
    pub expr_arena: VdMirExprArena,
    pub stmt_arena: VdMirStmtArena,
    pub symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
    pub output: Input::VdMirExprOutput,
}

pub trait IsVdMirExprInput<'a>: IsVdSemExprInput<'a> {
    type VdMirExprOutput: IsVdMirExprOutput + FromToVdMir<Self::VdSemExprOutput>;
}

pub trait IsVdMirExprOutput: std::fmt::Debug + Copy {
    fn show(self, builder: &VdMirExprDisplayTreeBuilder) -> String;
}

pub trait FromToVdMir<S> {
    fn from_to_vd_mir(output: S, builder: &mut VdMirExprBuilder) -> Self;
}

impl<'a, S, T: IsVdMirExprOutput> FromToVdMir<S> for T
where
    S: ToVdMir<T>,
{
    fn from_to_vd_mir(s: S, builder: &mut VdMirExprBuilder) -> Self {
        s.to_vd_mir(builder)
    }
}

impl<'a, Input: IsVdMirExprInput<'a>> VdMirExprTracker<'a, Input> {
    pub fn new(
        input: Input,
        token_annotations: &[((&str, &str), VdTokenAnnotation)],
        space_annotations: &[((&str, &str), VdSpaceAnnotation)],
    ) -> Self {
        let VdSemExprTracker {
            root_module_path,
            input,
            annotations,
            default_resolution_table,
            token_storage,
            ast_arena,
            ast_token_idx_range_map,
            expr_arena: sem_expr_arena,
            phrase_arena: sem_phrase_arena,
            clause_arena: sem_clause_arena,
            sentence_arena: sem_sentence_arena,
            stmt_arena: sem_stmt_arena,
            division_arena: sem_division_arena,
            expr_range_map: sem_expr_range_map,
            phrase_range_map: sem_phrase_range_map,
            clause_range_map: sem_clause_range_map,
            sentence_range_map: sem_sentence_range_map,
            stmt_range_map: sem_stmt_range_map,
            division_range_map: sem_division_range_map,
            symbol_local_defn_storage: sem_symbol_local_defn_storage,
            output,
        } = VdSemExprTracker::new(input, token_annotations, space_annotations);
        let mut builder = VdMirExprBuilder::new(
            sem_expr_arena.as_arena_ref(),
            sem_phrase_arena.as_arena_ref(),
            sem_clause_arena.as_arena_ref(),
            sem_sentence_arena.as_arena_ref(),
            sem_stmt_arena.as_arena_ref(),
            sem_division_arena.as_arena_ref(),
            &sem_symbol_local_defn_storage,
        );
        let result = FromToVdMir::from_to_vd_mir(output, &mut builder);
        let (expr_arena, stmt_arena, symbol_local_defn_storage) = builder.finish();
        Self {
            root_module_path,
            expr_arena,
            stmt_arena,
            symbol_local_defn_storage,
            output: result,
        }
    }

    pub(crate) fn show_display_tree(&self) -> String {
        let builder = self.display_tree_builder();
        self.output.show(&builder)
    }

    fn display_tree_builder<'b>(&'b self) -> VdMirExprDisplayTreeBuilder<'b> {
        VdMirExprDisplayTreeBuilder::new(
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
        )
    }
}

impl<'a> IsVdMirExprInput<'a> for LxDocumentInput<'a> {
    type VdMirExprOutput = VdMirStmtIdxRange;
}

impl<'a> IsVdMirExprInput<'a> for LxDocumentBodyInput<'a> {
    type VdMirExprOutput = VdMirStmtIdxRange;
}

impl<'a> IsVdMirExprInput<'a> for LxPageInput<'a> {
    type VdMirExprOutput = VdMirStmtIdxRange;
}

impl<'a> IsVdMirExprInput<'a> for LxFormulaInput<'a> {
    type VdMirExprOutput = VdMirExprIdx;
}

impl IsVdMirExprOutput for VdMirStmtIdxRange {
    fn show(self, builder: &VdMirExprDisplayTreeBuilder) -> String {
        DisplayTree::show_trees(&builder.render_stmts(self), &Default::default())
    }
}

impl IsVdMirExprOutput for VdMirExprIdx {
    fn show(self, builder: &VdMirExprDisplayTreeBuilder) -> String {
        builder.render_expr(self).show(&Default::default())
    }
}

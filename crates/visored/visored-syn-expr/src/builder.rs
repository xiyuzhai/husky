use std::iter::Peekable;

use crate::{
    clause::{VdSynClauseArena, VdSynClauseData, VdSynClauseIdx, VdSynClauseIdxRange},
    division::{VdSynDivisionArena, VdSynDivisionData, VdSynDivisionIdxRange},
    entity_tree::build_entity_tree_with,
    expr::{VdSynExprArena, VdSynExprData, VdSynExprIdx, VdSynExprIdxRange},
    helpers::tracker::IsVdSynOutput,
    phrase::{VdSynPhraseArena, VdSynPhraseData, VdSynPhraseIdx, VdSynPhraseIdxRange},
    range::*,
    region::VdSynExprRegionData,
    sentence::{VdSynSentenceArena, VdSynSentenceData, VdSynSentenceIdx, VdSynSentenceIdxRange},
    stmt::{VdSynStmtArena, VdSynStmtData, VdSynStmtIdx, VdSynStmtIdxRange},
    symbol::{
        build_all_symbol_defns_and_resolutions_with, builder::VdSynSymbolBuilder,
        local_defn::VdSynSymbolLocalDefnStorage, resolution::VdSynSymbolResolutionsTable,
    },
};
use crate::{division::VdSynDivisionMap, entity_tree::VdSynExprEntityTreeNode, stmt::VdSynStmtMap};
use either::*;
use latex_ast::{
    ast::{
        rose::{LxRoseAstData, LxRoseAstIdx, LxRoseAstIdxRange},
        LxAstArena, LxAstArenaRef, LxAstIdxRange,
    },
    range::LxAstTokenIdxRangeMap,
};
use latex_token::{idx::LxTokenIdxRange, storage::LxTokenStorage};
use latex_vfs::path::LxFilePath;
use visored_annotation::annotations::VdAnnotations;
use visored_global_resolution::{
    default_table::VdDefaultGlobalResolutionTable,
    resolution::command::VdCompleteCommandGlobalResolution,
};
use visored_item_path::module::VdModulePath;

pub struct VdSynExprBuilder<'db> {
    db: &'db ::salsa::Db,
    file_path: LxFilePath,
    token_storage: &'db LxTokenStorage,
    ast_arena: LxAstArenaRef<'db>,
    ast_token_idx_range_map: &'db LxAstTokenIdxRangeMap,
    annotations: &'db VdAnnotations,
    default_resolution_table: &'db VdDefaultGlobalResolutionTable,
    expr_arena: VdSynExprArena,
    phrase_arena: VdSynPhraseArena,
    clause_arena: VdSynClauseArena,
    sentence_arena: VdSynSentenceArena,
    stmt_arena: VdSynStmtArena,
    division_arena: VdSynDivisionArena,
}

/// # constructor
impl<'db> VdSynExprBuilder<'db> {
    pub fn new(
        db: &'db ::salsa::Db,
        file_path: LxFilePath,
        token_storage: &'db LxTokenStorage,
        ast_arena: LxAstArenaRef<'db>,
        ast_token_idx_range_map: &'db LxAstTokenIdxRangeMap,
        annotations: &'db VdAnnotations,
        default_resolution_table: &'db VdDefaultGlobalResolutionTable,
    ) -> Self {
        Self {
            db,
            file_path,
            token_storage,
            ast_arena,
            ast_token_idx_range_map,
            annotations,
            default_resolution_table,
            expr_arena: Default::default(),
            phrase_arena: Default::default(),
            clause_arena: Default::default(),
            sentence_arena: Default::default(),
            stmt_arena: Default::default(),
            division_arena: Default::default(),
        }
    }
}

/// # getters
impl<'db> VdSynExprBuilder<'db> {
    pub(crate) fn db(&self) -> &'db ::salsa::Db {
        self.db
    }

    pub(crate) fn token_storage(&self) -> &LxTokenStorage {
        self.token_storage
    }

    pub(crate) fn ast_arena(&self) -> LxAstArenaRef<'db> {
        self.ast_arena
    }

    pub(crate) fn ast_token_idx_range_map(&self) -> &LxAstTokenIdxRangeMap {
        &self.ast_token_idx_range_map
    }

    pub(crate) fn annotations(&self) -> &VdAnnotations {
        self.annotations
    }

    pub(crate) fn default_resolution_table(&self) -> &VdDefaultGlobalResolutionTable {
        self.default_resolution_table
    }

    pub(crate) fn expr_arena(&self) -> &VdSynExprArena {
        &self.expr_arena
    }

    pub(crate) fn phrase_arena(&self) -> &VdSynPhraseArena {
        &self.phrase_arena
    }

    pub(crate) fn clause_arena(&self) -> &VdSynClauseArena {
        &self.clause_arena
    }

    pub(crate) fn sentence_arena(&self) -> &VdSynSentenceArena {
        &self.sentence_arena
    }
}

impl<'db> VdSynExprBuilder<'db> {
    pub(crate) fn peek_new_division(
        &self,
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
    ) -> Option<()> {
        match self.ast_arena()[*asts.peek()?] {
            LxRoseAstData::CompleteCommand { command_path, .. }
                if let Some(VdCompleteCommandGlobalResolution::NewDivision(_)) = self
                    .default_resolution_table()
                    .resolve_complete_command(command_path) =>
            {
                Some(())
            }
            _ => None,
        }
    }
}

/// # actions
impl<'db> VdSynExprBuilder<'db> {
    pub(crate) fn alloc_expr(&mut self, data: VdSynExprData) -> VdSynExprIdx {
        self.expr_arena.alloc_one(data)
    }

    pub(crate) fn alloc_exprs(
        &mut self,
        data: impl IntoIterator<Item = VdSynExprData>,
    ) -> VdSynExprIdxRange {
        self.expr_arena.alloc_batch(data)
    }

    pub(crate) fn alloc_phrase(&mut self, data: VdSynPhraseData) -> VdSynPhraseIdx {
        self.phrase_arena.alloc_one(data)
    }

    pub(crate) fn alloc_phrases(&mut self, data: Vec<VdSynPhraseData>) -> VdSynPhraseIdxRange {
        self.phrase_arena.alloc_batch(data)
    }

    pub(crate) fn alloc_clause(&mut self, data: VdSynClauseData) -> VdSynClauseIdx {
        self.clause_arena.alloc_one(data)
    }

    pub(crate) fn alloc_clauses(&mut self, data: Vec<VdSynClauseData>) -> VdSynClauseIdxRange {
        self.clause_arena.alloc_batch(data)
    }

    pub(crate) fn alloc_sentence(&mut self, data: VdSynSentenceData) -> VdSynSentenceIdx {
        self.sentence_arena.alloc_one(data)
    }

    pub(crate) fn alloc_sentences(
        &mut self,
        data: Vec<VdSynSentenceData>,
    ) -> VdSynSentenceIdxRange {
        self.sentence_arena.alloc_batch(data)
    }

    pub(crate) fn alloc_stmt(&mut self, data: VdSynStmtData) -> VdSynStmtIdx {
        self.stmt_arena.alloc_one(data)
    }

    pub(crate) fn alloc_stmts(&mut self, data: Vec<VdSynStmtData>) -> VdSynStmtIdxRange {
        self.stmt_arena.alloc_batch(data)
    }

    pub(crate) fn alloc_divisions(
        &mut self,
        data: Vec<VdSynDivisionData>,
    ) -> VdSynDivisionIdxRange {
        self.division_arena.alloc_batch(data)
    }

    // pub fn finish_to_region_data(self) -> VdSynExprRegionData {
    //     let (
    //         expr_arena,
    //         phrase_arena,
    //         clause_arena,
    //         sentence_arena,
    //         stmt_arena,
    //         division_arena,
    //         symbol_defns,
    //         symbol_resolutions,
    //     ) = self.finish_with_symbols();
    //     VdSynExprRegionData::new(
    //         expr_arena,
    //         phrase_arena,
    //         clause_arena,
    //         sentence_arena,
    //         stmt_arena,
    //         division_arena,
    //         symbol_defns,
    //         symbol_resolutions,
    //     )
    // }

    pub(crate) fn finish_without_symbols(
        self,
    ) -> (
        VdSynExprArena,
        VdSynPhraseArena,
        VdSynClauseArena,
        VdSynSentenceArena,
        VdSynStmtArena,
        VdSynDivisionArena,
    ) {
        (
            self.expr_arena,
            self.phrase_arena,
            self.clause_arena,
            self.sentence_arena,
            self.stmt_arena,
            self.division_arena,
        )
    }

    pub(crate) fn finish_with(
        self,
        output: impl IsVdSynOutput,
    ) -> (
        VdSynExprArena,
        VdSynPhraseArena,
        VdSynClauseArena,
        VdSynSentenceArena,
        VdSynStmtArena,
        VdSynDivisionArena,
        VdSynExprTokenIdxRangeMap,
        VdSynPhraseTokenIdxRangeMap,
        VdSynClauseTokenIdxRangeMap,
        VdSynSentenceTokenIdxRangeMap,
        VdSynStmtTokenIdxRangeMap,
        VdSynDivisionTokenIdxRangeMap,
        VdSynExprEntityTreeNode,
        VdSynStmtMap<VdSynExprEntityTreeNode>,
        VdSynDivisionMap<VdSynExprEntityTreeNode>,
        VdSynSymbolLocalDefnStorage,
        VdSynSymbolResolutionsTable,
    ) {
        let (
            expr_range_map,
            phrase_range_map,
            clause_range_map,
            sentence_range_map,
            stmt_range_map,
            division_range_map,
        ) = calc_expr_range_map(
            self.db,
            &self.expr_arena,
            &self.phrase_arena,
            &self.clause_arena,
            &self.sentence_arena,
            &self.stmt_arena,
            &self.division_arena,
        );
        let (root_node, stmt_entity_tree_node_map, division_entity_tree_node_map) =
            build_entity_tree_with(
                self.db,
                self.file_path,
                self.stmt_arena.as_arena_ref(),
                self.division_arena.as_arena_ref(),
                output,
            );
        let (symbol_defns, symbol_resolutions) = build_all_symbol_defns_and_resolutions_with(
            self.db,
            self.token_storage,
            self.ast_arena,
            self.ast_token_idx_range_map,
            self.annotations,
            self.default_resolution_table,
            self.expr_arena.as_arena_ref(),
            self.phrase_arena.as_arena_ref(),
            self.clause_arena.as_arena_ref(),
            self.sentence_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.division_arena.as_arena_ref(),
            &expr_range_map,
            &phrase_range_map,
            &clause_range_map,
            &sentence_range_map,
            &stmt_range_map,
            &division_range_map,
            &stmt_entity_tree_node_map,
            &division_entity_tree_node_map,
            output,
        );
        (
            self.expr_arena,
            self.phrase_arena,
            self.clause_arena,
            self.sentence_arena,
            self.stmt_arena,
            self.division_arena,
            expr_range_map,
            phrase_range_map,
            clause_range_map,
            sentence_range_map,
            stmt_range_map,
            division_range_map,
            root_node,
            stmt_entity_tree_node_map,
            division_entity_tree_node_map,
            symbol_defns,
            symbol_resolutions,
        )
    }
}
pub trait ToVdSyn<T> {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> T;
}

impl<R> ToVdSyn<Either<VdSynExprIdx, R>> for (LxTokenIdxRange, LxAstIdxRange)
where
    (LxTokenIdxRange, LxRoseAstIdxRange): ToVdSyn<R>,
{
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder) -> Either<VdSynExprIdx, R> {
        let (token_range, asts) = self;
        match asts {
            LxAstIdxRange::Lisp(asts) => todo!(),
            LxAstIdxRange::Math(asts) => Either::Left((token_range, asts).to_vd_syn(builder)),
            LxAstIdxRange::Root(arena_idx_range) => todo!(),
            LxAstIdxRange::Rose(asts) => Either::Right((token_range, asts).to_vd_syn(builder)),
        }
    }
}

pub trait FromToVdSyn<S> {
    fn from_to_vd_syn(s: S, builder: &mut VdSynExprBuilder) -> Self;
}

impl<S, T> FromToVdSyn<S> for T
where
    S: ToVdSyn<T>,
{
    fn from_to_vd_syn(s: S, builder: &mut VdSynExprBuilder) -> Self {
        s.to_vd_syn(builder)
    }
}

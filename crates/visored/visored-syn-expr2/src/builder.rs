mod debug;

use crate::{
    block::VdSynBlockMap, division::VdSynDivisionMap, entity_tree::VdSynExprEntityTreeNode,
    environment::VdSynExprVibe, sentence::VdSynSentenceEntry,
};
use crate::{
    block::{VdSynBlockArena, VdSynBlockData, VdSynBlockIdx, VdSynBlockIdxRange},
    clause::{VdSynClauseArena, VdSynClauseData, VdSynClauseIdx, VdSynClauseIdxRange},
    division::{VdSynDivisionArena, VdSynDivisionData, VdSynDivisionIdxRange},
    entity_tree::build_entity_tree_with,
    expr::{VdSynExprArena, VdSynExprData, VdSynExprIdx, VdSynExprIdxRange},
    helpers::tracker::IsVdSynOutput,
    phrase::{VdSynPhraseArena, VdSynPhraseData, VdSynPhraseIdx, VdSynPhraseIdxRange},
    range::*,
    region::VdSynExprRegionData,
    sentence::{VdSynSentenceArena, VdSynSentenceData, VdSynSentenceIdx, VdSynSentenceIdxRange},
    symbol::{
        build_all_symbol_defns_and_resolutions_with, builder::VdSynSymbolBuilder,
        local_defn::VdSynSymbolLocalDefnStorage, resolution::VdSynSymbolResolutionsTable,
    },
};
use either::*;
use eterned::db::EternerDb;
use latex_ast::{
    ast::{
        rose::{LxRoseAstData, LxRoseAstIdx, LxRoseAstIdxRange},
        LxAstArena, LxAstArenaRef, LxAstIdxRange,
    },
    range::LxAstTokenIdxRangeMap,
};
use latex_token::{idx::LxTokenIdxRange, storage::LxTokenStorage};
use latex_vfs::path::LxFilePath;
use sealed::sealed;
use snl_prelude::mode::SnlMode;
use std::{iter::Peekable, sync::Mutex};
use visored_annotation::annotations::VdAnnotations;
use visored_entity_path::module::VdModulePath;
use visored_global_resolution::{
    default_table::VdDefaultGlobalResolutionTable,
    resolution::command::VdCompleteCommandGlobalResolution,
};
use visored_models::VdModels;

pub struct VdSynExprBuilder<'db> {
    db: &'db EternerDb,
    content: &'db str,
    file_path: LxFilePath,
    token_storage: &'db LxTokenStorage,
    ast_arena: LxAstArenaRef<'db>,
    ast_token_idx_range_map: &'db LxAstTokenIdxRangeMap,
    annotations: &'db VdAnnotations,
    default_global_resolution_table: &'db VdDefaultGlobalResolutionTable,
    models: &'db VdModels,
    expr_arena: Mutex<VdSynExprArena>,
    phrase_arena: Mutex<VdSynPhraseArena>,
    clause_arena: Mutex<VdSynClauseArena>,
    sentence_arena: Mutex<VdSynSentenceArena>,
    stmt_arena: Mutex<VdSynBlockArena>,
    division_arena: Mutex<VdSynDivisionArena>,
}

/// # constructor
impl<'db> VdSynExprBuilder<'db> {
    pub fn new(
        db: &'db EternerDb,
        content: &'db str,
        file_path: LxFilePath,
        token_storage: &'db LxTokenStorage,
        ast_arena: LxAstArenaRef<'db>,
        ast_token_idx_range_map: &'db LxAstTokenIdxRangeMap,
        annotations: &'db VdAnnotations,
        default_global_resolution_table: &'db VdDefaultGlobalResolutionTable,
        models: &'db VdModels,
    ) -> Self {
        Self {
            db,
            content,
            file_path,
            token_storage,
            ast_arena,
            ast_token_idx_range_map,
            annotations,
            default_global_resolution_table,
            models,
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
    pub(crate) fn db(&self) -> &'db EternerDb {
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
        self.default_global_resolution_table
    }

    pub(crate) fn with_expr_arena<R>(&self, f: impl FnOnce(&VdSynExprArena) -> R) -> R {
        f(&self.expr_arena.lock().unwrap())
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
        self.expr_arena.lock().unwrap().alloc_one(data)
    }

    pub(crate) fn alloc_exprs(
        &mut self,
        data: impl IntoIterator<Item = VdSynExprData>,
    ) -> VdSynExprIdxRange {
        self.expr_arena.lock().unwrap().alloc_batch(data)
    }

    pub(crate) fn alloc_phrase(&mut self, data: VdSynPhraseData) -> VdSynPhraseIdx {
        self.phrase_arena.lock().unwrap().alloc_one(data)
    }

    pub(crate) fn alloc_phrases(&mut self, data: Vec<VdSynPhraseData>) -> VdSynPhraseIdxRange {
        self.phrase_arena.lock().unwrap().alloc_batch(data)
    }

    pub(crate) fn alloc_clause(&mut self, data: VdSynClauseData) -> VdSynClauseIdx {
        self.clause_arena.lock().unwrap().alloc_one(data)
    }

    pub(crate) fn alloc_clauses(&mut self, data: Vec<VdSynClauseData>) -> VdSynClauseIdxRange {
        self.clause_arena.lock().unwrap().alloc_batch(data)
    }

    pub(crate) fn alloc_sentence(&mut self, data: VdSynSentenceEntry) -> VdSynSentenceIdx {
        self.sentence_arena.lock().unwrap().alloc_one(data)
    }

    pub(crate) fn alloc_sentences(
        &mut self,
        data: Vec<VdSynSentenceEntry>,
    ) -> VdSynSentenceIdxRange {
        self.sentence_arena.lock().unwrap().alloc_batch(data)
    }

    pub(crate) fn alloc_stmt(&mut self, data: VdSynBlockData) -> VdSynBlockIdx {
        self.stmt_arena.lock().unwrap().alloc_one(data)
    }

    pub(crate) fn alloc_stmts(&mut self, data: Vec<VdSynBlockData>) -> VdSynBlockIdxRange {
        self.stmt_arena.lock().unwrap().alloc_batch(data)
    }

    pub(crate) fn alloc_divisions(
        &mut self,
        data: Vec<VdSynDivisionData>,
    ) -> VdSynDivisionIdxRange {
        self.division_arena.lock().unwrap().alloc_batch(data)
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
        VdSynBlockArena,
        VdSynDivisionArena,
    ) {
        (
            self.expr_arena.into_inner().unwrap(),
            self.phrase_arena.into_inner().unwrap(),
            self.clause_arena.into_inner().unwrap(),
            self.sentence_arena.into_inner().unwrap(),
            self.stmt_arena.into_inner().unwrap(),
            self.division_arena.into_inner().unwrap(),
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
        VdSynBlockArena,
        VdSynDivisionArena,
        VdSynExprTokenIdxRangeMap,
        VdSynPhraseTokenIdxRangeMap,
        VdSynClauseTokenIdxRangeMap,
        VdSynSentenceTokenIdxRangeMap,
        VdSynBlockTokenIdxRangeMap,
        VdSynDivisionTokenIdxRangeMap,
        VdSynExprEntityTreeNode,
        VdSynBlockMap<VdSynExprEntityTreeNode>,
        VdSynDivisionMap<VdSynExprEntityTreeNode>,
        VdSynSymbolLocalDefnStorage,
        VdSynSymbolResolutionsTable,
    ) {
        let expr_arena = self.expr_arena.into_inner().unwrap();
        let phrase_arena = self.phrase_arena.into_inner().unwrap();
        let clause_arena = self.clause_arena.into_inner().unwrap();
        let sentence_arena = self.sentence_arena.into_inner().unwrap();
        let stmt_arena = self.stmt_arena.into_inner().unwrap();
        let division_arena = self.division_arena.into_inner().unwrap();
        let (
            expr_range_map,
            phrase_range_map,
            clause_range_map,
            sentence_range_map,
            stmt_range_map,
            division_range_map,
        ) = calc_expr_range_map(
            &expr_arena,
            &phrase_arena,
            &clause_arena,
            &sentence_arena,
            &stmt_arena,
            &division_arena,
        );
        let (root_node, stmt_entity_tree_node_map, division_entity_tree_node_map) =
            build_entity_tree_with(
                self.db,
                self.default_global_resolution_table,
                self.file_path,
                stmt_arena.as_arena_ref(),
                division_arena.as_arena_ref(),
                output,
            );
        let (symbol_defns, symbol_resolutions) = build_all_symbol_defns_and_resolutions_with(
            self.db,
            self.token_storage,
            self.ast_arena,
            self.ast_token_idx_range_map,
            self.annotations,
            self.default_global_resolution_table,
            expr_arena.as_arena_ref(),
            phrase_arena.as_arena_ref(),
            clause_arena.as_arena_ref(),
            sentence_arena.as_arena_ref(),
            stmt_arena.as_arena_ref(),
            division_arena.as_arena_ref(),
            &expr_range_map,
            &phrase_range_map,
            &clause_range_map,
            &sentence_range_map,
            &stmt_range_map,
            &division_range_map,
            &root_node,
            &stmt_entity_tree_node_map,
            &division_entity_tree_node_map,
            output,
        );
        (
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
            root_node,
            stmt_entity_tree_node_map,
            division_entity_tree_node_map,
            symbol_defns,
            symbol_resolutions,
        )
    }
}
pub trait ToVdSyn<T> {
    fn to_vd_syn(self, builder: &mut VdSynExprBuilder, vibe: VdSynExprVibe) -> T;
}

pub trait FromToVdSyn<S> {
    fn from_to_vd_syn(s: S, builder: &mut VdSynExprBuilder, vibe: VdSynExprVibe) -> Self;
}

impl<S, T> FromToVdSyn<S> for T
where
    S: ToVdSyn<T>,
{
    fn from_to_vd_syn(s: S, builder: &mut VdSynExprBuilder, vibe: VdSynExprVibe) -> Self {
        s.to_vd_syn(builder, vibe)
    }
}

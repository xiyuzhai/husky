mod debug;

use eterned::db::EternerDb;
use latex_token::{idx::LxTokenIdxRange, storage::LxTokenStorage};
use visored_annotation::annotations::VdAnnotations;
use visored_global_dispatch::default_table::VdDefaultGlobalDispatchTable;
use visored_global_resolution::default_table::VdDefaultGlobalResolutionTable;
use visored_syn_expr::{
    block::{VdSynBlockArenaRef, VdSynBlockIdx, VdSynBlockMap},
    clause::{
        r#let::VdSynLetClauseResolution, VdSynClauseArenaRef, VdSynClauseIdx, VdSynClauseMap,
    },
    division::{VdSynDivisionArenaRef, VdSynDivisionIdx, VdSynDivisionMap},
    entity_tree::VdSynExprEntityTreeNode,
    expr::{VdSynExprArenaRef, VdSynExprIdx, VdSynExprMap},
    phrase::{VdSynPhraseArenaRef, VdSynPhraseIdx, VdSynPhraseMap},
    range::VdSynExprTokenIdxRange,
    sentence::{VdSynSentenceArenaRef, VdSynSentenceIdx, VdSynSentenceMap},
    symbol::{local_defn::VdSynSymbolLocalDefnStorage, resolution::VdSynSymbolResolutionsTable},
};
use visored_term::{
    menu::{vd_ty_menu, VdTypeMenu},
    term::VdTerm,
    ty::{table::VdItemPathZfcTypeTable, VdType},
};

use crate::{
    block::{
        VdSemBlockArena, VdSemBlockArenaRef, VdSemBlockData, VdSemBlockEntry, VdSemBlockIdx,
        VdSemBlockIdxRange,
    },
    clause::{
        VdSemClauseArena, VdSemClauseArenaRef, VdSemClauseData, VdSemClauseEntry, VdSemClauseIdx,
        VdSemClauseIdxRange,
    },
    division::{
        VdSemDivisionArena, VdSemDivisionArenaRef, VdSemDivisionData, VdSemDivisionEntry,
        VdSemDivisionIdx, VdSemDivisionIdxRange,
    },
    expr::{
        VdSemExprArena, VdSemExprArenaRef, VdSemExprData, VdSemExprEntry, VdSemExprIdx,
        VdSemExprIdxRange,
    },
    helpers::latex_fmt::VdSemExprLaTeXFormatter,
    phrase::{VdSemPhraseArena, VdSemPhraseArenaRef, VdSemPhraseData, VdSemPhraseIdx},
    sentence::{
        VdSemSentenceArena, VdSemSentenceArenaRef, VdSemSentenceData, VdSemSentenceIdx,
        VdSemSentenceIdxRange,
    },
    sheet::VdSemExprSheetData,
    symbol::local_defn::{
        storage::VdSemSymbolLocalDefnStorage, VdSemSymbolLocalDefnData, VdSemSymbolLocalDefnIdx,
    },
};

pub(crate) struct VdSemExprBuilder<'a> {
    db: &'a EternerDb,
    content: &'a str,
    token_storage: &'a LxTokenStorage,
    annotations: &'a VdAnnotations,
    default_resolution_table: &'a VdDefaultGlobalResolutionTable,
    syn_expr_arena: VdSynExprArenaRef<'a>,
    syn_phrase_arena: VdSynPhraseArenaRef<'a>,
    syn_clause_arena: VdSynClauseArenaRef<'a>,
    syn_sentence_arena: VdSynSentenceArenaRef<'a>,
    syn_stmt_arena: VdSynBlockArenaRef<'a>,
    syn_division_arena: VdSynDivisionArenaRef<'a>,
    syn_expr_range_map: &'a VdSynExprMap<VdSynExprTokenIdxRange>,
    syn_let_clause_resolutions: &'a VdSynClauseMap<VdSynLetClauseResolution>,
    syn_symbol_resolution_table: &'a VdSynSymbolResolutionsTable,
    vd_ty_menu: &'a VdTypeMenu,
    item_path_zfc_ty_table: &'a VdItemPathZfcTypeTable,
    default_global_dispatch_table: &'a VdDefaultGlobalDispatchTable,
    stmt_entity_tree_node_map: &'a VdSynBlockMap<VdSynExprEntityTreeNode>,
    division_entity_tree_node_map: &'a VdSynDivisionMap<VdSynExprEntityTreeNode>,
    expr_arena: VdSemExprArena,
    phrase_arena: VdSemPhraseArena,
    clause_arena: VdSemClauseArena,
    sentence_arena: VdSemSentenceArena,
    stmt_arena: VdSemBlockArena,
    division_arena: VdSemDivisionArena,
    /// only needs to keep track of syn to sem expr map because of possible repetition
    syn_to_sem_expr_map: VdSynExprMap<VdSemExprIdx>,
    symbol_local_defn_storage: VdSemSymbolLocalDefnStorage,
}

impl<'a> VdSemExprBuilder<'a> {
    pub(crate) fn new(
        db: &'a EternerDb,
        content: &'a str,
        token_storage: &'a LxTokenStorage,
        annotations: &'a VdAnnotations,
        default_resolution_table: &'a VdDefaultGlobalResolutionTable,
        syn_expr_arena: VdSynExprArenaRef<'a>,
        syn_phrase_arena: VdSynPhraseArenaRef<'a>,
        syn_clause_arena: VdSynClauseArenaRef<'a>,
        syn_sentence_arena: VdSynSentenceArenaRef<'a>,
        syn_stmt_arena: VdSynBlockArenaRef<'a>,
        syn_division_arena: VdSynDivisionArenaRef<'a>,
        syn_expr_range_map: &'a VdSynExprMap<VdSynExprTokenIdxRange>,
        syn_let_clause_resolutions: &'a VdSynClauseMap<VdSynLetClauseResolution>,
        syn_symbol_local_defn_storage: &'a VdSynSymbolLocalDefnStorage,
        syn_symbol_resolution_table: &'a VdSynSymbolResolutionsTable,
        item_path_zfc_ty_table: &'a VdItemPathZfcTypeTable,
        default_global_dispatch_table: &'a VdDefaultGlobalDispatchTable,
        stmt_entity_tree_node_map: &'a VdSynBlockMap<VdSynExprEntityTreeNode>,
        division_entity_tree_node_map: &'a VdSynDivisionMap<VdSynExprEntityTreeNode>,
    ) -> Self {
        let mut slf = Self {
            db,
            content,
            token_storage,
            annotations,
            default_resolution_table,
            syn_expr_arena,
            syn_phrase_arena,
            syn_clause_arena,
            syn_sentence_arena,
            syn_stmt_arena,
            syn_division_arena,
            syn_expr_range_map,
            symbol_local_defn_storage: VdSemSymbolLocalDefnStorage::new_empty(),
            syn_let_clause_resolutions,
            syn_symbol_resolution_table,
            vd_ty_menu: vd_ty_menu(db),
            item_path_zfc_ty_table,
            default_global_dispatch_table,
            stmt_entity_tree_node_map,
            division_entity_tree_node_map,
            expr_arena: VdSemExprArena::default(),
            phrase_arena: VdSemPhraseArena::default(),
            clause_arena: VdSemClauseArena::default(),
            sentence_arena: VdSemSentenceArena::default(),
            stmt_arena: VdSemBlockArena::default(),
            division_arena: VdSemDivisionArena::default(),
            syn_to_sem_expr_map: VdSynExprMap::new2(syn_expr_arena),
        };
        // make sure symbols are built
        // expressions needed will be built in the process
        // be careful, bugs could lead to infinite loops
        slf.build_symbol_local_defns(syn_symbol_local_defn_storage);
        slf
    }
}

/// # getters
impl<'a> VdSemExprBuilder<'a> {
    pub(crate) fn db(&self) -> &'a EternerDb {
        self.db
    }

    pub(crate) fn content(&self) -> &'a str {
        self.content
    }

    pub fn syn_expr_arena(&self) -> VdSynExprArenaRef<'a> {
        self.syn_expr_arena
    }

    pub fn syn_phrase_arena(&self) -> VdSynPhraseArenaRef<'a> {
        self.syn_phrase_arena
    }

    pub fn syn_clause_arena(&self) -> VdSynClauseArenaRef<'a> {
        self.syn_clause_arena
    }

    pub fn syn_sentence_arena(&self) -> VdSynSentenceArenaRef<'a> {
        self.syn_sentence_arena
    }

    pub fn syn_stmt_arena(&self) -> VdSynBlockArenaRef<'a> {
        self.syn_stmt_arena
    }

    pub fn syn_division_arena(&self) -> VdSynDivisionArenaRef<'a> {
        self.syn_division_arena
    }

    pub fn syn_symbol_resolution_table(&self) -> &'a VdSynSymbolResolutionsTable {
        self.syn_symbol_resolution_table
    }

    pub fn syn_let_clause_resolutions(&self) -> &'a VdSynClauseMap<VdSynLetClauseResolution> {
        self.syn_let_clause_resolutions
    }

    pub fn symbol_local_defn_storage(&self) -> &VdSemSymbolLocalDefnStorage {
        &self.symbol_local_defn_storage
    }

    pub(crate) fn item_path_zfc_type_table(&self) -> &'a VdItemPathZfcTypeTable {
        self.item_path_zfc_ty_table
    }

    pub(crate) fn default_global_dispatch_table(&self) -> &'a VdDefaultGlobalDispatchTable {
        self.default_global_dispatch_table
    }

    pub(crate) fn ty_menu(&self) -> &'a VdTypeMenu {
        self.vd_ty_menu
    }

    pub(crate) fn expr_arena(&self) -> VdSemExprArenaRef {
        self.expr_arena.as_arena_ref()
    }

    pub(crate) fn phrase_arena(&self) -> VdSemPhraseArenaRef {
        self.phrase_arena.as_arena_ref()
    }

    pub(crate) fn clause_arena(&self) -> VdSemClauseArenaRef {
        self.clause_arena.as_arena_ref()
    }

    pub(crate) fn sentence_arena(&self) -> VdSemSentenceArenaRef {
        self.sentence_arena.as_arena_ref()
    }

    pub(crate) fn stmt_arena(&self) -> VdSemBlockArenaRef {
        self.stmt_arena.as_arena_ref()
    }

    pub(crate) fn division_arena(&self) -> VdSemDivisionArenaRef {
        self.division_arena.as_arena_ref()
    }

    pub(crate) fn syn_to_sem_expr_map(&self) -> &VdSynExprMap<VdSemExprIdx> {
        &self.syn_to_sem_expr_map
    }

    pub(crate) fn stmt_entity_tree_node_map(&self) -> &VdSynBlockMap<VdSynExprEntityTreeNode> {
        self.stmt_entity_tree_node_map
    }

    pub(crate) fn division_entity_tree_node_map(
        &self,
    ) -> &VdSynDivisionMap<VdSynExprEntityTreeNode> {
        self.division_entity_tree_node_map
    }
}

impl<'db> VdSemExprBuilder<'db> {
    pub(crate) fn alloc_local_defns(&mut self, defns: Vec<VdSemSymbolLocalDefnData>) {
        self.symbol_local_defn_storage.set_defns(defns);
    }

    pub(crate) fn set_local_defn_ty(&mut self, local_defn: VdSemSymbolLocalDefnIdx, ty: VdType) {
        self.symbol_local_defn_storage
            .set_local_defn_ty(local_defn, ty);
    }

    pub(crate) fn alloc_expr(
        &mut self,
        syn_expr: VdSynExprIdx,
        mut entry: VdSemExprEntry,
        expected_ty: Option<VdType>,
    ) -> VdSemExprIdx {
        if let Some(expected_ty) = expected_ty {
            entry.set_expected_ty(expected_ty);
        }
        let expr = self.expr_arena.alloc_one(entry);
        self.syn_to_sem_expr_map.insert(syn_expr, expr);
        expr
    }

    /// no need to keep track of syn to sem expr map
    pub(crate) fn alloc_exprs(
        &mut self,
        exprs: impl IntoIterator<Item = VdSemExprEntry>,
    ) -> VdSemExprIdxRange {
        self.expr_arena.alloc_many(exprs)
    }

    pub(crate) fn alloc_phrase(
        &mut self,
        syn_phrase: VdSynPhraseIdx,
        data: VdSemPhraseData,
    ) -> VdSemPhraseIdx {
        self.phrase_arena.alloc_one(data)
    }

    pub(crate) fn alloc_clauses(&mut self, clauses: Vec<VdSemClauseEntry>) -> VdSemClauseIdxRange {
        self.clause_arena.alloc_many(clauses)
    }

    pub(crate) fn alloc_sentences(
        &mut self,
        sentences: Vec<VdSemSentenceData>,
    ) -> VdSemSentenceIdxRange {
        self.sentence_arena.alloc_many(sentences)
    }

    pub(crate) fn alloc_stmts(&mut self, stmts: Vec<VdSemBlockEntry>) -> VdSemBlockIdxRange {
        self.stmt_arena.alloc_many(stmts)
    }

    pub(crate) fn alloc_division(
        &mut self,
        syn_division: VdSynDivisionIdx,
        data: VdSemDivisionData,
    ) -> VdSemDivisionIdx {
        let module_path = self.division_entity_tree_node_map[syn_division].module_path();
        self.division_arena
            .alloc_one(VdSemDivisionEntry::new(data, module_path))
    }

    pub(crate) fn alloc_divisions(
        &mut self,
        divisions: Vec<VdSemDivisionEntry>,
    ) -> VdSemDivisionIdxRange {
        self.division_arena.alloc_many(divisions)
    }

    pub(crate) fn infer_expr_term(&mut self, expr: VdSemExprIdx) -> VdTerm {
        let term = self.calc_expr_term(expr);
        self.expr_arena.update(expr, |entry| entry.set_term(term));
        term
    }

    pub(crate) fn finish_into_region_data(self) -> VdSemExprSheetData {
        VdSemExprSheetData::new(
            self.expr_arena,
            self.phrase_arena,
            self.clause_arena,
            self.sentence_arena,
            self.stmt_arena,
            self.division_arena,
            self.symbol_local_defn_storage,
        )
    }

    pub(crate) fn finish(
        self,
    ) -> (
        VdSemExprArena,
        VdSemPhraseArena,
        VdSemClauseArena,
        VdSemSentenceArena,
        VdSemBlockArena,
        VdSemDivisionArena,
        VdSemSymbolLocalDefnStorage,
    ) {
        (
            self.expr_arena,
            self.phrase_arena,
            self.clause_arena,
            self.sentence_arena,
            self.stmt_arena,
            self.division_arena,
            self.symbol_local_defn_storage,
        )
    }
}

use crate::{
    expr::{VdMirExprArena, VdMirExprArenaRef, VdMirExprData, VdMirExprIdx, VdMirExprIdxRange},
    region::VdMirExprRegionData,
    stmt::{VdMirStmtArena, VdMirStmtArenaRef, VdMirStmtData, VdMirStmtIdxRange},
    symbol::local_defn::{storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnData},
};
use visored_sem_expr::{
    clause::VdSemClauseArenaRef, division::VdSemDivisionArenaRef, expr::VdSemExprArenaRef,
    phrase::VdSemPhraseArenaRef, region::VdSemExprRegionData, sentence::VdSemSentenceArenaRef,
    stmt::VdSemStmtArenaRef, symbol::local_defn::storage::VdSemSymbolLocalDefnStorage,
};

pub struct VdMirExprBuilder<'db> {
    db: &'db ::salsa::Db,
    sem_expr_arena: VdSemExprArenaRef<'db>,
    sem_phrase_arena: VdSemPhraseArenaRef<'db>,
    sem_clause_arena: VdSemClauseArenaRef<'db>,
    sem_sentence_arena: VdSemSentenceArenaRef<'db>,
    sem_stmt_arena: VdSemStmtArenaRef<'db>,
    sem_division_arena: VdSemDivisionArenaRef<'db>,
    expr_arena: VdMirExprArena,
    stmt_arena: VdMirStmtArena,
    symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
}

impl<'db> VdMirExprBuilder<'db> {
    pub fn new0(db: &'db ::salsa::Db, vd_sem_expr_region_data: &'db VdSemExprRegionData) -> Self {
        Self::new(
            db,
            vd_sem_expr_region_data.expr_arena(),
            vd_sem_expr_region_data.phrase_arena(),
            vd_sem_expr_region_data.clause_arena(),
            vd_sem_expr_region_data.sentence_arena(),
            vd_sem_expr_region_data.stmt_arena(),
            vd_sem_expr_region_data.division_arena(),
            vd_sem_expr_region_data.sem_symbol_local_defn_storage(),
        )
    }

    pub fn new(
        db: &'db ::salsa::Db,
        sem_expr_arena: VdSemExprArenaRef<'db>,
        sem_phrase_arena: VdSemPhraseArenaRef<'db>,
        sem_clause_arena: VdSemClauseArenaRef<'db>,
        sem_sentence_arena: VdSemSentenceArenaRef<'db>,
        sem_stmt_arena: VdSemStmtArenaRef<'db>,
        sem_division_arena: VdSemDivisionArenaRef<'db>,
        sem_symbol_local_defn_storage: &VdSemSymbolLocalDefnStorage,
    ) -> Self {
        let mut slf = Self {
            db,
            sem_expr_arena,
            sem_phrase_arena,
            sem_clause_arena,
            sem_sentence_arena,
            sem_stmt_arena,
            sem_division_arena,
            expr_arena: VdMirExprArena::default(),
            stmt_arena: VdMirStmtArena::default(),
            symbol_local_defn_storage: VdMirSymbolLocalDefnStorage::new_empty(),
        };
        slf.build_symbol_local_defns(sem_symbol_local_defn_storage);
        slf
    }
}

impl<'db> VdMirExprBuilder<'db> {
    pub fn sem_expr_arena(&self) -> VdSemExprArenaRef<'db> {
        self.sem_expr_arena
    }

    pub fn sem_phrase_arena(&self) -> VdSemPhraseArenaRef<'db> {
        self.sem_phrase_arena
    }

    pub fn sem_clause_arena(&self) -> VdSemClauseArenaRef<'db> {
        self.sem_clause_arena
    }

    pub fn sem_sentence_arena(&self) -> VdSemSentenceArenaRef<'db> {
        self.sem_sentence_arena
    }

    pub fn sem_stmt_arena(&self) -> VdSemStmtArenaRef<'db> {
        self.sem_stmt_arena
    }

    pub fn sem_division_arena(&self) -> VdSemDivisionArenaRef<'db> {
        self.sem_division_arena
    }

    pub fn expr_arena(&self) -> VdMirExprArenaRef {
        self.expr_arena.as_arena_ref()
    }

    pub fn stmt_arena(&self) -> VdMirStmtArenaRef {
        self.stmt_arena.as_arena_ref()
    }
}

/// # actions
impl<'db> VdMirExprBuilder<'db> {
    pub(crate) fn alloc_expr(&mut self, data: VdMirExprData) -> VdMirExprIdx {
        self.expr_arena.alloc_one(data)
    }

    pub(crate) fn alloc_exprs(
        &mut self,
        data: impl IntoIterator<Item = VdMirExprData>,
    ) -> VdMirExprIdxRange {
        self.expr_arena.alloc_batch(data)
    }

    pub(crate) fn alloc_stmts(
        &mut self,
        data: impl IntoIterator<Item = VdMirStmtData>,
    ) -> VdMirStmtIdxRange {
        self.stmt_arena.alloc_batch(data)
    }

    pub(crate) fn alloc_symbol_local_defns(&mut self, data: Vec<VdMirSymbolLocalDefnData>) {
        self.symbol_local_defn_storage.set_defns(data);
    }

    pub fn finish_to_region_data(self) -> VdMirExprRegionData {
        VdMirExprRegionData::new(
            self.expr_arena,
            self.stmt_arena,
            self.symbol_local_defn_storage,
        )
    }

    pub fn finish(self) -> (VdMirExprArena, VdMirStmtArena, VdMirSymbolLocalDefnStorage) {
        (
            self.expr_arena,
            self.stmt_arena,
            self.symbol_local_defn_storage,
        )
    }
}

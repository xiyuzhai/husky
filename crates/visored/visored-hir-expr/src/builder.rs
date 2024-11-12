use crate::{
    expr::{VdHirExprArena, VdHirExprArenaRef, VdHirExprData, VdHirExprIdx, VdHirExprIdxRange},
    region::VdHirExprRegionData,
    stmt::{VdHirStmtArena, VdHirStmtArenaRef},
};
use visored_sem_expr::{
    clause::VdSemClauseArenaRef, division::VdSemDivisionArenaRef, expr::VdSemExprArenaRef,
    phrase::VdSemPhraseArenaRef, region::VdSemExprRegionData, sentence::VdSemSentenceArenaRef,
    stmt::VdSemStmtArenaRef,
};

pub struct VdHirExprBuilder<'db> {
    db: &'db ::salsa::Db,
    sem_expr_arena: VdSemExprArenaRef<'db>,
    sem_phrase_arena: VdSemPhraseArenaRef<'db>,
    sem_clause_arena: VdSemClauseArenaRef<'db>,
    sem_sentence_arena: VdSemSentenceArenaRef<'db>,
    sem_stmt_arena: VdSemStmtArenaRef<'db>,
    sem_division_arena: VdSemDivisionArenaRef<'db>,
    expr_arena: VdHirExprArena,
    stmt_arena: VdHirStmtArena,
}

impl<'db> VdHirExprBuilder<'db> {
    pub fn new0(db: &'db ::salsa::Db, vd_sem_expr_region_data: &'db VdSemExprRegionData) -> Self {
        Self {
            db,
            sem_expr_arena: vd_sem_expr_region_data.expr_arena(),
            sem_phrase_arena: vd_sem_expr_region_data.phrase_arena(),
            sem_clause_arena: vd_sem_expr_region_data.clause_arena(),
            sem_sentence_arena: vd_sem_expr_region_data.sentence_arena(),
            sem_stmt_arena: vd_sem_expr_region_data.stmt_arena(),
            sem_division_arena: vd_sem_expr_region_data.division_arena(),
            expr_arena: VdHirExprArena::default(),
            stmt_arena: VdHirStmtArena::default(),
        }
    }

    pub fn new(
        db: &'db ::salsa::Db,
        sem_expr_arena: VdSemExprArenaRef<'db>,
        sem_phrase_arena: VdSemPhraseArenaRef<'db>,
        sem_clause_arena: VdSemClauseArenaRef<'db>,
        sem_sentence_arena: VdSemSentenceArenaRef<'db>,
        sem_stmt_arena: VdSemStmtArenaRef<'db>,
        sem_division_arena: VdSemDivisionArenaRef<'db>,
    ) -> Self {
        Self {
            db,
            sem_expr_arena,
            sem_phrase_arena,
            sem_clause_arena,
            sem_sentence_arena,
            sem_stmt_arena,
            sem_division_arena,
            expr_arena: VdHirExprArena::default(),
            stmt_arena: VdHirStmtArena::default(),
        }
    }

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

    pub fn expr_arena(&self) -> VdHirExprArenaRef {
        self.expr_arena.as_arena_ref()
    }

    pub fn stmt_arena(&self) -> VdHirStmtArenaRef {
        self.stmt_arena.as_arena_ref()
    }
}

/// # actions
impl<'db> VdHirExprBuilder<'db> {
    pub(crate) fn alloc_expr(&mut self, data: VdHirExprData) -> VdHirExprIdx {
        self.expr_arena.alloc_one(data)
    }

    pub(crate) fn alloc_exprs(
        &mut self,
        data: impl IntoIterator<Item = VdHirExprData>,
    ) -> VdHirExprIdxRange {
        self.expr_arena.alloc_batch(data)
    }

    pub fn finish_to_region_data(self) -> VdHirExprRegionData {
        VdHirExprRegionData::new(self.expr_arena, self.stmt_arena)
    }

    pub fn finish(self) -> (VdHirExprArena, VdHirStmtArena) {
        (self.expr_arena, self.stmt_arena)
    }
}

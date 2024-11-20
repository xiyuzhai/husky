use crate::{
    clause::{VdSemClauseArena, VdSemClauseArenaRef, VdSemClauseData, VdSemClauseIdx},
    division::{VdSemDivisionArena, VdSemDivisionArenaRef},
    expr::{VdSemExprArena, VdSemExprArenaRef, VdSemExprData, VdSemExprIdx},
    helpers::latex_fmt::VdSemExprLaTeXFormatter,
    phrase::{VdSemPhraseArena, VdSemPhraseArenaRef, VdSemPhraseData, VdSemPhraseIdx},
    sentence::{VdSemSentenceArena, VdSemSentenceArenaRef, VdSemSentenceData, VdSemSentenceIdx},
    stmt::{VdSemStmtArena, VdSemStmtArenaRef},
    symbol::local_defn::storage::VdSemSymbolLocalDefnStorage,
};

pub struct VdSemExprRegionData {
    expr_arena: VdSemExprArena,
    phrase_arena: VdSemPhraseArena,
    clause_arena: VdSemClauseArena,
    sentence_arena: VdSemSentenceArena,
    stmt_arena: VdSemStmtArena,
    division_arena: VdSemDivisionArena,
    sem_symbol_local_defn_storage: VdSemSymbolLocalDefnStorage,
}

impl VdSemExprRegionData {
    pub(crate) fn new(
        expr_arena: VdSemExprArena,
        phrase_arena: VdSemPhraseArena,
        clause_arena: VdSemClauseArena,
        sentence_arena: VdSemSentenceArena,
        stmt_arena: VdSemStmtArena,
        division_arena: VdSemDivisionArena,
        sem_symbol_local_defn_storage: VdSemSymbolLocalDefnStorage,
    ) -> Self {
        Self {
            expr_arena,
            phrase_arena,
            clause_arena,
            sentence_arena,
            stmt_arena,
            division_arena,
            sem_symbol_local_defn_storage,
        }
    }

    pub fn expr_arena(&self) -> VdSemExprArenaRef {
        self.expr_arena.as_arena_ref()
    }

    pub fn phrase_arena(&self) -> VdSemPhraseArenaRef {
        self.phrase_arena.as_arena_ref()
    }

    pub fn clause_arena(&self) -> VdSemClauseArenaRef {
        self.clause_arena.as_arena_ref()
    }

    pub fn sentence_arena(&self) -> VdSemSentenceArenaRef {
        self.sentence_arena.as_arena_ref()
    }

    pub fn stmt_arena(&self) -> VdSemStmtArenaRef {
        self.stmt_arena.as_arena_ref()
    }

    pub fn division_arena(&self) -> VdSemDivisionArenaRef {
        self.division_arena.as_arena_ref()
    }

    pub fn sem_symbol_local_defn_storage(&self) -> &VdSemSymbolLocalDefnStorage {
        &self.sem_symbol_local_defn_storage
    }
}

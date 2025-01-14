use once_place::OncePlace;

use super::*;

pub struct VdMirExprRegionBuilder<'db> {
    input: &'db str,
    sem_expr_arena: VdSemExprArenaRef<'db>,
    sem_phrase_arena: VdSemPhraseArenaRef<'db>,
    sem_clause_arena: VdSemClauseArenaRef<'db>,
    sem_sentence_arena: VdSemSentenceArenaRef<'db>,
    sem_block_arena: VdSemBlockArenaRef<'db>,
    sem_division_arena: VdSemDivisionArenaRef<'db>,
    expr_arena: VdMirExprArena,
    stmt_arena: VdMirStmtArena,
    hint_arena: VdMirHintArena,
    symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
    source_map: VdMirRegionSourceMap,
}

impl<'db> VdMirExprRegionBuilder<'db> {
    pub fn new0(input: &'db str, sheet: &'db VdSemExprSheetData) -> Self {
        Self::new(
            input,
            sheet.expr_arena(),
            sheet.phrase_arena(),
            sheet.clause_arena(),
            sheet.sentence_arena(),
            sheet.stmt_arena(),
            sheet.division_arena(),
            sheet.sem_symbol_local_defn_storage(),
        )
    }

    pub fn new(
        input: &'db str,
        sem_expr_arena: VdSemExprArenaRef<'db>,
        sem_phrase_arena: VdSemPhraseArenaRef<'db>,
        sem_clause_arena: VdSemClauseArenaRef<'db>,
        sem_sentence_arena: VdSemSentenceArenaRef<'db>,
        sem_stmt_arena: VdSemBlockArenaRef<'db>,
        sem_division_arena: VdSemDivisionArenaRef<'db>,
        sem_symbol_local_defn_storage: &VdSemSymbolLocalDefnStorage,
    ) -> Self {
        let mut slf = Self {
            input,
            sem_expr_arena,
            sem_phrase_arena,
            sem_clause_arena,
            sem_sentence_arena,
            sem_block_arena: sem_stmt_arena,
            sem_division_arena,
            expr_arena: VdMirExprArena::default(),
            stmt_arena: VdMirStmtArena::default(),
            hint_arena: VdMirHintArena::default(),
            symbol_local_defn_storage: VdMirSymbolLocalDefnStorage::new_empty(),
            source_map: Default::default(),
        };
        // TODO: only build symbols that are used in the region
        slf.build_symbol_local_defns(sem_symbol_local_defn_storage);
        slf
    }
}

impl<'db> VdMirExprRegionBuilder<'db> {
    pub fn input(&self) -> &'db str {
        self.input
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

    pub fn sem_block_arena(&self) -> VdSemBlockArenaRef<'db> {
        self.sem_block_arena
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
impl<'db> VdMirExprRegionBuilder<'db> {
    pub(crate) fn alloc_expr(&mut self, entry: VdMirExprEntry) -> VdMirExprIdx {
        self.expr_arena.alloc_one(entry)
    }

    pub(crate) fn alloc_exprs(
        &mut self,
        entries: impl IntoIterator<Item = VdMirExprEntry>,
    ) -> VdMirExprIdxRange {
        self.expr_arena.alloc_many(entries)
    }

    pub(crate) fn alloc_stmts(&mut self, stmt_batch: VdMirStmtBatch) -> VdMirStmtIdxRange {
        let (mut entries, mut sources, goal) = stmt_batch.finish();
        if !entries.is_empty() {
            match *entries[0].data() {
                VdMirStmtData::Block { .. } => (),
                _ => {
                    entries.push(VdMirStmtEntry::new(VdMirStmtData::Qed {
                        goal_and_hypothesis_chunk_place: goal
                            .map(|goal| (goal, OncePlace::default())),
                    }));
                    sources.push(VdMirStmtSource::Qed);
                }
            }
        }
        let stmts = self.stmt_arena.alloc_many(entries);
        self.source_map.set_stmts(stmts, sources);
        stmts
    }

    pub(crate) fn alloc_tactics(
        &mut self,
        entries: impl IntoIterator<Item = VdMirHintEntry>,
        sources: impl IntoIterator<Item = VdMirHintSource>,
    ) -> VdMirHintIdxRange {
        let tactics = self.hint_arena.alloc_many(entries);
        self.source_map.set_tactics(tactics, sources);
        tactics
    }

    pub(crate) fn alloc_symbol_local_defns(&mut self, data: Vec<VdMirSymbolLocalDefnData>) {
        self.symbol_local_defn_storage.set_defns(data);
    }

    pub fn finish(
        self,
    ) -> (
        VdMirExprArena,
        VdMirStmtArena,
        VdMirHintArena,
        VdMirSymbolLocalDefnStorage,
        VdMirRegionSourceMap,
    ) {
        (
            self.expr_arena,
            self.stmt_arena,
            self.hint_arena,
            self.symbol_local_defn_storage,
            self.source_map,
        )
    }
}

use super::*;
use crate::{
    division::{
        VdMirDivisionArena, VdMirDivisionArenaRef, VdMirDivisionEntry, VdMirDivisionIdxRange,
    },
    region::{
        VdMirExprRegionArena, VdMirExprRegionArenaRef, VdMirExprRegionEntry, VdMirExprRegionIdx,
    },
};

pub struct VdMirExprSheetBuilder<'db> {
    input: &'db str,
    sem_block_arena: VdSemBlockArenaRef<'db>,
    sem_division_arena: VdSemDivisionArenaRef<'db>,
    region_arena: VdMirExprRegionArena,
    division_arena: VdMirDivisionArena,
}

impl<'db> VdMirExprSheetBuilder<'db> {
    pub fn new(input: &'db str, sheet: &'db VdSemExprSheetData) -> Self {
        Self {
            input,
            sem_block_arena: sheet.stmt_arena(),
            sem_division_arena: sheet.division_arena(),
            region_arena: VdMirExprRegionArena::default(),
            division_arena: VdMirDivisionArena::default(),
        }
    }
}

impl<'db> VdMirExprSheetBuilder<'db> {
    pub fn input(&self) -> &'db str {
        self.input
    }

    pub fn sem_block_arena(&self) -> VdSemBlockArenaRef<'db> {
        self.sem_block_arena
    }

    pub fn sem_division_arena(&self) -> VdSemDivisionArenaRef<'db> {
        self.sem_division_arena
    }

    pub fn region_arena(&self) -> VdMirExprRegionArenaRef {
        self.region_arena.as_arena_ref()
    }

    pub fn division_arena(&self) -> VdMirDivisionArenaRef {
        self.division_arena.as_arena_ref()
    }
}

/// # actions
impl<'db> VdMirExprSheetBuilder<'db> {
    pub(crate) fn alloc_region(&mut self, entry: VdMirExprRegionEntry) -> VdMirExprRegionIdx {
        self.region_arena.alloc_one(entry)
    }

    pub(crate) fn alloc_divisions(
        &mut self,
        entries: impl IntoIterator<Item = VdMirDivisionEntry>,
    ) -> VdMirDivisionIdxRange {
        self.division_arena.alloc_many(entries)
    }

    pub fn finish(self) -> (VdMirExprRegionArena, VdMirDivisionArena) {
        (self.region_arena, self.division_arena)
    }
}

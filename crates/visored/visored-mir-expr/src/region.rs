use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use visored_global_dispatch::default_table::VdDefaultGlobalDispatchTable;

use crate::{
    derivation::{VdMirDerivationArena, VdMirDerivationArenaRef},
    expr::{VdMirExprArena, VdMirExprArenaRef},
    hint::{VdMirHintArena, VdMirHintArenaRef, VdMirHintIdx},
    hypothesis::{VdMirHypothesisArena, VdMirHypothesisArenaRef, VdMirHypothesisIdx},
    stmt::{VdMirStmtArena, VdMirStmtArenaRef, VdMirStmtIdx},
    symbol::local_defn::storage::VdMirSymbolLocalDefnStorage,
};

pub struct VdMirExprRegionData {
    expr_arena: VdMirExprArena,
    stmt_arena: VdMirStmtArena,
    hint_arena: VdMirHintArena,
    hypothesis_arena: VdMirHypothesisArena,
    derivation_arena: VdMirDerivationArena,
    symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
}

pub struct VdMirExprRegionEntry {
    data: VdMirExprRegionData,
}

pub type VdMirExprRegionIdx = ArenaIdx<VdMirExprRegionEntry>;
pub type VdMirExprRegionIdxRange = ArenaIdxRange<VdMirExprRegionEntry>;
pub type VdMirExprRegionArena = Arena<VdMirExprRegionEntry>;
pub type VdMirExprRegionArenaRef<'a> = ArenaRef<'a, VdMirExprRegionEntry>;

impl VdMirExprRegionData {
    pub fn new(
        expr_arena: VdMirExprArena,
        stmt_arena: VdMirStmtArena,
        hint_arena: VdMirHintArena,
        hypothesis_arena: VdMirHypothesisArena,
        derivation_arena: VdMirDerivationArena,
        symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
    ) -> Self {
        Self {
            expr_arena,
            stmt_arena,
            hint_arena,
            hypothesis_arena,
            derivation_arena,
            symbol_local_defn_storage,
        }
    }
}

impl VdMirExprRegionData {
    pub fn expr_arena(&self) -> VdMirExprArenaRef {
        self.expr_arena.as_arena_ref()
    }

    pub fn stmt_arena(&self) -> VdMirStmtArenaRef {
        self.stmt_arena.as_arena_ref()
    }

    pub fn hint_arena(&self) -> VdMirHintArenaRef {
        self.hint_arena.as_arena_ref()
    }

    pub fn hypothesis_arena(&self) -> VdMirHypothesisArenaRef {
        self.hypothesis_arena.as_arena_ref()
    }

    pub fn derivation_arena(&self) -> VdMirDerivationArenaRef {
        self.derivation_arena.as_arena_ref()
    }

    pub fn symbol_local_defn_storage(&self) -> &VdMirSymbolLocalDefnStorage {
        &self.symbol_local_defn_storage
    }
}

#[derive(Clone, Copy)]
pub struct VdMirExprRegionDataRef<'a> {
    pub default_global_dispatch_table: &'a VdDefaultGlobalDispatchTable,
    pub expr_arena: VdMirExprArenaRef<'a>,
    pub stmt_arena: VdMirStmtArenaRef<'a>,
    pub hint_arena: VdMirHintArenaRef<'a>,
    pub symbol_local_defn_storage: &'a VdMirSymbolLocalDefnStorage,
}

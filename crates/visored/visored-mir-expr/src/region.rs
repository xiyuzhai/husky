use crate::{
    expr::{VdMirExprArena, VdMirExprArenaRef},
    stmt::{VdMirStmtArena, VdMirStmtArenaRef},
    symbol::local_defn::storage::VdMirSymbolLocalDefnStorage,
};

pub struct VdMirExprRegionData {
    expr_arena: VdMirExprArena,
    stmt_arena: VdMirStmtArena,
    symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
}

impl VdMirExprRegionData {
    pub fn new(
        expr_arena: VdMirExprArena,
        stmt_arena: VdMirStmtArena,
        symbol_local_defn_storage: VdMirSymbolLocalDefnStorage,
    ) -> Self {
        Self {
            expr_arena,
            stmt_arena,
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

    pub fn symbol_local_defn_storage(&self) -> &VdMirSymbolLocalDefnStorage {
        &self.symbol_local_defn_storage
    }
}

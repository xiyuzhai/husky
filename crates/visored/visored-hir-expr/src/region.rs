use crate::{
    expr::{VdHirExprArena, VdHirExprArenaRef},
    stmt::{VdHirStmtArena, VdHirStmtArenaRef},
};

pub struct VdHirExprRegionData {
    expr_arena: VdHirExprArena,
    stmt_arena: VdHirStmtArena,
}

impl VdHirExprRegionData {
    pub fn new(expr_arena: VdHirExprArena, stmt_arena: VdHirStmtArena) -> Self {
        Self {
            expr_arena,
            stmt_arena,
        }
    }
}

impl VdHirExprRegionData {
    pub fn expr_arena(&self) -> VdHirExprArenaRef {
        self.expr_arena.as_arena_ref()
    }

    pub fn stmt_arena(&self) -> VdHirStmtArenaRef {
        self.stmt_arena.as_arena_ref()
    }
}

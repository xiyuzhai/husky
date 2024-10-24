use crate::{
    expr::{LnHirExprArena, LnHirExprData, LnHirExprIdx, LnHirExprIdxRange},
    fmt::LnHirExprFormatter,
    stmt::{LnHirStmtArena, LnHirStmtData, LnHirStmtIdx, LnHirStmtIdxRange},
};

pub struct LeanHirExprBuilder<'db> {
    db: &'db ::salsa::Db,
    expr_arena: LnHirExprArena,
    stmt_arena: LnHirStmtArena,
}

impl<'db> LeanHirExprBuilder<'db> {
    pub fn new(db: &'db ::salsa::Db) -> Self {
        Self {
            db,
            expr_arena: Default::default(),
            stmt_arena: Default::default(),
        }
    }
}

impl<'db> LeanHirExprBuilder<'db> {
    pub fn db(&self) -> &'db ::salsa::Db {
        self.db
    }

    pub fn formatter(&self, line_max_len: usize) -> LnHirExprFormatter {
        LnHirExprFormatter::new(
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            line_max_len,
            self.db,
        )
    }
}

impl<'db> LeanHirExprBuilder<'db> {
    pub fn alloc_expr(&mut self, data: LnHirExprData) -> LnHirExprIdx {
        self.expr_arena.alloc_one(data)
    }

    pub fn alloc_exprs(
        &mut self,
        data: impl IntoIterator<Item = LnHirExprData>,
    ) -> LnHirExprIdxRange {
        self.expr_arena.alloc_batch(data)
    }

    pub fn alloc_stmt(&mut self, data: LnHirStmtData) -> LnHirStmtIdx {
        self.stmt_arena.alloc_one(data)
    }

    pub fn alloc_stmts(
        &mut self,
        data: impl IntoIterator<Item = LnHirStmtData>,
    ) -> LnHirStmtIdxRange {
        self.stmt_arena.alloc_batch(data)
    }
}

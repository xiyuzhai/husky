use crate::{
    expr::{LnHirExprArena, LnHirExprData, LnHirExprIdx, LnHirExprIdxRange},
    helpers::fmt::{LnHirExprFormatter, LnHirExprFormatterConfig},
    stmt::{LnHirStmtArena, LnHirStmtData, LnHirStmtIdx, LnHirStmtIdxRange},
    tactic::{LnHirTacticArena, LnHirTacticData, LnHirTacticIdx, LnHirTacticIdxRange},
};

pub struct LeanHirExprBuilder<'db> {
    db: &'db ::salsa::Db,
    expr_arena: LnHirExprArena,
    stmt_arena: LnHirStmtArena,
    tactic_arena: LnHirTacticArena,
}

impl<'db> LeanHirExprBuilder<'db> {
    pub fn new(db: &'db ::salsa::Db) -> Self {
        Self {
            db,
            expr_arena: Default::default(),
            stmt_arena: Default::default(),
            tactic_arena: Default::default(),
        }
    }
}

impl<'db> LeanHirExprBuilder<'db> {
    pub fn db(&self) -> &'db ::salsa::Db {
        self.db
    }

    pub fn formatter<'a>(&'a self, config: &'a LnHirExprFormatterConfig) -> LnHirExprFormatter<'a> {
        LnHirExprFormatter::new(
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.tactic_arena.as_arena_ref(),
            config,
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

    pub fn alloc_tactic(&mut self, data: LnHirTacticData) -> LnHirTacticIdx {
        self.tactic_arena.alloc_one(data)
    }

    pub fn alloc_tactics(
        &mut self,
        data: impl IntoIterator<Item = LnHirTacticData>,
    ) -> LnHirTacticIdxRange {
        self.tactic_arena.alloc_batch(data)
    }

    pub fn finish(self) -> (LnHirExprArena, LnHirStmtArena, LnHirTacticArena) {
        (self.expr_arena, self.stmt_arena, self.tactic_arena)
    }
}

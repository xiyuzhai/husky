use crate::{
    expr::{LnMirExprArena, LnMirExprData, LnMirExprIdx, LnMirExprIdxRange},
    helpers::fmt::{LnMirExprFormatter, LnMirExprFormatterConfig},
    item_defn::{LnItemDefnArena, LnItemDefnData, LnItemDefnIdxRange},
    stmt::{LnMirStmtArena, LnMirStmtData, LnMirStmtIdx, LnMirStmtIdxRange},
    tactic::{LnMirTacticArena, LnMirTacticData, LnMirTacticIdx, LnMirTacticIdxRange},
};
use lean_item_path::namespace::LnNamespace;

pub struct LnMirExprBuilder<'db> {
    db: &'db ::salsa::Db,
    expr_arena: LnMirExprArena,
    stmt_arena: LnMirStmtArena,
    tactic_arena: LnMirTacticArena,
    item_defn_arena: LnItemDefnArena,
    current_namespace: LnNamespace,
}

impl<'db> LnMirExprBuilder<'db> {
    pub fn new(db: &'db ::salsa::Db) -> Self {
        Self {
            db,
            expr_arena: Default::default(),
            stmt_arena: Default::default(),
            tactic_arena: Default::default(),
            item_defn_arena: Default::default(),
            current_namespace: LnNamespace::new_root(db),
        }
    }
}

impl<'db> LnMirExprBuilder<'db> {
    pub fn db(&self) -> &'db ::salsa::Db {
        self.db
    }

    pub fn formatter<'a>(&'a self, config: &'a LnMirExprFormatterConfig) -> LnMirExprFormatter<'a> {
        LnMirExprFormatter::new(
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.tactic_arena.as_arena_ref(),
            self.item_defn_arena.as_arena_ref(),
            config,
            self.db,
        )
    }
}

impl<'db> LnMirExprBuilder<'db> {
    pub fn alloc_expr(&mut self, data: LnMirExprData) -> LnMirExprIdx {
        self.expr_arena.alloc_one(data)
    }

    pub fn alloc_exprs(
        &mut self,
        data: impl IntoIterator<Item = LnMirExprData>,
    ) -> LnMirExprIdxRange {
        self.expr_arena.alloc_batch(data)
    }

    pub fn alloc_stmt(&mut self, data: LnMirStmtData) -> LnMirStmtIdx {
        self.stmt_arena.alloc_one(data)
    }

    pub fn alloc_stmts(
        &mut self,
        data: impl IntoIterator<Item = LnMirStmtData>,
    ) -> LnMirStmtIdxRange {
        self.stmt_arena.alloc_batch(data)
    }

    pub fn alloc_tactic(&mut self, data: LnMirTacticData) -> LnMirTacticIdx {
        self.tactic_arena.alloc_one(data)
    }

    pub fn alloc_tactics(
        &mut self,
        data: impl IntoIterator<Item = LnMirTacticData>,
    ) -> LnMirTacticIdxRange {
        self.tactic_arena.alloc_batch(data)
    }

    pub fn alloc_item_defns(&mut self, item_defns: Vec<LnItemDefnData>) -> LnItemDefnIdxRange {
        self.item_defn_arena.alloc_batch(item_defns)
    }

    pub fn finish(
        self,
    ) -> (
        LnMirExprArena,
        LnMirStmtArena,
        LnMirTacticArena,
        LnItemDefnArena,
    ) {
        (
            self.expr_arena,
            self.stmt_arena,
            self.tactic_arena,
            self.item_defn_arena,
        )
    }
}

pub trait WithLnNamespace<'db> {
    fn ln_mir_expr_builder_mut(&mut self) -> &mut LnMirExprBuilder<'db>;

    fn with_ln_namespace<R>(
        &mut self,
        namespace: LnNamespace,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let previous_namespace = self.ln_mir_expr_builder_mut().current_namespace;
        self.ln_mir_expr_builder_mut().current_namespace = namespace;
        let result = f(self);
        self.ln_mir_expr_builder_mut().current_namespace = previous_namespace;
        result
    }
}

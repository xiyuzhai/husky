//! TODO: put this under helpers
use crate::{
    expr::{LnMirExprArena, LnMirExprData, LnMirExprEntry, LnMirExprIdx, LnMirExprIdxRange},
    helpers::fmt::{LnMirExprFormatter, LnMirExprFormatterConfig},
    item_defn::{
        LnItemDefnArena, LnItemDefnComment, LnItemDefnCommentMap, LnItemDefnData, LnItemDefnIdx,
        LnItemDefnIdxRange, LnItemDefnOrderedMap,
    },
    stmt::{LnMirStmtArena, LnMirStmtData, LnMirStmtIdx, LnMirStmtIdxRange},
    tactic::{LnMirTacticArena, LnMirTacticData, LnMirTacticIdx, LnMirTacticIdxRange},
};
use eterned::db::EternerDb;
use lean_entity_path::namespace::LnNamespace;

pub struct LnMirExprConstructor {
    expr_arena: LnMirExprArena,
    stmt_arena: LnMirStmtArena,
    tactic_arena: LnMirTacticArena,
    item_defn_arena: LnItemDefnArena,
    current_namespace: LnNamespace,
    item_defn_comments: LnItemDefnOrderedMap<LnItemDefnComment>,
}

impl LnMirExprConstructor {
    pub fn new(db: &EternerDb) -> Self {
        Self {
            expr_arena: Default::default(),
            stmt_arena: Default::default(),
            tactic_arena: Default::default(),
            item_defn_arena: Default::default(),
            current_namespace: LnNamespace::new_root(db),
            item_defn_comments: Default::default(),
        }
    }
}

impl LnMirExprConstructor {
    pub fn formatter<'a>(
        &'a self,
        config: &'a LnMirExprFormatterConfig,
        db: &'a EternerDb,
    ) -> LnMirExprFormatter<'a> {
        LnMirExprFormatter::new(
            db,
            self.expr_arena.as_arena_ref(),
            self.stmt_arena.as_arena_ref(),
            self.tactic_arena.as_arena_ref(),
            self.item_defn_arena.as_arena_ref(),
            &self.item_defn_comments,
            config,
        )
    }
}

impl LnMirExprConstructor {
    pub fn alloc_expr(&mut self, entry: LnMirExprEntry) -> LnMirExprIdx {
        self.expr_arena.alloc_one(entry)
    }

    pub fn alloc_exprs(
        &mut self,
        entries: impl IntoIterator<Item = LnMirExprEntry>,
    ) -> LnMirExprIdxRange {
        self.expr_arena.alloc_many(entries)
    }

    pub fn alloc_stmt(&mut self, data: LnMirStmtData) -> LnMirStmtIdx {
        self.stmt_arena.alloc_one(data)
    }

    pub fn alloc_stmts(
        &mut self,
        data: impl IntoIterator<Item = LnMirStmtData>,
    ) -> LnMirStmtIdxRange {
        self.stmt_arena.alloc_many(data)
    }

    pub fn alloc_tactic(&mut self, data: LnMirTacticData) -> LnMirTacticIdx {
        self.tactic_arena.alloc_one(data)
    }

    pub fn alloc_tactics(
        &mut self,
        data: impl IntoIterator<Item = LnMirTacticData>,
    ) -> LnMirTacticIdxRange {
        self.tactic_arena.alloc_many(data)
    }

    pub fn alloc_item_defn(
        &mut self,
        data: LnItemDefnData,
        comment: LnItemDefnComment,
    ) -> LnItemDefnIdx {
        let item_defn = self.item_defn_arena.alloc_one(data);
        self.item_defn_comments.insert_next(item_defn, comment);
        item_defn
    }

    pub fn alloc_item_defns(
        &mut self,
        item_defns: impl IntoIterator<Item = LnItemDefnData>,
        comments: impl IntoIterator<Item = LnItemDefnComment>,
    ) -> LnItemDefnIdxRange {
        let item_defns = self.item_defn_arena.alloc_many(item_defns);
        self.item_defn_comments
            .insert_next_batch(item_defns, comments);
        item_defns
    }

    pub fn finish(
        self,
    ) -> (
        LnMirExprArena,
        LnMirStmtArena,
        LnMirTacticArena,
        LnItemDefnArena,
        LnItemDefnCommentMap,
    ) {
        (
            self.expr_arena,
            self.stmt_arena,
            self.tactic_arena,
            self.item_defn_arena,
            self.item_defn_comments,
        )
    }
}

pub trait WithLnNamespace {
    fn ln_mir_expr_builder_mut(&mut self) -> &mut LnMirExprConstructor;

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

impl LnMirExprConstructor {
    pub fn current_namespace(&self) -> LnNamespace {
        self.current_namespace
    }
}

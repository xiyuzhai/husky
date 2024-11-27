use super::*;
use crate::{
    expr::{LnMirExprArena, LnMirExprArenaRef, LnMirExprData, LnMirExprIdx},
    item_defn::{
        def::LnMirDefBody, LnItemDefnArenaRef, LnItemDefnChild, LnItemDefnData, LnItemDefnIdx,
        LnItemDefnIdxRange,
    },
    stmt::{LnMirStmtArena, LnMirStmtArenaRef, LnMirStmtIdx, LnMirStmtIdxRange},
    tactic::{LnMirTacticArena, LnMirTacticArenaRef, LnMirTacticIdx, LnMirTacticIdxRange},
};
use husky_tree_utils::display::DisplayTree;

pub struct LnMirExprDisplayTreeBuilder<'a> {
    expr_arena: LnMirExprArenaRef<'a>,
    stmt_arena: LnMirStmtArenaRef<'a>,
    tactic_arena: LnMirTacticArenaRef<'a>,
    defn_arena: LnItemDefnArenaRef<'a>,
}

impl<'a> LnMirExprDisplayTreeBuilder<'a> {
    pub fn new(
        expr_arena: LnMirExprArenaRef<'a>,
        stmt_arena: LnMirStmtArenaRef<'a>,
        tactic_arena: LnMirTacticArenaRef<'a>,
        defn_arena: LnItemDefnArenaRef<'a>,
    ) -> Self {
        Self {
            expr_arena,
            stmt_arena,
            tactic_arena,
            defn_arena,
        }
    }
}

impl<'a> LnMirExprDisplayTreeBuilder<'a> {
    pub fn render_expr(&self, expr: LnMirExprIdx) -> DisplayTree {
        let value = match self.expr_arena[expr] {
            LnMirExprData::Literal(literal) => format!("literal: `{}`", literal.data()),
            LnMirExprData::ItemPath(item_path) => format!("item path: `{}`", item_path.show()),
            LnMirExprData::Variable { ident } => format!("variable: `{}`", ident.data()),
            LnMirExprData::Lambda {
                ref parameters,
                body,
            } => format!("lambda"),
            LnMirExprData::Application {
                function,
                arguments,
            } => format!("application"),
            LnMirExprData::Sorry => "sorry".to_string(),
        };
        let children = self.expr_arena[expr].children();
        DisplayTree::new(
            value,
            children.into_iter().map(|c| self.render_expr(c)).collect(),
        )
    }

    pub fn render_defns_together(&self, defns: LnItemDefnIdxRange) -> DisplayTree {
        let children = self.render_defns(defns);
        DisplayTree::new("defns".to_string(), children)
    }

    pub fn render_defns(&self, defns: LnItemDefnIdxRange) -> Vec<DisplayTree> {
        defns
            .into_iter()
            .map(|defn| self.render_defn(defn))
            .collect()
    }

    pub fn render_defn(&self, defn: LnItemDefnIdx) -> DisplayTree {
        let defn_data = &self.defn_arena[defn];
        let value = match defn_data {
            LnItemDefnData::Variable { ident: symbol, ty } => {
                format!("variable: `{}`", symbol.data())
            }
            LnItemDefnData::Group { defns, ref meta } => format!("group: `{}`", meta),
            LnItemDefnData::Def { symbol, ty, body } => format!("def: `{}`", symbol.data()),
        };
        let children = defn_data.children();
        DisplayTree::new(
            value,
            children
                .into_iter()
                .map(|c| self.render_defn_child(c))
                .collect(),
        )
    }

    fn render_defn_child(&self, child: LnItemDefnChild) -> DisplayTree {
        match child {
            LnItemDefnChild::Defn(defn) => self.render_defn(defn),
            LnItemDefnChild::Expr(expr) => self.render_expr(expr),
            LnItemDefnChild::DefBody(body) => self.render_def_body(body),
        }
    }

    fn render_def_body(&self, body: LnMirDefBody) -> DisplayTree {
        match body {
            LnMirDefBody::Expr(expr) => self.render_expr(expr),
            LnMirDefBody::Tactics(tactics) => self.render_tactics_together(tactics),
            LnMirDefBody::Stmts(stmts) => self.render_stmts_together(stmts),
        }
    }

    pub fn render_tactics_together(&self, tactics: LnMirTacticIdxRange) -> DisplayTree {
        let children = self.render_tactics(tactics);
        DisplayTree::new("tactics".to_string(), children)
    }

    pub fn render_tactics(&self, tactics: LnMirTacticIdxRange) -> Vec<DisplayTree> {
        tactics
            .into_iter()
            .map(|tactic| self.render_tactic(tactic))
            .collect()
    }

    pub fn render_tactic(&self, tactic: LnMirTacticIdx) -> DisplayTree {
        let value = format!("tactic: `{:?}`", self.tactic_arena[tactic]);
        let children = vec![];
        DisplayTree::new(value, children)
    }

    pub fn render_stmts_together(&self, stmts: LnMirStmtIdxRange) -> DisplayTree {
        let children = self.render_stmts(stmts);
        DisplayTree::new("stmts".to_string(), children)
    }

    pub fn render_stmts(&self, stmts: LnMirStmtIdxRange) -> Vec<DisplayTree> {
        stmts
            .into_iter()
            .map(|stmt| self.render_stmt(stmt))
            .collect()
    }

    pub fn render_stmt(&self, stmt: LnMirStmtIdx) -> DisplayTree {
        let value = format!("stmt: `{:?}`", self.stmt_arena[stmt]);
        let children = vec![];
        DisplayTree::new(value, children)
    }
}

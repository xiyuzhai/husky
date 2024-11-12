use super::*;
use crate::{
    expr::{LnHirExprArena, LnHirExprArenaRef, LnHirExprData, LnHirExprIdx},
    stmt::{LnHirStmtArena, LnHirStmtArenaRef},
    tactic::{LnHirTacticArena, LnHirTacticArenaRef},
};
use husky_tree_utils::display::DisplayTree;

pub struct LnHirExprDisplayTreeBuilder<'a> {
    db: &'a ::salsa::Db,
    expr_arena: LnHirExprArenaRef<'a>,
    stmt_arena: LnHirStmtArenaRef<'a>,
    tactic_arena: LnHirTacticArenaRef<'a>,
}

impl<'a> LnHirExprDisplayTreeBuilder<'a> {
    pub fn new(
        db: &'a ::salsa::Db,
        expr_arena: LnHirExprArenaRef<'a>,
        stmt_arena: LnHirStmtArenaRef<'a>,
        tactic_arena: LnHirTacticArenaRef<'a>,
    ) -> Self {
        Self {
            db,
            expr_arena,
            stmt_arena,
            tactic_arena,
        }
    }
}

impl<'a> LnHirExprDisplayTreeBuilder<'a> {
    pub fn render_expr(&self, expr: LnHirExprIdx) -> DisplayTree {
        let db = self.db;
        let value = match self.expr_arena[expr] {
            LnHirExprData::Literal(literal) => format!("literal: `{}`", literal.data(db)),
            LnHirExprData::ItemPath(item_path) => format!("item path: `{}`", item_path.show(db)),
            LnHirExprData::Variable { ident } => todo!(),
            LnHirExprData::Prefix { opr, opd } => todo!(),
            LnHirExprData::Suffix { opd, opr } => todo!(),
            LnHirExprData::Binary { lopd, opr, ropd } => format!("binary: `{}`", opr),
            LnHirExprData::Lambda {
                ref parameters,
                body,
            } => todo!(),
            LnHirExprData::Application {
                function_and_arguments,
            } => todo!(),
        };
        let children = self.expr_arena[expr].children();
        DisplayTree::new(
            value,
            children.into_iter().map(|c| self.render_expr(c)).collect(),
        )
    }
}

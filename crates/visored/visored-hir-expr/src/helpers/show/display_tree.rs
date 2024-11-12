use husky_tree_utils::display::DisplayTree;

use crate::{
    expr::{application::VdHirApplicationFunction, VdHirExprArenaRef, VdHirExprData, VdHirExprIdx},
    stmt::VdHirStmtArenaRef,
};

pub struct VdHirExprDisplayTreeBuilder<'a> {
    db: &'a salsa::Db,
    expr_arena: VdHirExprArenaRef<'a>,
    stmt_arena: VdHirStmtArenaRef<'a>,
}

impl<'a> VdHirExprDisplayTreeBuilder<'a> {
    pub fn new(
        db: &'a salsa::Db,
        expr_arena: VdHirExprArenaRef<'a>,
        stmt_arena: VdHirStmtArenaRef<'a>,
    ) -> Self {
        Self {
            db,
            expr_arena,
            stmt_arena,
        }
    }
}

impl<'a> VdHirExprDisplayTreeBuilder<'a> {
    pub fn render_expr(&self, expr: VdHirExprIdx) -> DisplayTree {
        let db = self.db;
        let (value, children) = match self.expr_arena[expr] {
            VdHirExprData::Literal(literal) => (literal.data(db).as_str().to_string(), vec![]),
            VdHirExprData::Variable(ref variable) => ("variable".to_string(), vec![]),
            VdHirExprData::Application {
                function,
                arguments,
            } => {
                let value = match function {
                    VdHirApplicationFunction::IntAdd => "separator list int add".to_string(),
                    VdHirApplicationFunction::TrivialEq => "separator list eq".to_string(),
                };
                (
                    value,
                    arguments
                        .into_iter()
                        .map(|arg| self.render_expr(arg))
                        .collect(),
                )
            }
            VdHirExprData::ItemPath(item_path) => todo!(),
        };
        DisplayTree::new(value, children)
    }
}

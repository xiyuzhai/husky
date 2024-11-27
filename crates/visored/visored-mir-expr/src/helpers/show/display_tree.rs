use husky_tree_utils::display::DisplayTree;

use crate::{
    expr::{application::VdMirFunc, VdMirExprArenaRef, VdMirExprData, VdMirExprIdx},
    stmt::{VdMirStmtArenaRef, VdMirStmtData, VdMirStmtIdx, VdMirStmtIdxRange},
};

pub struct VdMirExprDisplayTreeBuilder<'a> {
    expr_arena: VdMirExprArenaRef<'a>,
    stmt_arena: VdMirStmtArenaRef<'a>,
}

impl<'a> VdMirExprDisplayTreeBuilder<'a> {
    pub fn new(expr_arena: VdMirExprArenaRef<'a>, stmt_arena: VdMirStmtArenaRef<'a>) -> Self {
        Self {
            expr_arena,
            stmt_arena,
        }
    }
}

impl<'a> VdMirExprDisplayTreeBuilder<'a> {
    pub fn render_expr(&self, expr: VdMirExprIdx) -> DisplayTree {
        let (value, children) = match self.expr_arena[expr] {
            VdMirExprData::Literal(literal) => (literal.data().as_str().to_string(), vec![]),
            VdMirExprData::Variable(ref variable) => ("variable".to_string(), vec![]),
            VdMirExprData::Application {
                function,
                arguments,
            } => {
                let value = match function {
                    VdMirFunc::NormalBasePrefixOpr(signature) => {
                        format!("prefix opr")
                    }
                    VdMirFunc::NormalBaseSeparator { .. } => "separator".to_string(),
                    VdMirFunc::NormalBaseBinaryOpr { .. } => "binary opr".to_string(),
                    VdMirFunc::InSet => "in set".to_string(),
                    VdMirFunc::Power(vd_power_signature) => {
                        format!("power")
                    }
                    VdMirFunc::NormalBaseSqrt(signature) => {
                        format!("sqrt")
                    }
                    VdMirFunc::NormalBaseFrac(signature) => {
                        format!("frac")
                    }
                };
                (
                    value,
                    arguments
                        .into_iter()
                        .map(|arg| self.render_expr(arg))
                        .collect(),
                )
            }
            VdMirExprData::ItemPath(item_path) => todo!(),
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            }
            | VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                ..
            } => (
                format!("folding separated list"),
                [self.render_expr(leader)]
                    .into_iter()
                    .chain(
                        followers
                            .iter()
                            .copied()
                            .map(|(_, expr)| self.render_expr(expr)),
                    )
                    .collect(),
            ),
        };
        DisplayTree::new(value, children)
    }

    pub fn render_stmts(&self, stmts: VdMirStmtIdxRange) -> Vec<DisplayTree> {
        stmts
            .into_iter()
            .map(|stmt| self.render_stmt(stmt))
            .collect()
    }

    pub fn render_stmt(&self, stmt: VdMirStmtIdx) -> DisplayTree {
        let (value, children) = match self.stmt_arena[stmt] {
            VdMirStmtData::Block { stmts, ref meta } => {
                (format!("block: {:?}", meta), self.render_stmts(stmts))
            }
            // TODO: render pattern and type
            VdMirStmtData::LetPlaceholder { ref pattern, ty } => {
                (format!("let placeholder",), vec![])
            }
            // TODO: render pattern
            VdMirStmtData::LetAssigned {
                ref pattern,
                assignment,
            } => (format!("let assigned"), vec![self.render_expr(assignment)]),
            VdMirStmtData::Then { formula } => (format!("then"), vec![self.render_expr(formula)]),
        };
        DisplayTree::new(value, children)
    }
}

use eterned::db::EternerDb;
use husky_tree_utils::display::DisplayTree;

use crate::{
    expr::{application::VdMirFunc, VdMirExprArenaRef, VdMirExprData, VdMirExprIdx},
    hint::{VdMirHintIdx, VdMirHintIdxRange},
    stmt::{VdMirStmtArenaRef, VdMirStmtData, VdMirStmtIdx, VdMirStmtIdxRange},
};

pub struct VdMirExprDisplayTreeBuilder<'a> {
    db: &'a EternerDb,
    expr_arena: VdMirExprArenaRef<'a>,
    stmt_arena: VdMirStmtArenaRef<'a>,
}

impl<'a> VdMirExprDisplayTreeBuilder<'a> {
    pub fn new(
        db: &'a EternerDb,
        expr_arena: VdMirExprArenaRef<'a>,
        stmt_arena: VdMirStmtArenaRef<'a>,
    ) -> Self {
        Self {
            db,
            expr_arena,
            stmt_arena,
        }
    }
}

impl<'a> VdMirExprDisplayTreeBuilder<'a> {
    pub fn db(&self) -> &'a EternerDb {
        self.db
    }
}

impl<'a> VdMirExprDisplayTreeBuilder<'a> {
    pub fn render_expr(&self, expr: VdMirExprIdx) -> DisplayTree {
        let db = self.db();
        let (value, children) = match *self.expr_arena[expr].data() {
            VdMirExprData::Literal(literal) => (literal.data().to_string(), vec![]),
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
                    VdMirFunc::Power(vd_power_signature) => {
                        format!("power")
                    }
                    VdMirFunc::NormalBaseSqrt(signature) => {
                        format!("sqrt")
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
            VdMirExprData::ChainingSeparatedList {
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
        let (value, children) = match *self.stmt_arena[stmt].data() {
            VdMirStmtData::Block { stmts, ref meta } => {
                (format!("block: {:?}", meta), self.render_stmts(stmts))
            }
            // TODO: render pattern and type
            VdMirStmtData::LetPlaceholder { ref pattern, ty } => {
                (format!("let placeholder",), vec![])
            }
            VdMirStmtData::Assume { .. } => todo!(),
            // TODO: render pattern
            VdMirStmtData::LetAssigned {
                ref pattern,
                assignment,
                ..
            } => (format!("let assigned"), vec![self.render_expr(assignment)]),
            VdMirStmtData::Goal { prop } => (format!("goal"), vec![self.render_expr(prop)]),
            VdMirStmtData::Have { prop, hint, .. } => {
                (format!("have"), vec![self.render_expr(prop)])
            }
            VdMirStmtData::Show { prop, hint, .. } => {
                (format!("show"), vec![self.render_expr(prop)])
            }
            VdMirStmtData::Qed {
                goal_and_hypothesis_chunk_place: goal_and_hypothesis_place,
            } => (
                format!("qed"),
                goal_and_hypothesis_place
                    .into_iter()
                    .map(|(goal, _)| self.render_expr(goal))
                    .collect(),
            ),
        };
        DisplayTree::new(value, children)
    }

    fn render_tactics<'b>(
        &'b self,
        tactics: VdMirHintIdxRange,
    ) -> impl Iterator<Item = DisplayTree> + 'b {
        tactics
            .into_iter()
            .map(move |tactic| self.render_tactic(tactic))
    }

    fn render_tactic(&self, tactic: VdMirHintIdx) -> DisplayTree {
        DisplayTree::new(format!("tactic: {:?}", tactic), vec![])
    }
}

use super::*;
use crate::{
    expr::{application::VdMirFunc, VdMirExprArenaRef, VdMirExprData, VdMirExprIdx},
    hint::{VdMirHintIdx, VdMirHintIdxRange},
    stmt::{VdMirStmtArenaRef, VdMirStmtData, VdMirStmtIdx, VdMirStmtIdxRange},
    symbol::local_defn::{storage::VdMirSymbolLocalDefnStorage, VdMirSymbolLocalDefnHead},
};
use ::lisp_show_expr::LispShowExpr;
use eterned::db::EternerDb;

pub struct VdMirExprLispShowExprBuilder<'a> {
    db: &'a EternerDb,
    expr_arena: VdMirExprArenaRef<'a>,
    stmt_arena: VdMirStmtArenaRef<'a>,
    local_defn_storage: &'a VdMirSymbolLocalDefnStorage,
}

impl<'a> VdMirExprLispShowExprBuilder<'a> {
    pub fn new(
        db: &'a EternerDb,
        expr_arena: VdMirExprArenaRef<'a>,
        stmt_arena: VdMirStmtArenaRef<'a>,
        local_defn_storage: &'a VdMirSymbolLocalDefnStorage,
    ) -> Self {
        Self {
            db,
            expr_arena,
            stmt_arena,
            local_defn_storage,
        }
    }
}

impl<'a> VdMirExprLispShowExprBuilder<'a> {
    pub fn render_expr(&self, expr: VdMirExprIdx) -> LispShowExpr {
        match *self.expr_arena[expr].data() {
            VdMirExprData::Literal(vd_literal) => LispShowExpr::String(vd_literal.to_string()),
            VdMirExprData::Variable(local_defn) => {
                match self.local_defn_storage.defn_arena()[local_defn].head() {
                    VdMirSymbolLocalDefnHead::Letter(lx_math_letter) => {
                        LispShowExpr::String(lx_math_letter.to_string())
                    }
                }
            }
            VdMirExprData::Application {
                function,
                arguments,
            } => {
                let mut args = Vec::new();
                for arg in arguments {
                    args.push(self.render_expr(arg));
                }
                LispShowExpr::List(args)
            }
            VdMirExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => {
                let mut args = vec![LispShowExpr::String(followers[0].0.separator().to_string())];
                args.push(self.render_expr(leader));
                for &(_, arg) in followers {
                    args.push(self.render_expr(arg));
                }
                LispShowExpr::List(args)
            }
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => {
                let mut args = vec![LispShowExpr::String(followers[0].0.separator().to_string())];
                args.push(self.render_expr(leader));
                for &(_, arg) in followers {
                    args.push(self.render_expr(arg));
                }
                LispShowExpr::List(args)
            }
            VdMirExprData::ItemPath(vd_item_path) => LispShowExpr::String(vd_item_path.to_string()),
        }
    }
}

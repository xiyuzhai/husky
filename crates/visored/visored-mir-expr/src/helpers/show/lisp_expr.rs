use super::*;
use crate::{
    expr::{application::VdMirFunc, VdMirExprArenaRef, VdMirExprData, VdMirExprIdx},
    hint::{VdMirHintIdx, VdMirHintIdxRange},
    stmt::{VdMirStmtArenaRef, VdMirStmtData, VdMirStmtIdx, VdMirStmtIdxRange},
};
use eterned::db::EternerDb;

pub struct VdMirExprLispExprBuilder<'a> {
    db: &'a EternerDb,
    lisp_expr_constructor: LispExprConstructor<'a>,
    expr_arena: VdMirExprArenaRef<'a>,
    stmt_arena: VdMirStmtArenaRef<'a>,
}

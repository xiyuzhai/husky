use super::*;
use crate::{expr::LnMirExprIdx, stmt::LnMirStmtIdxRange, tactic::LnMirTacticIdxRange};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LnMirDefBody {
    Expr(LnMirExprIdx),
    Tactics(LnMirTacticIdxRange),
    Stmts(LnMirStmtIdxRange),
}

use super::*;
use crate::{expr::LnMirExprIdx, stmt::LnMirStmtIdxRange, tactic::LnMirTacticIdxRange};

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LnMirDefBody {
    Expr(LnMirExprIdx),
    Tactics(LnMirTacticIdxRange),
    Stmts(LnMirStmtIdxRange),
}

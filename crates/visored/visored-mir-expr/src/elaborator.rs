pub mod linear;

use eterned::db::EternerDb;
use visored_global_dispatch::default_table::VdDefaultGlobalDispatchTable;

use crate::{
    expr::VdMirExprIdx,
    hypothesis::constructor::VdMirHypothesisConstructor,
    region::VdMirExprRegionDataRef,
    stmt::{VdMirStmtIdx, VdMirStmtIdxRange},
    *,
};

pub trait IsVdMirTacticElaborator<'db>: Sized {
    type HypothesisIdx;

    fn elaborate_stmts_ext(
        self,
        stmts: VdMirStmtIdxRange,
        hc: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    );
    fn elaborate_stmt_ext(
        self,
        stmt: VdMirStmtIdx,
        hc: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    );
    fn elaborate_expr_ext(
        self,
        expr: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    );
}

pub type VdMirTrivialElaborator<'db> = self::linear::VdMirSequentialElaborator<'db, ()>;

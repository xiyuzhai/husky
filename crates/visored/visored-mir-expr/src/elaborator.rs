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
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    );
    fn elaborate_stmt_ext(
        self,
        stmt: VdMirStmtIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    );
    fn elaborate_expr_ext(
        self,
        expr: VdMirExprIdx,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
    );

    fn run<R>(
        db: &'db EternerDb,
        global_dispatch_table: &VdDefaultGlobalDispatchTable,
        hypothesis_constructor: VdMirHypothesisConstructor<'db, Self::HypothesisIdx>,
        f: impl FnOnce(Self, VdMirHypothesisConstructor<'db, Self::HypothesisIdx>) -> R,
    ) -> R;
}

pub type VdMirTrivialElaborator<'db> = self::linear::VdMirSequentialElaborator<'db, ()>;

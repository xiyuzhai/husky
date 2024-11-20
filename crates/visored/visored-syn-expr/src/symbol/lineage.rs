use super::*;
use crate::{
    clause::VdSynClauseIdx, division::VdSynDivisionIdx, expr::VdSynExprIdx, phrase::VdSynPhraseIdx,
    sentence::VdSynSentenceIdx, stmt::VdSynStmtIdx,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VdSynLineage {
    pub(super) divisions: SmallVec<[VdSynDivisionIdx; 8]>,
    pub(super) stmts: SmallVec<[VdSynStmtIdx; 8]>,
    pub(super) sentence: Option<VdSynSentenceIdx>,
    pub(super) clause: Option<VdSynClauseIdx>,
    pub(super) phrases: SmallVec<[VdSynPhraseIdx; 8]>,
    pub(super) exprs: SmallVec<[VdSynExprIdx; 8]>,
}
impl VdSynLineage {
    pub(crate) fn current_stmt_or_division(&self) -> Either<VdSynStmtIdx, VdSynDivisionIdx> {
        self.stmts.last().copied().map(Left).unwrap_or_else(|| {
            self.divisions
                .last()
                .copied()
                .map(Right)
                .expect("lineage must have at least one division")
        })
    }
}

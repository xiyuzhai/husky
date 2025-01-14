use super::{VdMirHypothesisIdx, VdMirHypothesisIdxRange};
use crate::stmt::VdMirStmtIdx;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VdMirHypothesisChunk {
    stmt: VdMirStmtIdx,
    new_hypotheses: VdMirHypothesisIdxRange,
    main_hypothesis: VdMirHypothesisIdx,
}

impl VdMirHypothesisChunk {
    pub fn new(
        stmt: VdMirStmtIdx,
        new_hypotheses: VdMirHypothesisIdxRange,
        main_hypothesis: VdMirHypothesisIdx,
    ) -> Self {
        Self {
            stmt,
            new_hypotheses,
            main_hypothesis,
        }
    }
}

impl VdMirHypothesisChunk {
    pub fn stmt(&self) -> VdMirStmtIdx {
        self.stmt
    }

    pub fn new_hypotheses(&self) -> VdMirHypothesisIdxRange {
        self.new_hypotheses
    }

    pub fn main_hypothesis(&self) -> VdMirHypothesisIdx {
        self.main_hypothesis
    }
}

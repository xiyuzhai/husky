use super::{hypothesis::VdMirHypothesisIdx, VdMirDerivationIdx, VdMirDerivationIdxRange};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VdMirDerivationChunk {
    new_derivations: VdMirDerivationIdxRange,
    main_derivation: VdMirDerivationIdx,
}

impl VdMirDerivationChunk {
    pub fn new(
        new_derivations: VdMirDerivationIdxRange,
        main_derivation: VdMirDerivationIdx,
    ) -> Self {
        Self {
            new_derivations,
            main_derivation,
        }
    }
}

impl VdMirDerivationChunk {
    pub fn new_derivations(&self) -> VdMirDerivationIdxRange {
        self.new_derivations
    }

    pub fn main_derivation(&self) -> VdMirDerivationIdx {
        self.main_derivation
    }
}

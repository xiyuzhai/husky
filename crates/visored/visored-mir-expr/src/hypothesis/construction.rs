use super::*;
use crate::{coercion::VdMirCoercionConstruction, derivation::chunk::VdMirDerivationChunk};
use visored_entity_path::theorem::VdTheoremPath;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirHypothesisConstruction {
    Apply {
        path: VdTheoremPath,
        is_real_coercion: VdMirCoercionConstruction,
    },
    Assume,
    Sorry,
    TermEquivalence {
        hypothesis: VdMirHypothesisIdx,
        derivation_chunk: VdMirDerivationChunk,
    },
    TermTrivial(bool),
    CommRing,
    LetAssigned,
    LitnumReduce,
    LitnumBound,
    Kurapika,
}

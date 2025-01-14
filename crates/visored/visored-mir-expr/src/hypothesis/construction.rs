use super::*;
use crate::{coercion::VdMirCoercion, derivation::chunk::VdMirDerivationChunk};
use visored_entity_path::theorem::VdTheoremPath;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirHypothesisConstruction {
    Apply {
        path: VdTheoremPath,
        is_real_coercion: VdMirCoercion,
    },
    Assume,
    Sorry,
    TermEquivalent {
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

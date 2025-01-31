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
    // TODO: add derivation chunk
    TermTrivial(bool),
    // TODO: add derivation chunk
    CommRing,
    LetAssigned,
    // TODO: add derivation chunk
    LitnumReduce,
    // TODO: add derivation chunk
    LitnumBound {
        derivation_chunk: VdMirDerivationChunk,
    },
    Kurapika,
}

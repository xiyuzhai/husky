use crate::coercion::VdMirCoercion;

use super::*;
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
        derivations: VdMirDerivationIdxRange,
    },
    TermTrivial(bool),
    CommRing,
    LetAssigned,
    LitnumReduce,
    LitnumBound,
    Kurapika,
}

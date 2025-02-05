pub mod trivial_bound;

use self::trivial_bound::VdBsqTrivialBoundHypothesisConstruction;
use super::*;
use crate::coercion::VdBsqCoercion;
use stashes::litnum_bound::{VdBsqLitnumBound, VdBsqLitnumBoundSrc};
use std::marker::PhantomData;
use visored_entity_path::theorem::VdTheoremPath;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdBsqHypothesisConstruction<'sess> {
    TermTrivial(bool),
    Assume,
    Apply {
        path: VdTheoremPath,
        is_real_coercion: VdBsqCoercion<'sess>,
    },
    CommRing,
    TermEquivalence {
        hypothesis: VdBsqHypothesisIdx<'sess>,
    },
    Sorry,
    LetAssigned,
    LitnumReduce,
    LitnumBound {
        bound: VdBsqLitnumBound<'sess>,
    },
    TrivialBound(VdBsqTrivialBoundHypothesisConstruction),
}

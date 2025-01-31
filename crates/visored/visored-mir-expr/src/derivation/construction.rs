pub mod litnum_bound;
pub mod ring;
pub mod term;

use self::litnum_bound::VdMirLitnumBoundDerivationConstruction;
use self::ring::VdMirRingDerivationConstruction;
use self::term::VdMirTermDerivationConstruction;
use super::{expr::VdMirExprIdx, hypothesis::constructor::VdMirHypothesisConstructor, *};

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq)]
pub enum VdMirDerivationConstruction {
    LitnumBound(VdMirLitnumBoundDerivationConstruction),
    Ring(VdMirRingDerivationConstruction),
    Term(VdMirTermDerivationConstruction),
}

impl VdMirDerivationConstruction {
    pub fn check<'db, Src>(
        &self,
        prop: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, Src>,
    ) {
        match self {
            VdMirDerivationConstruction::LitnumBound(construction) => construction.check(prop, hc),
            VdMirDerivationConstruction::Ring(construction) => construction.check(prop, hc),
            VdMirDerivationConstruction::Term(construction) => construction.check(prop, hc),
        }
    }
}

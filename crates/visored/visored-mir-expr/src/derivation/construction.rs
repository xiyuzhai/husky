pub mod ring;
pub mod term;

use self::ring::VdMirRingDerivationConstruction;
use self::term::VdMirTermDerivationConstruction;
use super::{expr::VdMirExprIdx, hypothesis::constructor::VdMirHypothesisConstructor};

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq)]
pub enum VdMirDerivationConstruction {
    Ring(VdMirRingDerivationConstruction),
    Term(VdMirTermDerivationConstruction),
}

impl VdMirDerivationConstruction {
    pub fn check<'db, Src>(&self, prop: VdMirExprIdx, hc: &VdMirHypothesisConstructor<'db, Src>) {
        match self {
            VdMirDerivationConstruction::Ring(construction) => construction.check(prop, hc),
            VdMirDerivationConstruction::Term(construction) => construction.check(prop, hc),
        }
    }
}

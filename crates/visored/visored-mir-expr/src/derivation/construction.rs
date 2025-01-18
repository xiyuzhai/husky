pub mod ring;

use self::ring::VdMirRingDerivationConstruction;
use super::{expr::VdMirExprIdx, hypothesis::constructor::VdMirHypothesisConstructor};

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirDerivationConstruction {
    Ring(VdMirRingDerivationConstruction),
}

impl VdMirDerivationConstruction {
    pub fn check<'db, Src>(&self, prop: VdMirExprIdx, hc: &VdMirHypothesisConstructor<'db, Src>) {
        match self {
            VdMirDerivationConstruction::Ring(construction) => construction.check(prop, hc),
        }
    }
}

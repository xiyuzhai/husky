pub mod ring;
pub mod term;

use self::{ring::VdMirRingDerivationConstruction, term::VdMirTermDerivationConstruction};

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq)]
pub enum VdMirDerivationConstruction {
    Ring(VdMirRingDerivationConstruction),
    Term(VdMirTermDerivationConstruction),
}

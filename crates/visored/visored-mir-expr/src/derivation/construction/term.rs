use crate::derivation::VdMirDerivationIdx;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirTermDerivationConstruction {
    Sum,
    Product,
    Finalize {
        src_term_equivalent: VdMirDerivationIdx,
        dst_term_equivalent: VdMirDerivationIdx,
    },
}

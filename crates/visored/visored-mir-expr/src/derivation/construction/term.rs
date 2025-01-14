use crate::derivation::{VdMirDerivationIdx, VdMirDerivationIdxRange};

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirTermDerivationConstruction {
    Obvious,
    Sum {
        summand_term_equivalences: VdMirDerivationIdxRange,
    },
    Product {
        factor_term_equivalences: VdMirDerivationIdxRange,
    },
    Finalize {
        src_term_equivalence: VdMirDerivationIdx,
        dst_term_equivalence: VdMirDerivationIdx,
    },
}

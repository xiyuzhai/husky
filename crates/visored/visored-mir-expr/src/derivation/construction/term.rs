use visored_signature::signature::separator::base::{
    chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
};

use crate::{
    derivation::{VdMirDerivationIdx, VdMirDerivationIdxRange},
    expr::application::VdMirFunc,
};

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirTermDerivationConstruction {
    Literal,
    Variable,
    ItemPath,
    Sum {
        leader_equivalence: VdMirDerivationIdx,
        follower_equivalences: Vec<(VdBaseFoldingSeparatorSignature, VdMirDerivationIdx)>,
    },
    Sub {
        lopd: VdMirDerivationIdx,
        ropd: VdMirDerivationIdx,
    },
    Product {
        leader_equivalence: VdMirDerivationIdx,
        follower_equivalences: Vec<(VdBaseFoldingSeparatorSignature, VdMirDerivationIdx)>,
    },
    Div {
        numerator: VdMirDerivationIdx,
        denominator: VdMirDerivationIdx,
    },
    ChainingSeparatedList {
        leader_equivalence: VdMirDerivationIdx,
        follower_equivalences: Vec<(VdBaseChainingSeparatorSignature, VdMirDerivationIdx)>,
    },
    Square {
        radicand: VdMirDerivationIdx,
    },
    Finalize {
        src_term_equivalence: VdMirDerivationIdx,
        dst_term_equivalence: VdMirDerivationIdx,
    },
}

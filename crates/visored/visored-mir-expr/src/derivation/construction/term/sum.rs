use crate::{helpers::compare::assert_deep_eq, hypothesis::constructor::expr::ds};

use super::*;
use visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator;
use visored_opr::separator::VdBaseSeparator;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

pub(super) fn check_literal_add_literal<'db, Src>(
    lhs: VdMirExprIdx,
    rhs: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    let VdMirExprData::FoldingSeparatedList {
        leader,
        ref followers,
    } = *hc.expr(lhs).data()
    else {
        unreachable!("leader is not a literal, but a `{:?}`", hc.expr(lhs).data())
    };
    let lopd = hc.literal(leader);
    let &[(signature, follower)] = followers.as_slice() else {
        panic!()
    };
    assert_eq!(
        signature.separator(),
        VdMirBaseFoldingSeparator::CommRingAdd
    );
    let ropd = hc.literal(follower);
    let rhs = hc.literal(rhs);
    assert_eq!(&lopd.data().add(ropd.data()), rhs.data());
}

/// derive `a + b => term` from `a => term_a`, `b => term_b` and `term_a + term_b => term`
pub(super) fn check_add_eq<'db, Src>(
    // `a + b`
    lhs: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    // `term`
    term: VdMirExprIdx,
    // `a => term_a`
    lopd: VdMirTermDerivationIdx,
    // `b => term_b`
    ropd: VdMirTermDerivationIdx,
    // `term_a + term_b => term`
    merge: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::EQ);
    ds!(let (a + b) = lhs, hc);
    ds!(let (a1 => term_a) = lopd.prop(hc), hc);
    assert_deep_eq!(a1, a, hc);
    ds!(let (b1 => term_b) = ropd.prop(hc), hc);
    assert_deep_eq!(b1, b, hc);
    ds!(let (merge_lhs => term1) = merge.prop(hc), hc);
    assert_deep_eq!(term1, term, hc);
    ds!(let (term_a1 + term_b1) = merge_lhs, hc);
    assert_deep_eq!(term_a1, term_a, hc);
    assert_deep_eq!(term_b1, term_b, hc);
}

/// derive `a + c => c + 1 * a` if `a` is an atom and `c` is a constant
pub(super) fn check_atom_add_constant<'db, Src>(
    lhs: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    rhs: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::EQ);
    ds!(let (a + c) = lhs, hc);
    ds!(let (c1 + rhs_ropd) = rhs, hc);
    ds!(let (one * a1) = rhs_ropd, hc);
    assert!(hc.literal(one).is_one());
}

/// derive `c + a => c + 1 * a` if `a` is an atom and `c` is a nonzero literal or summand with different stem
pub(super) fn check_nonzero_literal_add_atom<'db, Src>(
    lhs: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    rhs: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::EQ);
    ds!(let (c + a) = lhs, hc);
    ds!(let (c1 + rhs_ropd) = rhs, hc);
    ds!(let (one * a1) = rhs_ropd, hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(c1, c, hc);
    assert_deep_eq!(a1, a, hc);
}

/// derive `c + 0 => c`
pub(super) fn check_nf_add_zero<'db, Src>(
    lhs: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    c1: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::EQ);
    ds!(let (c + zero) = lhs, hc);
    assert!(hc.literal(zero).is_zero());
    assert_deep_eq!(c1, c, hc);
}

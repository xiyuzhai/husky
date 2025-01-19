use crate::helpers::compare::assert_deep_eq;

use super::*;
use visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator;
use visored_opr::separator::VdBaseSeparator;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

pub(super) fn check_add_literal<'db, Src>(
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
    rhs: VdMirExprIdx,
    // `a => term_a`
    lopd: VdMirTermDerivationIdx,
    // `b => term_b`
    ropd: VdMirTermDerivationIdx,
    // `term_a + term_b => term`
    merge: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::EQ);
    let (a, b) = hc.split_folding_separated_list(lhs, VdMirBaseFoldingSeparator::COMM_RING_ADD);
    let term = rhs;
    let (a1, term_a) =
        hc.split_trivial_chaining_separated_list(lopd.prop(hc), VdMirBaseChainingSeparator::EQ);
    assert_deep_eq!(a1, a, hc);
    let (b1, term_b) =
        hc.split_trivial_chaining_separated_list(ropd.prop(hc), VdMirBaseChainingSeparator::EQ);
    assert_deep_eq!(
        b1,
        b,
        hc,
        "b1 = `{}`, b = `{}`",
        hc.show_expr_lisp(b1),
        hc.show_expr_lisp(b)
    );
    let (merge_lhs, term1) =
        hc.split_trivial_chaining_separated_list(merge.prop(hc), VdMirBaseChainingSeparator::EQ);
    assert_deep_eq!(term1, term, hc);
    let (term_a1, term_b1) =
        hc.split_folding_separated_list(merge_lhs, VdMirBaseFoldingSeparator::COMM_RING_ADD);
    assert_deep_eq!(term_a1, term_a, hc);
    assert_deep_eq!(term_b1, term_b, hc);
}

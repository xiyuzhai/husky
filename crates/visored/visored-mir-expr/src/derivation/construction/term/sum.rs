use super::*;
use visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator;
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
    lhs: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    rhs: VdMirExprIdx,
    lopd: VdMirTermDerivationIdx,
    ropd: VdMirTermDerivationIdx,
    merge: VdMirTermDerivationIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}

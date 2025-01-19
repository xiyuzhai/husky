use super::*;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

pub(super) fn check_literal_sum<'db, Src>(
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
    let ropd = hc.literal(follower);
    let rhs = hc.literal(rhs);
    assert_eq!(&lopd.data().add(ropd.data()), rhs.data());
}

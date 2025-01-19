use super::*;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

pub(super) fn check_literal_sum<'db, Src>(
    leader: VdMirExprIdx,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    let leader = hc.literal(leader);
    let follower = hc.literal(follower);
    todo!()
}

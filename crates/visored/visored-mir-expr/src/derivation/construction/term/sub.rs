use super::*;

/// obtain `a - b => term` from `a + (-b) => term`
pub(super) fn check_sub_eqs_add_neg<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}

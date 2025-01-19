use super::*;
use crate::hypothesis::constructor::expr::ds;

/// obtain `a - b => term` from `a + (-b) => term`
pub(super) fn check_sub_eqs_add_neg<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (leader_lhs => term) = leader, hc);
    todo!()
}

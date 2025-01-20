use super::*;
use crate::{helpers::compare::assert_deep_eq, hypothesis::constructor::expr::ds};

/// obtain `a - b => term` from `a + (-b) => term`
pub(super) fn check_sub_eqs_add_neg<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    term: VdMirExprIdx,
    add_neg: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (a - b) = leader, hc);
    ds!(let (add_neg_lhs => term1) = add_neg.prop(hc), hc);
    assert_deep_eq!(term1, term, hc);
    ds!(let (a1 + neg_b) = add_neg_lhs, hc);
    assert_deep_eq!(a1, a, hc);
    ds!(let (-b1) = neg_b, hc);
    assert_deep_eq!(b1, b, hc);
}

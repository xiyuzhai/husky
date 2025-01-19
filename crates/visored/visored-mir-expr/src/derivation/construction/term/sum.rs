use crate::{helpers::compare::eq, hypothesis::constructor::expr::ds};

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
    eq!(a1, a, hc);
    ds!(let (b1 => term_b) = ropd.prop(hc), hc);
    eq!(b1, b, hc);
    ds!(let (merge_lhs => term1) = merge.prop(hc), hc);
    eq!(term1, term, hc);
    ds!(let (term_a1 + term_b1) = merge_lhs, hc);
    eq!(term_a1, term_a, hc);
    eq!(term_b1, term_b, hc);
}

/// derive `a + c => c + 1 * a` if `a` is an atom and `c` is a constant
pub(super) fn check_atom_add_constant<'db, Src>(
    lhs: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    rhs: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    use husky_print_utils::*;
    p!(hc.show_expr_lisp(lhs), hc.show_expr_lisp(rhs));
    todo!()
}

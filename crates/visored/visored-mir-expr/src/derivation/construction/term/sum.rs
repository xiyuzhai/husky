use crate::{helpers::compare::assert_deep_eq, hypothesis::constructor::expr::ds};

use super::*;
use visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator;
use visored_opr::separator::VdBaseSeparator;
use visored_signature::signature::separator::base::folding::VdBaseFoldingSeparatorSignature;

pub(super) fn check_literal_add_literal<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a + b) = expr, hc);
    let a = hc.literal(a);
    let b = hc.literal(b);
    let term = hc.literal(term);
    assert_eq!(&a.data().add(b.data()), term.data());
}

/// derive `a + b => term` from `a => term_a`, `b => term_b` and `term_a + term_b => term`
pub(super) fn check_add_eq<'db, Src>(
    // `a + b`
    prop: VdMirExprIdx,
    // `a => term_a`
    lopd: VdMirTermDerivationIdx,
    // `b => term_b`
    ropd: VdMirTermDerivationIdx,
    // `term_a + term_b => term`
    merge: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (lhs => term) = prop, hc);
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

/// derive `a + c => c + 1 * a` if `a` is an atom and `c` is a litnum
pub(super) fn check_atom_add_swap<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (lhs => term) = prop, hc);
    ds!(let (a + c) = lhs, hc);
    ds!(let (c1 + rhs_ropd) = term, hc);
    ds!(let (one * a1) = rhs_ropd, hc);
    assert!(hc.literal(one).is_one());
}

/// derive `c + a => c + 1 * a` if `a` is an atom and `c` is a nonzero literal or summand with different stem
pub(super) fn check_nonzero_literal_add_atom<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (c + a) = expr, hc);
    ds!(let (c1 + rhs_ropd) = term, hc);
    ds!(let (one * a1) = rhs_ropd, hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(c1, c, hc);
    assert_deep_eq!(a1, a, hc);
}

/// derive `c + 0 => c`
pub(super) fn check_nf_add_zero<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (c + zero) = expr, hc);
    assert!(hc.literal(zero).is_zero());
    assert_deep_eq!(term, c, hc);
}

/// derive `a + b => 0 + 1 * a + b` if `a` is an atom and `b` is a product with higher stem
/// or derive `a + b => 0 + b + 1 * a` if `a` is an atom and `b` is a product with lower stem
/// or derive `a + b => 0 + c * a` if `a` is an atom and `b` is a product with same stem and coefficient d=c-1 and `c` is nonzero
/// or derive `a + b => 0` if `a` is an atom and `b` is a product with same stem and coefficient d=-1
pub(super) fn check_atom_add_product<'db, Src>(
    prop: VdMirExprIdx,
    comparison: core::cmp::Ordering,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a + b) = expr, hc);
    ds!(let (d * stem) = b, hc);
    let d = hc.literal(d);
    match comparison {
        std::cmp::Ordering::Less => {
            ds!(let (lopd + b1) = term, hc);
            ds!(let (zero + lropd) = lopd, hc);
            assert!(hc.literal(zero).is_zero());
            ds!(let (one * a1) = lropd, hc);
            assert!(hc.literal(one).is_one());
            assert_deep_eq!(a1, a, hc);
            assert_deep_eq!(b1, b, hc);
        }
        std::cmp::Ordering::Equal => todo!(),
        std::cmp::Ordering::Greater => todo!(),
    }
}

/// derive `0 + a => term` from `a => term`
pub(super) fn check_zero_add<'db, Src>(
    prop: VdMirExprIdx,
    a_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (zero + a) = expr, hc);
    ds!(let (a1 => term1) = a_nf.prop(hc), hc);
    assert!(hc.literal(zero).is_zero());
    assert_deep_eq!(term1, term, hc);
    assert_deep_eq!(a1, a, hc);
}

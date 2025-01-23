use super::*;
use crate::expr::application::VdMirFunc;
use visored_mir_opr::opr::prefix::VdMirBasePrefixOpr;
use visored_opr::opr::prefix::VdBasePrefixOpr;
use visored_signature::signature::prefix_opr::VdBasePrefixOprSignature;
use visored_term::term::literal::{VdLiteral, VdLiteralData};

pub(super) fn check_neg_literal<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (-a) = expr, hc);
    let minus_a = term;
    let a = hc.literal(a);
    let minus_a = hc.literal(minus_a);
    assert_eq!(minus_a.data(), &a.data().neg());
}

/// derive `-a => term` from `a => a_term` and `-a_term => term`
pub(super) fn check_neg_eq<'db, Src>(
    prop: VdMirExprIdx,
    opd_nf: VdMirTermDerivationIdx,
    minus_opd_nf_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (minus_a => term) = prop, hc);
    ds!(let (-a) = minus_a, hc);
    ds!(let (a1 => a_term) = opd_nf.prop(hc), hc);
    ds!(let (minus_a_term => term1) = minus_opd_nf_nf.prop(hc), hc);
    ds!(let (-a_term1) = minus_a_term, hc);
    assert_deep_eq!(a_term1, a_term, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(term1, term, hc);
}

/// derive `-a => term` from `(-1) * a => term`
pub(super) fn check_neg_atom<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}

/// derive `-(a + b) => neg_a_term + neg_b_term` from `-a => neg_a_term` and `-b => neg_b_term`
pub(super) fn check_neg_sum<'db, Src>(
    prop: VdMirExprIdx,
    neg_a_nf: VdMirTermDerivationIdx,
    neg_b_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    p!(hc.fmt_expr(prop));
    ds!(let (expr => term) = prop, hc);
    ds!(let (-a_plus_b) = expr, hc);
    ds!(let (a + b) = a_plus_b, hc);
    ds!(let (neg_a_term + neg_b_term) = term, hc);
    ds!(let (neg_a => neg_a_term1) = neg_a_nf.prop(hc), hc);
    ds!(let (neg_b => neg_b_term1) = neg_b_nf.prop(hc), hc);
    ds!(let (-a1) = neg_a_term1, hc);
    ds!(let (-b1) = neg_b_term1, hc);
    assert_deep_eq!(neg_a_term1, neg_a_term, hc);
    assert_deep_eq!(neg_b_term1, neg_b_term, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
}

/// derive `-(c * a) => (-c) * a` if `c` is a litnum
pub(super) fn check_neg_product<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (-c_mul_a) = expr, hc);
    ds!(let (c * a) = c_mul_a, hc);
    ds!(let (minus_c * a1) = term, hc);
    assert_deep_eq!(a1, a, hc);
    let c = hc.literal(c);
    let minus_c = hc.literal(minus_c);
    assert_eq!(minus_c.data(), &c.data().neg());
}

/// derive `-(a^b) => (-1) * a^b`
pub(super) fn check_neg_exponential<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (-a_pow_b) = expr, hc);
    ds!(let (minus_one * a_pow_b1) = term, hc);
    assert!(hc.literal(minus_one).is_i128(-1));
    assert_deep_eq!(a_pow_b1, a_pow_b, hc);
}

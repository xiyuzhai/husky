use super::*;
use hypothesis::VdMirHypothesisIdx;

/// derive `a / b => term` from `a => a_term`, `b => b_term` and `a_term / b_term => term`
pub(super) fn check_div_eq<'db, Src>(
    prop: VdMirExprIdx,
    numerator_dn: VdMirTermDerivationIdx,
    denominator_dn: VdMirTermDerivationIdx,
    numerator_dn_div_denominator_dn_dn: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a / b) = expr, hc);
    ds!(let (a1 => a_term) = numerator_dn.prop(hc), hc);
    ds!(let (b1 => b_term) = denominator_dn.prop(hc), hc);
    ds!(let (a_term_div_b_term => term1) = numerator_dn_div_denominator_dn_dn.prop(hc), hc);
    ds!(let (a_term1 / b_term1) = a_term_div_b_term, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
    assert_deep_eq!(term1, term, hc);
    assert_deep_eq!(a_term1, a_term, hc);
    assert_deep_eq!(b_term1, b_term, hc);
}

/// derive `a / b => term` from `a * b⁻¹ => term` if `b` is a literal
pub(super) fn check_div_literal<'db, Src>(
    prop: VdMirExprIdx,
    a_mul_b_inv_dn: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    p!(hc.fmt_expr(prop), hc.fmt_expr(a_mul_b_inv_dn.prop(hc)));
    ds!(let (expr => term) = prop, hc);
    ds!(let (a / b) = expr, hc);
    ds!(let (a_mul_b_inv => term1) = a_mul_b_inv_dn.prop(hc), hc);
    ds!(let (a1 * b_inv) = a_mul_b_inv, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(term1, term, hc);
    let b = hc.literal(b);
    let b_inv = hc.literal(b_inv);
    assert_eq!(b_inv.data(), &b.data().inv().unwrap());
}

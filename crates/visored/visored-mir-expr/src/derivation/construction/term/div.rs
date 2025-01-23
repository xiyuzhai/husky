use super::*;
use hypothesis::VdMirHypothesisIdx;

pub(super) fn check_div_eq<'db, Src>(
    prop: VdMirExprIdx,
    numerator_dn: VdMirTermDerivationIdx,
    denominator_dn: VdMirTermDerivationIdx,
    numerator_dn_div_denominator_dn_dn: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}

/// derive `a / b => term` from `a * b⁻¹ => term` if `b` is a literal
pub(super) fn check_div_literal<'db, Src>(
    prop: VdMirExprIdx,
    a_mul_b_inv_dn: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (lhs => term) = prop, hc);
    ds!(let (a / b) = lhs, hc);
    ds!(let (a_mul_b_inv => term1) = a_mul_b_inv_dn.prop(hc), hc);
    ds!(let (a1 * b_inv) = a_mul_b_inv, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(term1, term, hc);
    let b = hc.literal(b);
    let b_inv = hc.literal(b_inv);
    assert_eq!(b_inv.data(), &b.data().inv().unwrap());
}

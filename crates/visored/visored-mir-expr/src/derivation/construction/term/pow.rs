use super::*;

pub(super) fn check_non_reduced_power<'db, Src>(
    prop: VdMirExprIdx,
    base_nf: VdMirTermDerivationIdx,
    exponent_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (base ^ exponent) = expr, hc);
    ds!(let (one * stem) = term, hc);
    assert!(hc.is_one(one));
    ds!(let (base_term ^ exponent_term) = stem, hc);
    ds!(let (base1 => base_term1) = base_nf.prop(hc), hc);
    ds!(let (exponent1 => exponent_term1) = exponent_nf.prop(hc), hc);
    assert_deep_eq!(base, base1, hc);
    assert_deep_eq!(base_term1, base_term, hc);
    assert_deep_eq!(exponent, exponent1, hc);
    assert_deep_eq!(exponent_term1, exponent_term, hc);
}

pub(super) fn check_power_one<'db, Src>(
    prop: VdMirExprIdx,
    base_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (base ^ one) = expr, hc);
    assert!(hc.is_one(one));
    ds!(let (base1 => term1) = base_nf.prop(hc), hc);
    assert_deep_eq!(base, base1, hc);
    assert_deep_eq!(term1, term, hc);
}

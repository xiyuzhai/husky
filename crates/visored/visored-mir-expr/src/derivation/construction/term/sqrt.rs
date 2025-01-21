use super::*;

pub(super) fn check_sqrt<'db, Src>(
    prop: VdMirExprIdx,
    radicand_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (sqrt radicand) = expr, hc);
    ds!(let (c * stem) = term, hc);
    assert!(hc.literal(c).is_one());
    ds!(let (radicand_term ** one_half) = stem, hc);
    assert!(hc.literal(one_half).is_one_half());
    ds!(let (radicand1 => radicand_term1) = radicand_nf.prop(hc), hc);
    assert_deep_eq!(radicand, radicand1, hc);
    assert_deep_eq!(radicand_term, radicand_term1, hc);
}

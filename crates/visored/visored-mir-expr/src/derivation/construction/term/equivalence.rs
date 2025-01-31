use super::*;

pub(super) fn check_non_trivial_hypothesis_equivalence<'db, Src>(
    prop: VdMirExprIdx,
    src: VdMirHypothesisIdx,
    src_nf: VdMirTermDerivationIdx,
    dst_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (src_expr => src_term) = src_nf.prop(hc), hc);
    assert_deep_eq!(hc.hypothesis_arena()[src].expr(), src_expr, hc);
    ds!(let (dst_expr => dst_term) = dst_nf.prop(hc), hc);
    assert_deep_eq!(prop, dst_expr, hc);
    assert_deep_eq!(src_term, dst_term, hc);
}

pub(super) fn check_expr_equivalence<'db, Src>(
    prop: VdMirExprIdx,
    src_nf: VdMirTermDerivationIdx,
    dst_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    // todo!()
}

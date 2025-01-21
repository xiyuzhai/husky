use super::*;

/// derive `1 * b => b`
pub(super) fn check_one_mul_atom<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (one * b) = expr, hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(term, b, hc);
}

/// derive `c * b => c * b^1` if `c` is a constant
pub(super) fn check_nonone_literal_mul_atom<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (c * b) = expr, hc);
    let c = hc.literal(c);
    assert!(!c.is_one());
    use husky_print_utils::*;
    p!(hc.show_expr_lisp(term));
    ds!(let (c1 * b_pow_1) = term, hc);
    ds!(let (b1 ^ one) = b_pow_1, hc);
    assert!(hc.literal(one).is_one());
    todo!()
}

/// derive `a * b => term` from `a => term_a`, `b => term_b` and `term_a * term_b => term`
pub(super) fn check_mul_eq<'db, Src>(
    prop: VdMirExprIdx,
    // `a => term_a`
    lopd: VdMirTermDerivationIdx,
    // `b => term_b`
    ropd: VdMirTermDerivationIdx,
    // `term_a * term_b => term`
    merge: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a * b) = expr, hc);
    ds!(let (a1 => term_a) = lopd.prop(hc), hc);
    assert_deep_eq!(a1, a, hc);
    ds!(let (b1 => term_b) = ropd.prop(hc), hc);
    assert_deep_eq!(b1, b, hc);
    ds!(let (merge_lhs => term1) = merge.prop(hc), hc);
    assert_deep_eq!(term1, term, hc);
    ds!(let (term_a1 * term_b1) = merge_lhs, hc);
    assert_deep_eq!(term_a1, term_a, hc);
    assert_deep_eq!(term_b1, term_b, hc);
}

use super::*;

/// derive `1 * b => b`
pub(super) fn check_one_mul_atom<'db, Src>(
    expr: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    term: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::EQ);
    ds!(let (one * b) = expr, hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(term, b, hc);
}

/// derive `c * b => c * b^1` if `c` is a constant
pub(super) fn check_nonone_literal_mul_atom<'db, Src>(
    expr: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    term: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::EQ);
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

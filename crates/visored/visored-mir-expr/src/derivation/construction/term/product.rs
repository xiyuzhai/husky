use visored_mir_opr::separator::folding::VdMirBaseFoldingSeparator;

use super::*;

pub(super) fn check_literal_mul_literal<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a * b) = expr, hc);
    let a = hc.literal(a);
    let b = hc.literal(b);
    let term = hc.literal(term);
    assert_eq!(&a.data().mul(b.data()), term.data());
}

/// derive `1 * a => term` from `a => term`
pub(super) fn check_one_mul<'db, Src>(
    prop: VdMirExprIdx,
    a_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (one * a) = expr, hc);
    ds!(let (a1 => term1) = a_nf.prop(hc), hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(term1, term, hc);
    assert_deep_eq!(a1, a, hc);
}

/// derive `c * b => c * b^1` if `c` is a constant
pub(super) fn check_nonone_literal_mul_atom<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (c * b) = expr, hc);
    ds!(let (c1 * b_pow_1) = term, hc);
    ds!(let (b1 ^ one) = b_pow_1, hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(c1, c, hc);
    assert_deep_eq!(b1, b, hc);
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

/// derive `a * b => 1 * a^1 * b^1` if `a` and `b` are atoms with the term order of `a` being lesser than `b`
/// derive `a * b => 1 * b^1 * a^1` if `a` and `b` are atoms with the term order of `a` being greater than `b`
/// derive `a * a => 1 * a^2`
pub(super) fn check_atom_mul_atom<'db, Src>(
    prop: VdMirExprIdx,
    comparison: core::cmp::Ordering,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a * b) = expr, hc);
    match comparison {
        std::cmp::Ordering::Less => {
            ds!(let (one * stem) = term, hc);
            assert!(hc.literal(one).is_one());
            ds!(let (a1_pow_1 * b1_pow_1) = stem, hc);
            ds!(let (a1 ^ one) = a1_pow_1, hc);
            assert!(hc.literal(one).is_one());
            ds!(let (b1 ^ one) = b1_pow_1, hc);
            assert!(hc.literal(one).is_one());
            assert_deep_eq!(a1, a, hc);
            assert_deep_eq!(b1, b, hc);
        }
        std::cmp::Ordering::Equal => todo!(),
        std::cmp::Ordering::Greater => {
            ds!(let (c * stem) = term, hc);
            assert!(hc.literal(c).is_one());
            ds!(let (b1_pow_1 * a1_pow_1) = stem, hc);
            ds!(let (b1 ^ one) = b1_pow_1, hc);
            assert!(hc.literal(one).is_one());
            ds!(let (a1 ^ one) = a1_pow_1, hc);
            assert!(hc.literal(one).is_one());
            assert_deep_eq!(a1, a, hc);
            assert_deep_eq!(b1, b, hc);
        }
    }
}

/// derive `a * (b * c) => term` from `a * b => lterm` and `lterm * c => term`
pub(super) fn check_mul_assoc<'db, Src>(
    prop: VdMirExprIdx,
    rsignature: VdBaseFoldingSeparatorSignature,
    merge_rlopd_nf: VdMirTermDerivationIdx,
    merge_rropd_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a * expr_rhs) = expr, hc);
    ds!(let (b * c) = expr_rhs, hc);
    ds!(let (lopd1 => lterm) = merge_rlopd_nf.prop(hc), hc);
    ds!(let (a1 * b1) = lopd1, hc);
    ds!(let (lhs => term1) = merge_rropd_nf.prop(hc), hc);
    ds!(let (lterm1 * c1) = lhs, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
    assert_deep_eq!(lterm1, lterm, hc);
    assert_deep_eq!(c1, c, hc);
    assert_deep_eq!(term1, term, hc);
}

/// derive `c * a * b => c * (a * b)` if `a` and `b` are exponentials with `a`'s base being less than `b`'s base
pub(super) fn check_simple_product_mul_exponential_less<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (c_mul_a * b) = expr, hc);
    ds!(let (c * a) = c_mul_a, hc);
    ds!(let (c1 * a_mul_b) = term, hc);
    ds!(let (a1 * b1) = a_mul_b, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
    assert_deep_eq!(c1, c, hc);
}

/// derive `c * a * b => c * (b * a)` if `a` and `b` are exponentials with `a`'s base being greater than `b`'s base
pub(super) fn check_simple_product_mul_exponential_greater<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}

/// derive `c * a * b => c * (a * b^1)`
pub(super) fn check_simple_product_mul_base_less<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (c_mul_a * b) = expr, hc);
    ds!(let (c * a) = c_mul_a, hc);
    ds!(let (c1 * a_mul_b_pow_one) = term, hc);
    ds!(let (a1 * b_pow_one) = a_mul_b_pow_one, hc);
    ds!(let (b1 ^ one) = b_pow_one, hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
    assert_deep_eq!(c1, c, hc);
}

/// derive `c * a * b => c * (b^1 * a)`
pub(super) fn check_simple_product_mul_base_greater<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    todo!()
}

/// derive `a * c` => `c * a^1`
pub(super) fn check_base_mul_literal<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a * c) = expr, hc);
    ds!(let (c1 * a_pow_one) = term, hc);
    ds!(let (a1 ^ one) = a_pow_one, hc);
    assert!(hc.is_one(one));
    assert_deep_eq!(a1, a, hc);
    let c = hc.literal(c);
    let c1 = hc.literal(c1);
    assert_eq!(c1, c);
}

/// derive `a * (b + c) => ab_term + ac_term` from `a * b => ab_term` and `a * c => ac_term`
pub(super) fn check_literal_mul_sum<'db, Src>(
    prop: VdMirExprIdx,
    a_mul_b_derivation: VdMirTermDerivationIdx,
    a_mul_c_derivation: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a * b_add_c) = expr, hc);
    ds!(let (b + c) = b_add_c, hc);
    ds!(let (a_mul_b => ab_term) = a_mul_b_derivation.prop(hc), hc);
    ds!(let (a_mul_c => ac_term) = a_mul_c_derivation.prop(hc), hc);
    ds!(let (ab_term1 + ac_term1) = term, hc);
    ds!(let (a1 * b1) = a_mul_b, hc);
    ds!(let (a2 * c1) = a_mul_c, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(a2, a, hc);
    assert_deep_eq!(b1, b, hc);
    assert_deep_eq!(c1, c, hc);
    assert_deep_eq!(ab_term1, ab_term, hc);
    assert_deep_eq!(ac_term1, ac_term, hc);
}

/// derive `a + b => b + a` if `b` is a product and `a` is a literal
pub(super) fn check_product_add_literal<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a + b) = expr, hc);
    ds!(let (b1 + a1) = term, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
}

/// derive `a * b => 1 * (a^1 * b)`
pub(super) fn check_atom_mul_exponential_less<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a * b) = expr, hc);
    ds!(let (one * stem) = term, hc);
    assert!(hc.literal(one).is_one());
    ds!(let (a_pow_one * b1) = stem, hc);
    ds!(let (a1 ^ one) = a_pow_one, hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
}

/// derive `a * b => 1 * (b * a^1)`
pub(super) fn check_atom_mul_exponential_greater<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a * b) = expr, hc);
    ds!(let (one * stem) = term, hc);
    assert!(hc.literal(one).is_one());
    ds!(let (b1 * a_pow_one) = stem, hc);
    ds!(let (a1 ^ one) = a_pow_one, hc);
    assert!(hc.literal(one).is_one());
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
}

/// derive `a / b => term` from `a * b⁻¹ => term` if `b` is an atom
pub(super) fn check_div_atom<'db, Src>(
    prop: VdMirExprIdx,
    a_mul_b_inv_dn: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    ds!(let (a / b) = expr, hc);
    ds!(let (mul_expr => term1) = a_mul_b_inv_dn.prop(hc), hc);
    ds!(let (a1 * b_inv) = mul_expr, hc);
    ds!(let (b1 ^ neg_one) = b_inv, hc);
    assert!(hc.literal(neg_one).is_neg_one());
    assert_deep_eq!(term1, term, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
}

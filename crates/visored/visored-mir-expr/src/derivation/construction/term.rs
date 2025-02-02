mod div;
pub mod equivalence;
pub mod neg;
pub mod pow;
pub mod product;
mod sqrt;
pub mod sub;
pub mod sum;

use self::{div::*, equivalence::*, neg::*, pow::*, product::*, sqrt::*, sub::*, sum::*};
use super::*;
use crate::{
    derivation::VdMirDerivationIdx,
    expr::VdMirExprData,
    helpers::compare::{assert_deep_eq, vd_mir_expr_deep_eq},
    hypothesis::constructor::expr::ds,
};
use coercion::{
    pow::VdMirPowCoercion, triangle::VdMirCoercionTriangle, VdMirBinaryOprCoercion, VdMirCoercion,
    VdMirPrefixOprCoercion, VdMirSeparatorCoercion,
};
use hypothesis::VdMirHypothesisIdx;
use visored_mir_opr::separator::chaining::{
    VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
};
use visored_signature::signature::separator::base::{
    chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
};
use visored_term::term::literal::VdLiteral;

#[derive(Debug, PartialEq, Eq, strum::IntoStaticStr)]
pub enum VdMirTermDerivationConstruction {
    Reflection,
    NumComparison {
        lhs_nf: VdMirTermDerivationIdx,
        rhs_nf: VdMirTermDerivationIdx,
        lhs_nf_minus_rhs_nf_nf: VdMirTermDerivationIdx,
    },
    /// derive `a - b => term` from `a + (-b) => term`
    SubEqsAddNeg {
        add_neg: VdMirTermDerivationIdx,
        b_neg_coercion: VdMirPrefixOprCoercion,
    },
    LiteralAddLiteral {
        lopd: VdLiteral,
        ropd: VdLiteral,
    },
    /// derive `a + b => term` from `a => term_a`, `b => term_b` and `a_term + b_term => term`
    AddEq {
        a_eq_coercion: VdMirSeparatorCoercion,
        b_eq_coercion: VdMirSeparatorCoercion,
        a_derivation: VdMirTermDerivationIdx,
        b_derivation: VdMirTermDerivationIdx,
        a_term_add_b_term_derivation: VdMirTermDerivationIdx,
    },
    AdditionInterchange,
    AdditionAssociativity,
    AdditionIdentity,
    AdditionInverse,
    AdditionDistributivity,
    /// derive `a + c => c + 1 * a^1` if `a` is an atom and `c` is a nonzero literal
    AtomAddNonZeroLiteral,
    /// derive `a + b => 0 + 1 * a^1 + b` if `a` is an atom and `b` is a product with higher stem
    AtomAddProductLess {
        zero_add_one_mul_a_pow_one_add_coercion: VdMirSeparatorCoercion,
        one_mul_a_pow_one_add_coercion: VdMirSeparatorCoercion,
        one_a_ac_coercion_triangle: VdMirCoercionTriangle,
        a_pow_one_pow_coercion: VdMirPowCoercion,
    },
    /// derive `a + b => 0 + c * a^1` if `a` is an atom and `b` is a product with same stem and coefficient d=c-1 and `c` is nonzero
    AtomAddProductEqualKeep,
    /// derive `a + b => 0` if `a` is an atom and `b` is a product with same stem and coefficient d=-1
    AtomAddProductEqualCancel,
    /// derive `a + b => 0 + b + 1 * a^1` if `a` is an atom and `b` is a product with lower stem
    AtomAddProductGreater,
    /// derive `a + b * x + c * x => a + (b + c) * x`
    SumAddProductEqualKeep,
    /// derive `a + b * x + c * x => a` if `b + c` is zero
    SumAddProductEqualCancel,
    /// derive `a + b + c => term` from `a + c => term_ac` and `term_ac + b => term`
    SumAddProductGreater {
        a_add_c_nf: VdMirTermDerivationIdx,
        term_ac_add_b_nf: VdMirTermDerivationIdx,
    },
    LiteralMulLiteral,
    MulEq {
        a: VdMirTermDerivationIdx,
        b: VdMirTermDerivationIdx,
        a_eq_coercion: VdMirSeparatorCoercion,
        b_eq_coercion: VdMirSeparatorCoercion,
        merge: VdMirTermDerivationIdx,
    },
    /// derive `a * c` => `c * a^1`
    BaseMulLiteral,
    /// derive `1 * a => term` from `a => term`
    OneMul {
        a_nf: VdMirTermDerivationIdx,
    },
    /// derive `c * b => c * b^1` if `c` is a litnum
    NonOneLiteralMulAtom,
    /// derive `a + 0 => a`
    NfAddZero,
    /// derive `src_nf ↔ dst_nf`
    NonTrivialHypothesisEquivalence {
        src: VdMirHypothesisIdx,
        src_nf: VdMirTermDerivationIdx,
        dst_nf: VdMirTermDerivationIdx,
    },
    NonTrivialExprEquivalence {
        src_nf: VdMirTermDerivationIdx,
        dst_nf: VdMirTermDerivationIdx,
    },
    /// derive `a * b => 1 * a^1 * b^1` if `a` and `b` are atoms with the term order of `a` being lesser than `b`
    /// derive `a * b => 1 * b^1 * a^1` if `a` and `b` are atoms with the term order of `a` being greater than `b`
    /// derive `a * a => 1 * a^2`
    AtomMulAtom {
        comparison: core::cmp::Ordering,
    },
    Sqrt {
        radicand_nf: VdMirTermDerivationIdx,
    },
    /// derive `a * (b * c) => term` from `a * b => ab_term` and `ab_term * c => term`
    MulProduct {
        rsignature: VdBaseFoldingSeparatorSignature,
        ab_nf: VdMirTermDerivationIdx,
        ab_term_mul_c_nf: VdMirTermDerivationIdx,
        ab_eq_coercion: VdMirSeparatorCoercion,
        ab_mul_coercion: VdMirSeparatorCoercion,
        bc_mul_coercion: VdMirSeparatorCoercion,
    },
    NonReducedPower {
        base: VdMirTermDerivationIdx,
        exponent: VdMirTermDerivationIdx,
    },
    PowerOne {
        base: VdMirTermDerivationIdx,
    },
    NegLiteral,
    /// derive `-a => term` from `a => a_term` and `-a_term => term`
    NegEq {
        opd_nf: VdMirTermDerivationIdx,
        neg_a_term_nf: VdMirTermDerivationIdx,
    },
    /// derive `-a => (-1) * a^1`
    NegAtom,
    /// derive `-(a + b) => neg_a_term + neg_b_term` from `-a => neg_a_term` and `-b => neg_b_term`
    NegSum {
        neg_a_nf: VdMirTermDerivationIdx,
        neg_b_nf: VdMirTermDerivationIdx,
    },
    /// derive `-(c * a) => (-c) * a` if `c` is a litnum
    NegProduct,
    /// derive `-(a^b) => (-1) * a^b`
    NegExponential,
    /// derive `0 + a => term` from `a => term`
    ZeroAdd {
        a_nf: VdMirTermDerivationIdx,
    },
    /// derive `a + b => term` from `a + 1 * b^1 => term` if `b` is an atom
    AddAtom {
        add_product_nf: VdMirTermDerivationIdx,
    },
    /// derive `a + b => 0 + a + b` if `a` and `b` are products and the stem of `a` is less than the stem of `b`
    ProductAddProductLess {
        zero_add_a_add_coercion: VdMirSeparatorCoercion,
    },
    ProductAddProductEqualKeep,
    ProductAddProductEqualCancel,
    /// derive `a + b => 0 + b + a` if `a` and `b` are products and the stem of `a` is greater than the stem of `b`
    ProductAddProductGreater {
        zero_add_b_add_coercion: VdMirSeparatorCoercion,
    },
    /// derive `c * a * b => c * (a * b)` if `a` and `b` are exponentials with `a`'s base being less than `b`'s base
    SimpleProductMulExponentialLess,
    /// derive `c * a * b => c * (b * a)` if `a` and `b` are exponentials with `a`'s base being greater than `b`'s base
    SimpleProductMulExponentialGreater,
    /// derive `c * a * b => c * (a * b^1)`
    SimpleProductMulBaseLess,
    /// derive `c * a * b => c * (b^1 * a)`
    SimpleProductMulBaseGreater,
    /// derive `a + (b + c) => term` from `a + b => term_ab` and `term_ab + c => term`
    AddSum {
        a_add_b_derivation: VdMirTermDerivationIdx,
        a_add_b_derived_add_c_derivation: VdMirTermDerivationIdx,
    },
    /// derive `a / b => term` from `a => a_term`, `b => b_term` and `a_term / b_term => term`
    DivEq {
        a_dn: VdMirTermDerivationIdx,
        b_dn: VdMirTermDerivationIdx,
        a_eq_coercion: VdMirSeparatorCoercion,
        b_eq_coercion: VdMirSeparatorCoercion,
        a_nf_div_b_nf_dn: VdMirTermDerivationIdx,
    },
    /// derive `a / b => term` from `a * b⁻¹ => term` if `b` is a literal
    DivLiteral {
        a_mul_b_inv_dn: VdMirTermDerivationIdx,
    },
    /// derive `p => term` from `p => a * (b + c)^1` `a * b => ab_term` and `a * c => ac_term` and `ab_term + ac_term => term`
    LiteralMulSum {
        p_derivation: VdMirTermDerivationIdx,
        a_mul_b_derivation: VdMirTermDerivationIdx,
        a_mul_c_derivation: VdMirTermDerivationIdx,
        ab_term_plus_ac_term_derivation: VdMirTermDerivationIdx,
        pow_coercion: VdMirPowCoercion,
        bc_add_coercion: VdMirSeparatorCoercion,
        ab_eq_coercion: VdMirSeparatorCoercion,
        ab_mul_coercion: VdMirSeparatorCoercion,
        ac_eq_coercion: VdMirSeparatorCoercion,
        ac_mul_coercion: VdMirSeparatorCoercion,
        a_ab_abc_coercion_triangle: VdMirCoercionTriangle,
        a_ac_abc_coercion_triangle: VdMirCoercionTriangle,
        b_ab_abc_coercion_triangle: VdMirCoercionTriangle,
        b_bc_abc_coercion_triangle: VdMirCoercionTriangle,
        c_ac_abc_coercion_triangle: VdMirCoercionTriangle,
        c_bc_abc_coercion_triangle: VdMirCoercionTriangle,
        p_coercion: VdMirSeparatorCoercion,
    },
    /// derive `a + b + c => term` from `a + c => ac_term` and `ac_term + b => term`
    SumAddLiteral {
        a_add_c_derivation: VdMirTermDerivationIdx,
        a_add_c_derived_add_b_derivation: VdMirTermDerivationIdx,
        a_add_b_add_coercion: VdMirSeparatorCoercion,
        a_ab_abc_coercion_triangle: VdMirCoercionTriangle,
        b_ab_abc_coercion_triangle: VdMirCoercionTriangle,
        ac_eq_coercion: VdMirSeparatorCoercion,
        ac_add_coercion: VdMirSeparatorCoercion,
        a_ac_abc_coercion_triangle: VdMirCoercionTriangle,
        c_ac_abc_coercion_triangle: VdMirCoercionTriangle,
    },
    /// derive `a + b => b + a` if `b` is a product and `a` is a literal
    ProductAddLiteral,
    /// derive `a / b => term` from `a * b⁻¹ => term` if `b` is an atom
    DivAtom {
        a_mul_b_inv_dn: VdMirTermDerivationIdx,
    },
    /// derive `a * b => 1 * (a^1 * b)`
    AtomMulExponentialLess,
    /// derive `a * b => 1 * (b * a^1)`
    AtomMulExponentialGreater,
    /// derive `1 * a^1 => a`
    OneMulPowerOne,
    /// derive `a * 1 => a`
    MulOne,
    /// derive `(c * a) * d => e * a` if `c`, `d` and `e` are literals and `e` is equal to `c * d`
    SimpleProductMulLiteral {
        c_mul_a_mul_coercion: VdMirSeparatorCoercion,
        e_mul_a_mul_coercion: VdMirSeparatorCoercion,
        a_ae_acd_coercion_triangle: VdMirCoercionTriangle,
        a_ac_acd_coercion_triangle: VdMirCoercionTriangle,
        e_ae_acd_coercion_triangle: VdMirCoercionTriangle,
    },
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub struct VdMirTermDerivationIdx(VdMirDerivationIdx);

impl std::ops::Deref for VdMirTermDerivationIdx {
    type Target = VdMirDerivationIdx;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn alloc_term_derivation(
        &mut self,
        prop: VdMirExprIdx,
        construction: VdMirTermDerivationConstruction,
    ) -> VdMirTermDerivationIdx {
        let idx = self.alloc_derivation(prop, construction.into());
        VdMirTermDerivationIdx(idx)
    }
}

impl VdMirTermDerivationIdx {
    pub fn prop<'db, 'a, Src>(self, hc: &'a VdMirHypothesisConstructor<'db, Src>) -> VdMirExprIdx {
        hc.derivation_arena()[*self].prop()
    }

    pub fn construction<'db, 'a, Src>(
        self,
        hc: &'a VdMirHypothesisConstructor<'db, Src>,
    ) -> &'a VdMirTermDerivationConstruction {
        match hc.derivation_arena()[*self].construction() {
            VdMirDerivationConstruction::Term(construction) => construction,
            _ => unreachable!(),
        }
    }
}

impl VdMirTermDerivationConstruction {
    pub fn check<'db, Src>(
        &self,
        prop: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, Src>,
    ) {
        match *self {
            VdMirTermDerivationConstruction::Reflection => check_reflection(prop, hc),
            VdMirTermDerivationConstruction::LiteralAddLiteral { lopd, ropd } => {
                check_literal_add_literal(prop, hc)
            }
            VdMirTermDerivationConstruction::NumComparison {
                lhs_nf,
                rhs_nf,
                lhs_nf_minus_rhs_nf_nf,
            } => check_num_comparison(prop, lhs_nf, rhs_nf, lhs_nf_minus_rhs_nf_nf, hc),
            VdMirTermDerivationConstruction::SubEqsAddNeg {
                add_neg,
                b_neg_coercion,
            } => check_sub_eqs_add_neg(prop, add_neg, hc),
            VdMirTermDerivationConstruction::AdditionInterchange => check_add_interchange(prop, hc),
            VdMirTermDerivationConstruction::AdditionAssociativity => todo!(),
            VdMirTermDerivationConstruction::AdditionIdentity => todo!(),
            VdMirTermDerivationConstruction::AdditionInverse => todo!(),
            VdMirTermDerivationConstruction::AdditionDistributivity => todo!(),
            VdMirTermDerivationConstruction::NegLiteral => check_neg_literal(prop, hc),
            VdMirTermDerivationConstruction::NegEq {
                opd_nf,
                neg_a_term_nf,
            } => check_neg_eq(prop, opd_nf, neg_a_term_nf, hc),
            VdMirTermDerivationConstruction::NegAtom => check_neg_atom(prop, hc),
            VdMirTermDerivationConstruction::NegSum { neg_a_nf, neg_b_nf } => {
                check_neg_sum(prop, neg_a_nf, neg_b_nf, hc)
            }
            VdMirTermDerivationConstruction::NegProduct => check_neg_product(prop, hc),
            VdMirTermDerivationConstruction::NegExponential => check_neg_exponential(prop, hc),
            VdMirTermDerivationConstruction::AddEq {
                a_derivation: lopd,
                b_derivation: ropd,
                a_term_add_b_term_derivation: merge,
                ..
            } => check_add_eq(prop, lopd, ropd, merge, hc),
            VdMirTermDerivationConstruction::AtomAddNonZeroLiteral => {
                check_atom_add_non_zero_literal(prop, hc)
            }
            VdMirTermDerivationConstruction::LiteralMulLiteral => {
                check_literal_mul_literal(prop, hc)
            }
            VdMirTermDerivationConstruction::MulEq {
                a,
                b,
                a_eq_coercion,
                b_eq_coercion,
                merge,
            } => check_mul_eq(prop, a, b, merge, hc),
            VdMirTermDerivationConstruction::BaseMulLiteral => check_base_mul_literal(prop, hc),
            VdMirTermDerivationConstruction::OneMul { a_nf } => check_one_mul(prop, a_nf, hc),
            VdMirTermDerivationConstruction::NonOneLiteralMulAtom => {
                check_nonone_literal_mul_atom(prop, hc)
            }
            VdMirTermDerivationConstruction::NfAddZero => check_nf_add_zero(prop, hc),
            VdMirTermDerivationConstruction::NonTrivialHypothesisEquivalence {
                src,
                src_nf,
                dst_nf,
            } => check_non_trivial_hypothesis_equivalence(prop, src, src_nf, dst_nf, hc),
            VdMirTermDerivationConstruction::AtomMulAtom { comparison } => {
                check_atom_mul_atom(prop, comparison, hc)
            }
            VdMirTermDerivationConstruction::Sqrt { radicand_nf } => {
                check_sqrt(prop, radicand_nf, hc)
            }
            VdMirTermDerivationConstruction::MulProduct {
                rsignature,
                ab_nf,
                ab_term_mul_c_nf,
                ab_eq_coercion,
                ab_mul_coercion,
                bc_mul_coercion,
            } => check_mul_assoc(prop, rsignature, ab_nf, ab_term_mul_c_nf, hc),
            VdMirTermDerivationConstruction::NonReducedPower { base, exponent } => {
                check_non_reduced_power(prop, base, exponent, hc)
            }
            VdMirTermDerivationConstruction::PowerOne { base } => check_power_one(prop, base, hc),
            VdMirTermDerivationConstruction::AtomAddProductLess {
                zero_add_one_mul_a_pow_one_add_coercion,
                one_mul_a_pow_one_add_coercion,
                one_a_ac_coercion_triangle,
                a_pow_one_pow_coercion,
            } => check_atom_add_product_less(prop, hc),
            VdMirTermDerivationConstruction::AtomAddProductEqualKeep => {
                check_atom_add_product_equal_keep(prop, hc)
            }
            VdMirTermDerivationConstruction::AtomAddProductEqualCancel => {
                check_atom_add_product_equal_cancel(prop, hc)
            }
            VdMirTermDerivationConstruction::AtomAddProductGreater => {
                check_atom_add_product_greater(prop, hc)
            }
            VdMirTermDerivationConstruction::SumAddProductGreater {
                a_add_c_nf,
                term_ac_add_b_nf,
            } => check_sum_add_product_greater(prop, a_add_c_nf, term_ac_add_b_nf, hc),
            VdMirTermDerivationConstruction::ZeroAdd { a_nf } => check_zero_add(prop, a_nf, hc),
            VdMirTermDerivationConstruction::AddAtom { add_product_nf } => {
                check_add_atom(prop, add_product_nf, hc)
            }
            VdMirTermDerivationConstruction::SumAddProductEqualKeep => todo!(),
            VdMirTermDerivationConstruction::SumAddProductEqualCancel => todo!(),
            VdMirTermDerivationConstruction::ProductAddProductLess {
                zero_add_a_add_coercion,
            } => check_product_add_product_less(prop, hc),
            VdMirTermDerivationConstruction::ProductAddProductEqualKeep => todo!(),
            VdMirTermDerivationConstruction::ProductAddProductEqualCancel => todo!(),
            VdMirTermDerivationConstruction::ProductAddProductGreater {
                zero_add_b_add_coercion,
            } => check_product_add_product_greater(prop, hc),
            VdMirTermDerivationConstruction::SimpleProductMulExponentialLess => {
                check_simple_product_mul_exponential_less(prop, hc)
            }
            VdMirTermDerivationConstruction::SimpleProductMulExponentialGreater => {
                check_simple_product_mul_exponential_greater(prop, hc)
            }
            VdMirTermDerivationConstruction::SimpleProductMulBaseLess => {
                check_simple_product_mul_base_less(prop, hc)
            }
            VdMirTermDerivationConstruction::SimpleProductMulBaseGreater => {
                check_simple_product_mul_base_greater(prop, hc)
            }
            VdMirTermDerivationConstruction::AddSum {
                a_add_b_derivation,
                a_add_b_derived_add_c_derivation,
            } => check_add_sum(
                prop,
                a_add_b_derivation,
                a_add_b_derived_add_c_derivation,
                hc,
            ),
            VdMirTermDerivationConstruction::DivEq {
                a_dn,
                b_dn,
                a_eq_coercion: a_coercion,
                b_eq_coercion: b_coercion,
                a_nf_div_b_nf_dn,
            } => check_div_eq(prop, a_dn, b_dn, a_nf_div_b_nf_dn, hc),
            VdMirTermDerivationConstruction::DivLiteral { a_mul_b_inv_dn } => {
                check_div_literal(prop, a_mul_b_inv_dn, hc)
            }
            VdMirTermDerivationConstruction::LiteralMulSum {
                p_derivation,
                a_mul_b_derivation,
                a_mul_c_derivation,
                ab_term_plus_ac_term_derivation,
                pow_coercion,
                a_ab_abc_coercion_triangle,
                a_ac_abc_coercion_triangle,
                b_ab_abc_coercion_triangle,
                b_bc_abc_coercion_triangle,
                c_ac_abc_coercion_triangle,
                c_bc_abc_coercion_triangle,
                p_coercion,
                bc_add_coercion,
                ab_eq_coercion,
                ab_mul_coercion,
                ac_eq_coercion,
                ac_mul_coercion,
            } => check_literal_mul_sum(
                prop,
                p_derivation,
                a_mul_b_derivation,
                a_mul_c_derivation,
                ab_term_plus_ac_term_derivation,
                hc,
            ),
            VdMirTermDerivationConstruction::SumAddLiteral {
                a_add_c_derivation,
                a_add_c_derived_add_b_derivation,
                a_add_b_add_coercion,
                a_ab_abc_coercion_triangle,
                b_ab_abc_coercion_triangle,
                ac_eq_coercion,
                ac_add_coercion,
                a_ac_abc_coercion_triangle,
                c_ac_abc_coercion_triangle,
            } => check_sum_add_literal(
                prop,
                a_add_c_derivation,
                a_add_c_derived_add_b_derivation,
                hc,
            ),
            VdMirTermDerivationConstruction::ProductAddLiteral => {
                check_product_add_literal(prop, hc)
            }
            VdMirTermDerivationConstruction::DivAtom { a_mul_b_inv_dn } => {
                check_div_atom(prop, a_mul_b_inv_dn, hc)
            }
            VdMirTermDerivationConstruction::AtomMulExponentialLess => {
                check_atom_mul_exponential_less(prop, hc)
            }
            VdMirTermDerivationConstruction::AtomMulExponentialGreater => {
                check_atom_mul_exponential_greater(prop, hc)
            }
            VdMirTermDerivationConstruction::NonTrivialExprEquivalence { src_nf, dst_nf } => {
                check_expr_equivalence(prop, src_nf, dst_nf, hc)
            }
            VdMirTermDerivationConstruction::OneMulPowerOne => check_one_mul_power_one(prop, hc),
            VdMirTermDerivationConstruction::MulOne => check_mul_one(prop, hc),
            VdMirTermDerivationConstruction::SimpleProductMulLiteral {
                c_mul_a_mul_coercion,
                e_mul_a_mul_coercion: e_mul_a_coercion,
                a_ae_acd_coercion_triangle,
                a_ac_acd_coercion_triangle,
                e_ae_acd_coercion_triangle,
            } => check_simple_product_mul_literal(prop, hc),
        }
    }
}

fn check_reflection<'db, Src>(prop: VdMirExprIdx, hc: &mut VdMirHypothesisConstructor<'db, Src>) {
    let (lhs, signature, rhs) = hc.split_any_trivial_chaining_separated_list(prop);
    match signature.separator() {
        VdMirBaseChainingSeparator::Iff => (),
        VdMirBaseChainingSeparator::Relation(separator) => match separator {
            VdMirBaseRelationSeparator::Comparison(separator) => match separator {
                VdMirBaseComparisonSeparator::Eq => (),
                VdMirBaseComparisonSeparator::Ne => panic!(),
                VdMirBaseComparisonSeparator::Lt => panic!(),
                VdMirBaseComparisonSeparator::Gt => panic!(),
                VdMirBaseComparisonSeparator::Le => todo!("should we allow this?"),
                VdMirBaseComparisonSeparator::Ge => todo!("should we allow this?"),
            },
            VdMirBaseRelationSeparator::Containment(_) => panic!(),
        },
    }
    assert_deep_eq!(lhs, rhs, hc)
}

/// derive `a <nc> b => term <nc> 0` from `a - b <nc> 0 => term <nc> 0` and `a - b => term`
fn check_num_comparison<'db, Src>(
    prop: VdMirExprIdx,
    a_nf: VdMirTermDerivationIdx,
    b_nf: VdMirTermDerivationIdx,
    a_nf_minus_a_nf_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (leader => follower) = prop, hc);
    let (a, leader_signature, b) = hc.split_any_trivial_chaining_separated_list(leader);
    let (term, follower_signature, zero) = hc.split_any_trivial_chaining_separated_list(follower);
    assert_eq!(leader_signature.separator(), follower_signature.separator());
    let VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::Comparison(separator)) =
        leader_signature.separator()
    else {
        unreachable!()
    };
    assert!(hc.literal(zero).is_zero());
    ds!(let (a_nf_minus_b_nf => term1) = a_nf_minus_a_nf_nf.prop(hc), hc);
    assert_deep_eq!(term1, term, hc);
    ds!(let (a1 => a_nf) = a_nf.prop(hc), hc);
    ds!(let (b1 => b_nf) = b_nf.prop(hc), hc);
    ds!(let (a_nf1 - b_nf1) = a_nf_minus_b_nf, hc);
    assert_deep_eq!(a1, a, hc);
    assert_deep_eq!(b1, b, hc);
    assert_deep_eq!(a_nf1, a_nf, hc);
    assert_deep_eq!(b_nf1, b_nf, hc);
}

/// obtain `a + (b + c) = term` from `a + b + c = term`
fn check_add_interchange<'db, Src>(prop: VdMirExprIdx, hc: &VdMirHypothesisConstructor<'db, Src>) {
    todo!()
    // let expr_arena = hc.expr_arena();
}

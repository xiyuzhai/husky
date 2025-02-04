use super::*;
use convert_case::{Case, Casing};
use either::*;
use lean_entity_path::{
    theorem::{LnTermDerivationTheoremPath, LnTheoremPath},
    LnItemPath,
};
use lean_mir_expr::expr::{application::LnMirFunc, LnMirExprIdx, LnMirExprIdxRange};
use smallvec::*;
use visored_mir_expr::{
    coercion::{VdMirCoercion, VdMirSeparatorCoercion},
    derivation::construction::term::{VdMirTermDerivationConstruction, VdMirTermDerivationIdx},
    expr::{VdMirExprEntry, VdMirExprIdx},
    hypothesis::VdMirHypothesisIdx,
};

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(super) fn build_term_tactic_construction(
        &mut self,
        construction: &VdMirTermDerivationConstruction,
    ) -> LnMirExprIdx {
        let variant_name: &'static str = construction.into();
        let arguments: Option<LnMirExprIdxRange> = match *construction {
            VdMirTermDerivationConstruction::Reflection => None,
            VdMirTermDerivationConstruction::NumComparison {
                separator,
                a_nf,
                b_nf,
                a_nf_sub_b_nf_nf,
                a_eq_coercion,
                b_eq_coercion,
            } => Some(
                [
                    A(separator.unicode()),
                    D(*a_nf),
                    D(*b_nf),
                    D(*a_nf_sub_b_nf_nf),
                    C(a_eq_coercion.into()),
                    C(b_eq_coercion.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::SubEqsAddNeg {
                add_neg,
                b_neg_coercion,
            } => Some([D(*add_neg), C(b_neg_coercion.into())].to_lean(self)),
            VdMirTermDerivationConstruction::LiteralAddLiteral { lopd, ropd } => None,
            VdMirTermDerivationConstruction::AddEq {
                a_eq_coercion,
                b_eq_coercion,
                a_derivation,
                b_derivation,
                a_term_add_b_term_derivation,
            } => Some(
                [
                    D(*a_derivation),
                    D(*b_derivation),
                    C(a_eq_coercion.into()),
                    C(b_eq_coercion.into()),
                    D(*a_term_add_b_term_derivation),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::NegLiteral => None,
            VdMirTermDerivationConstruction::NegEq {
                opd_nf,
                neg_a_term_nf,
            } => Some([D(*opd_nf), D(*neg_a_term_nf)].to_lean(self)),
            VdMirTermDerivationConstruction::NegAtom => None,
            VdMirTermDerivationConstruction::NegSum {
                neg_a_nf,
                neg_b_nf,
                a_eq_coercion: ha_eq_coercion,
                b_eq_coercion: hb_eq_coercion,
                a_neg_coercion: ha_neg_coercion,
                b_neg_coercion: hb_neg_coercion,
                neg_a_term_add_neg_b_term_add_coercion,
            } => Some(
                [
                    D(*neg_a_nf),
                    D(*neg_b_nf),
                    C(ha_eq_coercion.into()),
                    C(hb_eq_coercion.into()),
                    C(ha_neg_coercion.into()),
                    C(hb_neg_coercion.into()),
                    C(neg_a_term_add_neg_b_term_add_coercion.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::NegProduct => None,
            VdMirTermDerivationConstruction::NegExponential => None,
            VdMirTermDerivationConstruction::AtomAddNonZeroLiteral => None,
            VdMirTermDerivationConstruction::LiteralMulLiteral => None,
            VdMirTermDerivationConstruction::MulEq {
                a,
                b,
                a_eq_coercion,
                b_eq_coercion,
                merge,
            } => Some(
                [
                    D(*a),
                    D(*b),
                    D(*merge),
                    C(a_eq_coercion.into()),
                    C(b_eq_coercion.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::BaseMulLiteral => None,
            VdMirTermDerivationConstruction::OneMul { .. } => None,
            VdMirTermDerivationConstruction::NonOneLiteralMulAtom => None,
            VdMirTermDerivationConstruction::NfAddZero => None,
            VdMirTermDerivationConstruction::NonTrivialHypothesisEquivalence {
                src,
                src_nf,
                dst_nf,
            } => Some([H(src), D(*src_nf), D(*dst_nf)].to_lean(self)),
            VdMirTermDerivationConstruction::AtomMulAtomLess {
                a_pow_one_pow_coercion,
                b_pow_one_pow_coercion,
            } => Some(
                [
                    C(a_pow_one_pow_coercion.into()),
                    C(b_pow_one_pow_coercion.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::AtomMulAtomEqual => None,
            VdMirTermDerivationConstruction::AtomMulAtomGreater {
                a_pow_one_pow_coercion,
                b_pow_one_pow_coercion,
            } => Some(
                [
                    C(a_pow_one_pow_coercion.into()),
                    C(b_pow_one_pow_coercion.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::Sqrt { radicand_nf } => {
                Some([D(*radicand_nf)].to_lean(self))
            }
            VdMirTermDerivationConstruction::MulProduct {
                rsignature,
                ab_nf,
                ab_term_mul_c_nf,
                ab_eq_coercion,
                ab_mul_coercion,
                bc_mul_coercion,
            } => Some(
                [
                    D(*ab_nf),
                    D(*ab_term_mul_c_nf),
                    C(ab_eq_coercion.into()),
                    C(ab_mul_coercion.into()),
                    C(bc_mul_coercion.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::NonReducedPower { base, exponent } => {
                Some([D(*base), D(*exponent)].to_lean(self))
            }
            VdMirTermDerivationConstruction::PowerOne { base } => None,
            VdMirTermDerivationConstruction::AtomAddProductLess {
                zero_add_one_mul_a_pow_one_add_coercion,
                one_mul_a_pow_one_add_coercion,
                one_a_ac_coercion_triangle,
                a_pow_one_pow_coercion,
            } => Some(
                [
                    C(zero_add_one_mul_a_pow_one_add_coercion.into()),
                    C(one_mul_a_pow_one_add_coercion.into()),
                    C(one_a_ac_coercion_triangle.into()),
                    C(a_pow_one_pow_coercion.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::AtomAddProductEqualKeep => None,
            VdMirTermDerivationConstruction::AtomAddProductEqualCancel => None,
            VdMirTermDerivationConstruction::AtomAddProductGreater => None,
            VdMirTermDerivationConstruction::ZeroAdd { .. } => None,
            VdMirTermDerivationConstruction::AddAtom { add_product_nf } => {
                Some([add_product_nf].to_lean(self))
            }
            VdMirTermDerivationConstruction::SumAddProductEqualKeep => None,
            VdMirTermDerivationConstruction::SumAddProductEqualCancel => None,
            VdMirTermDerivationConstruction::SumAddProductGreater {
                a_add_c_nf,
                term_ac_add_b_nf,
                ab_add_coercion,
                a_ab_abc_coercion_triangle,
                b_ab_abc_coercion_triangle,
                ac_eq_coercion,
                ac_add_coercion,
                a_ac_abc_coercion_triangle,
                c_ac_abc_coercion_triangle,
            } => Some(
                [
                    D(*a_add_c_nf),
                    D(*term_ac_add_b_nf),
                    C(ab_add_coercion.into()),
                    C(a_ab_abc_coercion_triangle.into()),
                    C(b_ab_abc_coercion_triangle.into()),
                    C(ac_eq_coercion.into()),
                    C(ac_add_coercion.into()),
                    C(a_ac_abc_coercion_triangle.into()),
                    C(c_ac_abc_coercion_triangle.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::ProductAddProductLess {
                zero_add_a_add_coercion,
            } => Some([C(zero_add_a_add_coercion.into())].to_lean(self)),
            VdMirTermDerivationConstruction::ProductAddProductEqualKeep => None,
            VdMirTermDerivationConstruction::ProductAddProductEqualCancel => None,
            VdMirTermDerivationConstruction::ProductAddProductGreater {
                zero_add_b_add_coercion,
            } => Some([C(zero_add_b_add_coercion.into())].to_lean(self)),
            VdMirTermDerivationConstruction::SimpleProductMulExponentialLess {
                c_mul_a_mul_coercion,
                a_mul_b_mul_coercion,
                c_ac_abc_coercion_triangle,
                a_ac_abc_coercion_triangle,
                b_ab_abc_coercion_triangle,
                a_ab_abc_coercion_triangle,
            } => Some(
                [
                    C(c_mul_a_mul_coercion.into()),
                    C(a_mul_b_mul_coercion.into()),
                    C(c_ac_abc_coercion_triangle.into()),
                    C(a_ac_abc_coercion_triangle.into()),
                    C(b_ab_abc_coercion_triangle.into()),
                    C(a_ab_abc_coercion_triangle.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::SimpleProductMulExponentialGreater => None,
            VdMirTermDerivationConstruction::SimpleProductMulBaseLess => None,
            VdMirTermDerivationConstruction::SimpleProductMulBaseGreater => None,
            VdMirTermDerivationConstruction::AddSum {
                a_add_b_derivation,
                a_add_b_derived_add_c_derivation,
                b_add_c_add_coercion,
                b_βγ_αβγ_coercion_triangle,
                c_βγ_αβγ_coercion_triangle,
                a_add_b_eq_coercion,
                a_add_b_add_coercion,
                a_αβ_αβγ_coercion_triangle,
                b_αβ_αβγ_coercion_triangle,
                ab_term_αβ_αβγ_coercion_triangle,
                ab_term_add_c_eq_coercion,
                ab_term_add_c_add_coercion,
                ab_term_αβˈγ_αβγ_coercion_triangle,
                c_αβˈγ_αβγ_coercion_triangle,
            } => Some(
                [
                    D(*a_add_b_derivation),
                    D(*a_add_b_derived_add_c_derivation),
                    C(b_add_c_add_coercion.into()),
                    C(b_βγ_αβγ_coercion_triangle.into()),
                    C(c_βγ_αβγ_coercion_triangle.into()),
                    C(a_add_b_eq_coercion.into()),
                    C(a_add_b_add_coercion.into()),
                    C(a_αβ_αβγ_coercion_triangle.into()),
                    C(b_αβ_αβγ_coercion_triangle.into()),
                    C(ab_term_αβ_αβγ_coercion_triangle.into()),
                    C(ab_term_add_c_eq_coercion.into()),
                    C(ab_term_add_c_add_coercion.into()),
                    C(ab_term_αβˈγ_αβγ_coercion_triangle.into()),
                    C(c_αβˈγ_αβγ_coercion_triangle.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::DivEq {
                a_dn,
                b_dn,
                a_eq_coercion: a_coercion,
                b_eq_coercion: b_coercion,
                a_nf_div_b_nf_dn,
            } => Some(
                [
                    D(*a_dn),
                    D(*b_dn),
                    C(a_coercion.into()),
                    C(b_coercion.into()),
                    D(*a_nf_div_b_nf_dn),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::DivLiteral { a_mul_b_inv_dn } => {
                Some([a_mul_b_inv_dn].to_lean(self))
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
            } => Some(
                [
                    D(*p_derivation),
                    D(*a_mul_b_derivation),
                    D(*a_mul_c_derivation),
                    D(*ab_term_plus_ac_term_derivation),
                    C(pow_coercion.into()),
                    C(bc_add_coercion.into()),
                    C(ab_eq_coercion.into()),
                    C(ab_mul_coercion.into()),
                    C(ac_eq_coercion.into()),
                    C(ac_mul_coercion.into()),
                    C(a_ab_abc_coercion_triangle.into()),
                    C(a_ac_abc_coercion_triangle.into()),
                    C(b_ab_abc_coercion_triangle.into()),
                    C(b_bc_abc_coercion_triangle.into()),
                    C(c_ac_abc_coercion_triangle.into()),
                    C(c_bc_abc_coercion_triangle.into()),
                    C(p_coercion.into()),
                ]
                .to_lean(self),
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
            } => Some(
                [
                    D(*a_add_c_derivation),
                    D(*a_add_c_derived_add_b_derivation),
                    C(a_add_b_add_coercion.into()),
                    C(a_ab_abc_coercion_triangle.into()),
                    C(b_ab_abc_coercion_triangle.into()),
                    C(ac_eq_coercion.into()),
                    C(ac_add_coercion.into()),
                    C(a_ac_abc_coercion_triangle.into()),
                    C(c_ac_abc_coercion_triangle.into()),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::ProductAddLiteral => None,
            VdMirTermDerivationConstruction::DivAtom { a_mul_b_inv_dn } => {
                Some([a_mul_b_inv_dn].to_lean(self))
            }
            VdMirTermDerivationConstruction::AtomMulExponentialLess => None,
            VdMirTermDerivationConstruction::AtomMulExponentialGreater {
                a_pow_one_pow_coercion,
            } => Some([C(a_pow_one_pow_coercion.into())].to_lean(self)),
            VdMirTermDerivationConstruction::NonTrivialExprEquivalence { src_nf, dst_nf } => {
                Some([D(*src_nf), D(*dst_nf)].to_lean(self))
            }
            VdMirTermDerivationConstruction::OneMulPowerOne => None,
            VdMirTermDerivationConstruction::MulOne => None,
            VdMirTermDerivationConstruction::SimpleProductMulLiteral {
                c_mul_a_mul_coercion,
                e_mul_a_mul_coercion: e_mul_a_coercion,
                a_ae_acd_coercion_triangle,
                a_ac_acd_coercion_triangle,
                e_ae_acd_coercion_triangle,
            } => Some(
                [
                    C(c_mul_a_mul_coercion.into()),
                    C(e_mul_a_coercion.into()),
                    C(a_ae_acd_coercion_triangle.into()),
                    C(a_ac_acd_coercion_triangle.into()),
                    C(e_ae_acd_coercion_triangle.into()),
                ]
                .to_lean(self),
            ),
        };
        let tactics = self.alloc_tactics([LnMirTacticData::Custom {
            name: term_derivation_tactic_name_from_variant_name(variant_name).into(),
            arguments,
            construction: None,
        }]);
        self.alloc_expr(LnMirExprEntry::new(LnMirExprData::By { tactics }))
    }

    pub(super) fn build_term_derivation_chunk_end_tactic_data(
        &mut self,
        construction: &VdMirTermDerivationConstruction,
    ) -> LnMirTacticData {
        match construction {
            VdMirTermDerivationConstruction::NonTrivialHypothesisEquivalence {
                src,
                src_nf,
                dst_nf,
            } => LnMirTacticData::Assumption,
            _ => todo!(),
        }
    }
}

fn term_derivation_tactic_name_from_variant_name(variant_name: &'static str) -> String {
    format!("term_derivation_{}", variant_name.to_case(Case::Snake))
}

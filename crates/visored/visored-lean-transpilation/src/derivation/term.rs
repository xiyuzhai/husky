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
        use Argument::{Coercion as C, Derivation as D, Expr as E, Hypothesis as H};

        #[derive(Copy, Clone)]
        enum Argument {
            Coercion(VdMirCoercion),
            Derivation(VdMirTermDerivationIdx),
            Expr(VdMirExprIdx),
            Hypothesis(VdMirHypothesisIdx),
        }

        impl<S> VdTranspileToLean<S, LnMirExprEntry> for Argument
        where
            S: IsVdLeanTranspilationScheme,
        {
            fn to_lean(self, builder: &mut VdLeanTranspilationBuilder<S>) -> LnMirExprEntry {
                match self {
                    C(coercion) => coercion.to_lean(builder),
                    D(derivation) => derivation.to_lean(builder),
                    E(expr) => expr.to_lean(builder),
                    H(hypothesis) => hypothesis.to_lean(builder),
                }
            }
        }

        let variant_name: &'static str = construction.into();
        let arguments: Option<LnMirExprIdxRange> = match *construction {
            VdMirTermDerivationConstruction::Reflection => None,
            VdMirTermDerivationConstruction::NumComparison {
                lhs_nf,
                rhs_nf,
                lhs_nf_minus_rhs_nf_nf,
            } => None,
            VdMirTermDerivationConstruction::SubEqsAddNeg {
                add_neg,
                b_neg_coercion,
            } => Some([D(add_neg), C(b_neg_coercion.into())].to_lean(self)),
            VdMirTermDerivationConstruction::LiteralAddLiteral { lopd, ropd } => None,
            VdMirTermDerivationConstruction::AddEq {
                a_eq_coercion,
                b_eq_coercion,
                a_derivation,
                b_derivation,
                a_term_add_b_term_derivation,
            } => Some(
                [
                    D(a_derivation),
                    D(b_derivation),
                    C(a_eq_coercion.into()),
                    C(b_eq_coercion.into()),
                    D(a_term_add_b_term_derivation),
                ]
                .to_lean(self),
            ),
            VdMirTermDerivationConstruction::AdditionInterchange => None,
            VdMirTermDerivationConstruction::AdditionAssociativity => None,
            VdMirTermDerivationConstruction::AdditionIdentity => None,
            VdMirTermDerivationConstruction::AdditionInverse => None,
            VdMirTermDerivationConstruction::AdditionDistributivity => None,
            VdMirTermDerivationConstruction::NegLiteral => None,
            VdMirTermDerivationConstruction::NegEq {
                opd_nf,
                minus_opd_nf_nf,
            } => None,
            VdMirTermDerivationConstruction::NegAtom => None,
            VdMirTermDerivationConstruction::NegSum { neg_a_nf, neg_b_nf } => None,
            VdMirTermDerivationConstruction::NegProduct => None,
            VdMirTermDerivationConstruction::NegExponential => None,
            VdMirTermDerivationConstruction::AtomAddNonZeroLiteral => None,
            VdMirTermDerivationConstruction::LiteralMulLiteral => None,
            VdMirTermDerivationConstruction::MulEq { lopd, ropd, merge } => None,
            VdMirTermDerivationConstruction::BaseMulLiteral => None,
            VdMirTermDerivationConstruction::OneMul { .. } => None,
            VdMirTermDerivationConstruction::NonOneLiteralMulAtom => None,
            VdMirTermDerivationConstruction::NfAddZero => None,
            VdMirTermDerivationConstruction::NonTrivialHypothesisEquivalence {
                src,
                src_nf,
                dst_nf,
            } => Some([H(src), D(src_nf), D(dst_nf)].to_lean(self)),
            VdMirTermDerivationConstruction::AtomMulAtom { comparison } => None,
            VdMirTermDerivationConstruction::Sqrt { radicand_nf } => None,
            VdMirTermDerivationConstruction::MulProduct {
                rsignature,
                merge_rlopd_nf,
                merge_rropd_nf,
            } => None,
            VdMirTermDerivationConstruction::NonReducedPower { base, exponent } => None,
            VdMirTermDerivationConstruction::PowerOne { base } => None,
            VdMirTermDerivationConstruction::AtomAddProduct { comparison } => None,
            VdMirTermDerivationConstruction::ZeroAdd { .. } => None,
            VdMirTermDerivationConstruction::AddAtom { add_product_nf } => {
                Some([add_product_nf].to_lean(self))
            }
            VdMirTermDerivationConstruction::SumAddProductEqualKeep => None,
            VdMirTermDerivationConstruction::SumAddProductEqualCancel => None,
            VdMirTermDerivationConstruction::SumAddProductGreater { .. } => None,
            VdMirTermDerivationConstruction::ProductAddProductLess => None,
            VdMirTermDerivationConstruction::ProductAddProductEqualKeep => None,
            VdMirTermDerivationConstruction::ProductAddProductEqualCancel => None,
            VdMirTermDerivationConstruction::ProductAddProductGreater => None,
            VdMirTermDerivationConstruction::SimpleProductMulExponentialLess => None,
            VdMirTermDerivationConstruction::SimpleProductMulExponentialGreater => None,
            VdMirTermDerivationConstruction::SimpleProductMulBaseLess => None,
            VdMirTermDerivationConstruction::SimpleProductMulBaseGreater => None,
            VdMirTermDerivationConstruction::AddSum {
                a_add_b_derivation,
                a_add_b_derived_add_c_derivation,
            } => None,
            VdMirTermDerivationConstruction::DivEq {
                numerator_dn,
                denominator_dn,
                numerator_dn_div_denominator_dn_dn,
            } => None,
            VdMirTermDerivationConstruction::DivLiteral { a_mul_b_inv_dn } => None,
            VdMirTermDerivationConstruction::LiteralMulSum {
                p_derivation,
                a_mul_b_derivation,
                a_mul_c_derivation,
                ab_term_plus_ac_term_derivation,
            } => None,
            VdMirTermDerivationConstruction::SumAddLiteral {
                a_add_c_derivation,
                a_add_c_derived_add_b_derivation,
            } => None,
            VdMirTermDerivationConstruction::ProductAddLiteral => None,
            VdMirTermDerivationConstruction::DivAtom { a_mul_b_inv_dn } => None,
            VdMirTermDerivationConstruction::AtomMulExponentialLess => None,
            VdMirTermDerivationConstruction::AtomMulExponentialGreater => None,
            VdMirTermDerivationConstruction::ExprEquivalence { src_nf, dst_nf } => None,
            VdMirTermDerivationConstruction::OneMulPowerOne => None,
            VdMirTermDerivationConstruction::MulOne => None,
            VdMirTermDerivationConstruction::SimpleProductMulLiteral => None,
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

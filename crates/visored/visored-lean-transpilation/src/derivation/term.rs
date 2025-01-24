use super::*;
use lean_entity_path::{
    theorem::{LnTermDerivationTheoremPath, LnTheoremPath},
    LnItemPath,
};
use lean_mir_expr::expr::{application::LnMirFunc, LnMirExprIdx, LnMirExprIdxRange};
use smallvec::*;
use visored_mir_expr::derivation::construction::term::{
    VdMirTermDerivationConstruction, VdMirTermDerivationIdx,
};

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(super) fn build_term_tactic_construction(
        &mut self,
        construction: &VdMirTermDerivationConstruction,
    ) -> LnMirExprIdx {
        let (item_path, arguments): (LnTermDerivationTheoremPath, LnMirExprIdxRange) =
            match construction {
                VdMirTermDerivationConstruction::Reflection => (
                    LnTermDerivationTheoremPath::Reflection,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::NumComparison {
                    lhs_nf,
                    rhs_nf,
                    lhs_nf_minus_rhs_nf_nf,
                } => (
                    LnTermDerivationTheoremPath::NumComparison,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::SubEqsAddNeg { add_neg } => (
                    LnTermDerivationTheoremPath::LiteralAddLiteral,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::LiteralAddLiteral { lopd, ropd } => (
                    LnTermDerivationTheoremPath::LiteralAddLiteral,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::AddEq { lopd, ropd, merge } => {
                    (LnTermDerivationTheoremPath::AddEq, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::AdditionInterchange => (
                    LnTermDerivationTheoremPath::AdditionInterchange,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::AdditionAssociativity => (
                    LnTermDerivationTheoremPath::AdditionAssociativity,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::AdditionIdentity => (
                    LnTermDerivationTheoremPath::AdditionIdentity,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::AdditionInverse => (
                    LnTermDerivationTheoremPath::AdditionInverse,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::AdditionDistributivity => (
                    LnTermDerivationTheoremPath::AdditionDistributivity,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::NegLiteral => (
                    LnTermDerivationTheoremPath::NegLiteral,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::NegEq {
                    opd_nf,
                    minus_opd_nf_nf,
                } => (LnTermDerivationTheoremPath::NegEq, self.alloc_exprs([])),
                VdMirTermDerivationConstruction::NegAtom => {
                    (LnTermDerivationTheoremPath::NegAtom, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::NegSum { neg_a_nf, neg_b_nf } => {
                    (LnTermDerivationTheoremPath::NegSum, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::NegProduct => (
                    LnTermDerivationTheoremPath::NegProduct,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::NegExponential => (
                    LnTermDerivationTheoremPath::NegExponential,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::AtomAddNonZeroLiteral => (
                    LnTermDerivationTheoremPath::AtomAddSwap,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::LiteralMulLiteral => (
                    LnTermDerivationTheoremPath::LiteralMul,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::MulEq { lopd, ropd, merge } => {
                    (LnTermDerivationTheoremPath::MulEq, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::BaseMulLiteral => (
                    LnTermDerivationTheoremPath::AtomMulSwap,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::OneMul { .. } => {
                    (LnTermDerivationTheoremPath::OneMul, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::NonOneLiteralMulAtom => (
                    LnTermDerivationTheoremPath::NonOneLiteralMulAtom,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::NfAddZero => {
                    (LnTermDerivationTheoremPath::NfAddZero, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::NonTrivialFinish { src_nf, dst_nf } => (
                    LnTermDerivationTheoremPath::NonTrivialFinish,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::AtomMulAtom { comparison } => {
                    let path = match comparison {
                        core::cmp::Ordering::Less => LnTermDerivationTheoremPath::AtomMulAtomLess,
                        core::cmp::Ordering::Equal => LnTermDerivationTheoremPath::AtomMulAtomEqual,
                        core::cmp::Ordering::Greater => {
                            LnTermDerivationTheoremPath::AtomMulAtomGreater
                        }
                    };
                    (path, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::Sqrt { radicand_nf } => {
                    (LnTermDerivationTheoremPath::Sqrt, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::MulProduct {
                    rsignature,
                    merge_rlopd_nf,
                    merge_rropd_nf,
                } => (
                    LnTermDerivationTheoremPath::MulProduct,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::NonReducedPower { base, exponent } => (
                    LnTermDerivationTheoremPath::NonReducedPower,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::PowerOne { base } => {
                    (LnTermDerivationTheoremPath::PowerOne, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::AtomAddProduct { comparison } => (
                    LnTermDerivationTheoremPath::AtomAddProduct,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::ZeroAdd { .. } => {
                    (LnTermDerivationTheoremPath::ZeroAdd, self.alloc_exprs([]))
                }
                VdMirTermDerivationConstruction::AddAtom { .. } => {
                    ((LnTermDerivationTheoremPath::AddAtom, self.alloc_exprs([])))
                }
                VdMirTermDerivationConstruction::SumAddProductEqualKeep => (
                    LnTermDerivationTheoremPath::SumAddProductEqualKeep,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::SumAddProductEqualCancel => (
                    LnTermDerivationTheoremPath::SumAddProductEqualCancel,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::SumAddProductGreater { .. } => (
                    LnTermDerivationTheoremPath::SumAddProductGreater,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::ProductAddProductLess => (
                    LnTermDerivationTheoremPath::ProductAddProductLess,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::ProductAddProductEqualKeep => (
                    LnTermDerivationTheoremPath::ProductAddProductEqualKeep,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::ProductAddProductEqualCancel => (
                    LnTermDerivationTheoremPath::ProductAddProductEqualCancel,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::ProductAddProductGreater => (
                    LnTermDerivationTheoremPath::ProductAddProductGreater,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::SimpleProductMulExponentialLess => (
                    LnTermDerivationTheoremPath::SimpleProductMulExponentialLess,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::SimpleProductMulExponentialGreater => (
                    LnTermDerivationTheoremPath::SimpleProductMulExponentialGreater,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::AddSum {
                    a_add_b_derivation,
                    a_add_b_derived_add_c_derivation,
                } => (LnTermDerivationTheoremPath::AddSum, self.alloc_exprs([])),
                VdMirTermDerivationConstruction::DivEq {
                    numerator_dn,
                    denominator_dn,
                    numerator_dn_div_denominator_dn_dn,
                } => (LnTermDerivationTheoremPath::DivEq, self.alloc_exprs([])),
                VdMirTermDerivationConstruction::DivLiteral { a_mul_b_inv_dn } => (
                    LnTermDerivationTheoremPath::DivLiteral,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::LiteralMulSum {
                    a_mul_b_derivation,
                    a_mul_c_derivation,
                } => (
                    LnTermDerivationTheoremPath::LiteralMulSum,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::SumAddLiteral {
                    a_add_c_derivation,
                    a_add_c_derived_add_b_derivation,
                } => (
                    LnTermDerivationTheoremPath::SumAddLiteral,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::ProductAddLiteral => (
                    LnTermDerivationTheoremPath::ProductAddLiteral,
                    self.alloc_exprs([]),
                ),
            };
        let func = self.alloc_expr(LnMirExprEntry::new(
            LnMirExprData::ItemPath(LnItemPath::Theorem(LnTheoremPath::TermDerivation(
                item_path,
            ))),
            None,
        ));
        self.alloc_expr(LnMirExprEntry::new(
            LnMirExprData::Application {
                function: LnMirFunc::Expr(func),
                arguments,
            },
            None,
        ))
    }

    pub(super) fn build_term_derivation_chunk_end_tactic_data(
        &mut self,
        construction: &VdMirTermDerivationConstruction,
    ) -> LnMirTacticData {
        match construction {
            VdMirTermDerivationConstruction::NonTrivialFinish { src_nf, dst_nf } => {
                LnMirTacticData::Assumption
            }
            _ => todo!(),
        }
    }
}

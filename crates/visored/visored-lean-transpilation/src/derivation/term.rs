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
                VdMirTermDerivationConstruction::AtomAddSwap => (
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
                VdMirTermDerivationConstruction::AtomMulSwap => (
                    LnTermDerivationTheoremPath::AtomMulSwap,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::OneMulNormalized => (
                    LnTermDerivationTheoremPath::OneMulNormalized,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::NonOneLiteralMulAtom => (
                    LnTermDerivationTheoremPath::NonOneLiteralMulAtom,
                    self.alloc_exprs([]),
                ),
                VdMirTermDerivationConstruction::NonZeroLiteralAddAtom => (
                    LnTermDerivationTheoremPath::NonZeroLiteralAddAtom,
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
                VdMirTermDerivationConstruction::MulAssoc { rsignature } => todo!(),
                VdMirTermDerivationConstruction::NonReducedPower { base, exponent } => todo!(),
                VdMirTermDerivationConstruction::PowerOne { base } => todo!(),
                VdMirTermDerivationConstruction::NonOneLiteralMulExponential => todo!(),
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

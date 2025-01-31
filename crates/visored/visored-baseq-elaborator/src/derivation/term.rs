pub mod chaining_separated_list;
pub mod division;
mod expr_derived;
mod neg;
pub mod power;
mod product;
pub mod sqrt;
mod subtraction;
mod sum;

use self::expr_derived::*;
use super::*;
use expr::{VdBsqExpr, VdBsqExprData};
use smallvec::*;
use visored_mir_expr::{
    derivation::{
        chunk::VdMirDerivationChunk,
        construction::{
            term::{VdMirTermDerivationConstruction, VdMirTermDerivationIdx},
            VdMirDerivationConstruction,
        },
        VdMirDerivationIdx, VdMirDerivationIdxRange,
    },
    expr::{application::VdMirFunc, VdMirExprData, VdMirExprEntry, VdMirExprIdx},
    hypothesis::{constructor::VdMirHypothesisConstructor, VdMirHypothesisIdx},
};
use visored_mir_opr::{
    opr::{binary::VdMirBaseBinaryOpr, prefix::VdMirBasePrefixOpr},
    separator::{folding::VdMirBaseFoldingSeparator, VdMirBaseSeparator},
};

impl<'db, 'sess> VdBsqElaboratorInner<'db, 'sess>
where
    'db: 'sess,
{
    pub fn transcribe_term_derivation(
        &mut self,
        src: VdBsqHypothesisIdx<'sess>,
        dst: VdBsqHypothesisIdx<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationChunk {
        hc.obtain_derivation_chunk_within_hypothesis(|hc| {
            self.transcribe_non_trivial_hypothesis_equivalence_term_derivation(src, dst, hc)
        })
    }

    pub fn transcribe_non_trivial_hypothesis_equivalence_term_derivation(
        &mut self,
        src: VdBsqHypothesisIdx<'sess>,
        dst: VdBsqHypothesisIdx<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationIdx {
        let src_nf = self.transcribe_expr_term_derivation(self.hc.arena()[src].prop(), hc);
        let dst_nf = self.transcribe_expr_term_derivation(self.hc.arena()[dst].prop(), hc);
        let prop = self.hc.arena()[dst].prop().transcribe(None, self, hc);
        hc.alloc_derivation(
            prop,
            VdMirTermDerivationConstruction::NonTrivialHypothesisEquivalence {
                src: hc.cached_hypothesis(src).unwrap(),
                src_nf: src_nf.derivation(),
                dst_nf: dst_nf.derivation(),
            }
            .into(),
        )
    }

    pub fn transcribe_non_trivial_expr_equivalence_term_derivation(
        &mut self,
        src: VdBsqExpr<'sess>,
        dst: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationIdx {
        let src_nf = self.transcribe_expr_term_derivation(src, hc);
        let dst_nf = self.transcribe_expr_term_derivation(dst, hc);
        let prop = dst.transcribe(None, self, hc);
        hc.alloc_term_derivation(
            prop,
            VdMirTermDerivationConstruction::ExprEquivalence {
                src_nf: src_nf.derivation(),
                dst_nf: dst_nf.derivation(),
            }
            .into(),
        )
    }

    fn transcribe_expr_term_derivation(
        &mut self,
        expr: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExprNormalized<'sess> {
        let construction = self.transcribe_expr_term_derivation_construction(expr, hc);
        VdBsqExprNormalized::new(expr, construction, self, hc)
    }

    fn transcribe_expr_term_derivation_construction(
        &mut self,
        expr: VdBsqExpr<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        match *expr.data() {
            VdBsqExprData::Literal(_) => VdMirTermDerivationConstruction::Reflection,
            VdBsqExprData::Variable(_, _) => VdMirTermDerivationConstruction::Reflection,
            VdBsqExprData::ItemPath(_) => VdMirTermDerivationConstruction::Reflection,
            VdBsqExprData::Application {
                function,
                ref arguments,
            } => match function {
                VdMirFunc::NormalBasePrefixOpr(signature) => {
                    let opd = arguments[0];
                    match signature.opr {
                        VdMirBasePrefixOpr::RingPos => todo!(),
                        VdMirBasePrefixOpr::RingNeg => {
                            self.transcribe_neg_term_derivation_construction(opd, hc)
                        }
                        _ => todo!(),
                    }
                }
                VdMirFunc::NormalBaseSeparator(signature) => todo!(),
                VdMirFunc::NormalBaseBinaryOpr(signature) => match signature.opr {
                    VdMirBaseBinaryOpr::CommRingSub => {
                        let &[lopd, ropd] = arguments.as_slice() else {
                            unreachable!()
                        };
                        self.transcribe_sub_term_derivation_construction(lopd, signature, ropd, hc)
                    }
                    VdMirBaseBinaryOpr::CommFieldDiv => {
                        let &[numerator, denominator] = arguments.as_slice() else {
                            unreachable!()
                        };
                        self.transcribe_div_term_derivation_construction(numerator, denominator, hc)
                    }
                },
                VdMirFunc::Power(signature) => {
                    let &[base, exponent] = arguments.as_slice() else {
                        unreachable!()
                    };
                    self.transcribe_pow_term_derivation_construction(base, exponent, hc)
                }
                VdMirFunc::NormalBaseSqrt(vd_base_sqrt_signature) => {
                    let radicand = arguments[0];
                    self.transcribe_sqrt_term_derivation_construction(radicand, hc)
                }
            },
            VdBsqExprData::FoldingSeparatedList {
                leader,
                ref followers,
            } => match followers[0].0.separator() {
                VdMirBaseFoldingSeparator::CommRingAdd => {
                    self.transcribe_sum_term_derivation_construction(leader, followers, hc)
                }
                VdMirBaseFoldingSeparator::CommRingMul => {
                    self.transcribe_product_term_derivation_construction(leader, followers, hc)
                }
                VdMirBaseFoldingSeparator::SetTimes => todo!(),
                VdMirBaseFoldingSeparator::TensorOtimes => todo!(),
            },
            VdBsqExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => self.transcribe_chaining_separated_list_term_derivation_construction(
                leader, followers, hc,
            ),
        }
    }
}

impl<'db, 'sess> VdBsqExpr<'sess> {
    fn normalize(
        self,
        elr: &mut VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExprNormalized<'sess> {
        elr.transcribe_expr_term_derivation(self, hc)
    }
}

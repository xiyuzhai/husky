pub mod chaining_separated_list;
pub mod division;
mod expr_nf;
mod neg;
pub mod power;
mod product;
pub mod square_root;
mod subtraction;
mod sum;

use self::expr_nf::*;
use super::*;
use expr::{VdBsqExprData, VdBsqExprFld};
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
            let src_term_equivalence =
                self.transcribe_expr_term_derivation(self.hc.arena()[src].expr(), hc);
            let dst_term_equivalence =
                self.transcribe_expr_term_derivation(self.hc.arena()[dst].expr(), hc);
            let prop = self.hc.arena()[dst].expr().transcribe(None, self, hc);
            hc.alloc_derivation(prop, todo!())
        })
    }

    fn transcribe_expr_term_derivation(
        &mut self,
        expr: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExprNf<'sess> {
        let prop = self.transcribe_expr_term_derivation_prop(expr, hc);
        let construction = self.transcribe_expr_term_derivation_construction(expr, hc);
        VdBsqExprNf::new(hc.alloc_term_derivation(prop, construction), expr)
    }

    fn transcribe_expr_term_derivation_prop(
        &mut self,
        expr: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprIdx {
        let term = expr.term();
        let (expr_transcription, expr_ty) = expr.transcribe_with_ty(None, self, hc);
        let (term_transcription, term_ty) = term.expr(self, hc).transcribe_with_ty(None, self, hc);
        let signature = hc.infer_equivalence_signature(expr_ty, term_ty);
        let prop_expr_data = VdMirExprData::ChainingSeparatedList {
            leader: expr_transcription,
            followers: smallvec![(signature, term_transcription)],
            joined_signature: None,
        };
        let prop_expr_ty = self.ty_menu().prop;
        hc.mk_expr(VdMirExprEntry::new(prop_expr_data, prop_expr_ty, None))
    }

    fn transcribe_expr_term_derivation_construction(
        &mut self,
        expr: VdBsqExprFld<'sess>,
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
                        self.transcribe_sub_term_derivation_construction(lopd, ropd, hc)
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

impl<'db, 'sess> VdBsqExprFld<'sess> {
    fn normalize(
        self,
        elr: &mut VdBsqElaboratorInner<'db, 'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdBsqExprNf<'sess> {
        elr.transcribe_expr_term_derivation(self, hc)
    }
}

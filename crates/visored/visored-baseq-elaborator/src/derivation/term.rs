pub mod chaining_separated_list;
pub mod division;
pub mod power;
mod product;
pub mod square_root;
mod subtraction;
mod sum;

use super::*;
use expr::{VdBsqExprFld, VdBsqExprFldData};
use smallvec::*;
use visored_mir_expr::{
    derivation::{
        chunk::VdMirDerivationChunk,
        construction::{term::VdMirTermDerivationConstruction, VdMirDerivationConstruction},
        VdMirDerivationIdx, VdMirDerivationIdxRange,
    },
    expr::{application::VdMirFunc, VdMirExprData, VdMirExprEntry, VdMirExprIdx},
    hypothesis::{constructor::VdMirHypothesisConstructor, VdMirHypothesisIdx},
};
use visored_mir_opr::{
    opr::binary::VdMirBaseBinaryOpr,
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
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationChunk {
        hypothesis_constructor.obtain_derivation_chunk_within_hypothesis(|hypothesis_constructor| {
            let src_term_equivalence = self.transcribe_expr_term_derivation(
                self.hypothesis_constructor.arena()[src].expr(),
                hypothesis_constructor,
            );
            let dst_term_equivalence = self.transcribe_expr_term_derivation(
                self.hypothesis_constructor.arena()[dst].expr(),
                hypothesis_constructor,
            );
            let prop = self.hypothesis_constructor.arena()[dst]
                .expr()
                .transcribe(self, hypothesis_constructor);
            hypothesis_constructor.alloc_derivation(prop, todo!())
        })
    }

    fn transcribe_expr_term_derivation(
        &mut self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationIdx {
        let prop = self.transcribe_expr_term_derivation_prop(expr, hypothesis_constructor);
        let construction =
            self.transcribe_expr_term_derivation_construction(expr, hypothesis_constructor);
        hypothesis_constructor.alloc_derivation(prop, construction.into())
    }

    fn transcribe_expr_term_derivation_prop(
        &mut self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirExprIdx {
        let term = expr.term();
        let (expr_transcription, expr_ty) = expr.transcribe_with_ty(self, hypothesis_constructor);
        let (term_transcription, term_ty) =
            term.transcribe_with_ty(self, Some(expr_ty), hypothesis_constructor);
        let signature = hypothesis_constructor.infer_equivalence_signature(expr_ty, term_ty);
        let prop_expr_data = VdMirExprData::ChainingSeparatedList {
            leader: expr_transcription,
            followers: smallvec![(signature, term_transcription)],
            joined_signature: None,
        };
        let prop_expr_ty = self.ty_menu().prop;
        hypothesis_constructor.mk_expr(VdMirExprEntry::new(prop_expr_data, prop_expr_ty, None))
    }

    fn transcribe_expr_term_derivation_construction(
        &mut self,
        expr: VdBsqExprFld<'sess>,
        hc: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        match *expr.data() {
            VdBsqExprFldData::Literal(_) => VdMirTermDerivationConstruction::Reflection,
            VdBsqExprFldData::Variable(_, _) => VdMirTermDerivationConstruction::Reflection,
            VdBsqExprFldData::ItemPath(_) => VdMirTermDerivationConstruction::Reflection,
            VdBsqExprFldData::Application {
                function,
                ref arguments,
            } => match function {
                VdMirFunc::NormalBasePrefixOpr(vd_base_prefix_opr_signature) => todo!(),
                VdMirFunc::NormalBaseSeparator(vd_base_separator_signature) => todo!(),
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
                VdMirFunc::Power(vd_power_signature) => {
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
            VdBsqExprFldData::FoldingSeparatedList {
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
            VdBsqExprFldData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => self.transcribe_chaining_separated_list_term_derivation_construction(
                leader, followers, hc,
            ),
        }
    }
}

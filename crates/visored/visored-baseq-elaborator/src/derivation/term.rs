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
        &self,
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
            hypothesis_constructor.alloc_derivation(
                prop,
                VdMirDerivationConstruction::Term(VdMirTermDerivationConstruction::Finalize {
                    src_term_equivalence,
                    dst_term_equivalence,
                }),
            )
        })
    }

    fn transcribe_expr_term_derivation(
        &self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirDerivationIdx {
        let prop = self.transcribe_expr_term_derivation_prop(expr, hypothesis_constructor);
        let construction =
            self.transcribe_expr_term_derivation_construction(expr, hypothesis_constructor);
        hypothesis_constructor.alloc_derivation(prop, construction.into())
    }

    fn transcribe_expr_term_derivation_prop(
        &self,
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
        &self,
        expr: VdBsqExprFld<'sess>,
        hypothesis_constructor: &mut VdMirHypothesisConstructor<'db, VdBsqHypothesisIdx<'sess>>,
    ) -> VdMirTermDerivationConstruction {
        match *expr.data() {
            VdBsqExprFldData::Literal(_) => VdMirTermDerivationConstruction::Literal,
            VdBsqExprFldData::Variable(_, _) => VdMirTermDerivationConstruction::Variable,
            VdBsqExprFldData::ItemPath(_) => VdMirTermDerivationConstruction::ItemPath,
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
                        let lopd =
                            self.transcribe_expr_term_derivation(lopd, hypothesis_constructor);
                        let ropd =
                            self.transcribe_expr_term_derivation(ropd, hypothesis_constructor);
                        VdMirTermDerivationConstruction::Sub { lopd, ropd }
                    }
                    VdMirBaseBinaryOpr::CommFieldDiv => {
                        let &[numerator, denominator] = arguments.as_slice() else {
                            unreachable!()
                        };
                        let numerator =
                            self.transcribe_expr_term_derivation(numerator, hypothesis_constructor);
                        let denominator = self
                            .transcribe_expr_term_derivation(denominator, hypothesis_constructor);
                        VdMirTermDerivationConstruction::Div {
                            numerator,
                            denominator,
                        }
                    }
                },
                VdMirFunc::Power(vd_power_signature) => VdMirTermDerivationConstruction::Power {
                    base: self
                        .transcribe_expr_term_derivation(arguments[0], hypothesis_constructor),
                    exponent: self
                        .transcribe_expr_term_derivation(arguments[1], hypothesis_constructor),
                },
                VdMirFunc::NormalBaseSqrt(vd_base_sqrt_signature) => {
                    let radicand =
                        self.transcribe_expr_term_derivation(arguments[0], hypothesis_constructor);
                    VdMirTermDerivationConstruction::Square { radicand }
                }
            },
            VdBsqExprFldData::FoldingSeparatedList {
                leader,
                ref followers,
            } => {
                let (fst_func, fst) = followers[0];
                let leader_equivalence =
                    self.transcribe_expr_term_derivation(leader, hypothesis_constructor);
                let follower_equivalences = followers
                    .iter()
                    .map(|&(func, follower)| {
                        (
                            func,
                            self.transcribe_expr_term_derivation(follower, hypothesis_constructor),
                        )
                    })
                    .collect::<Vec<_>>();
                match fst_func.separator() {
                    VdMirBaseFoldingSeparator::CommRingAdd => {
                        VdMirTermDerivationConstruction::Sum {
                            leader_equivalence,
                            follower_equivalences,
                        }
                    }
                    VdMirBaseFoldingSeparator::CommRingMul => {
                        VdMirTermDerivationConstruction::Product {
                            leader_equivalence,
                            follower_equivalences,
                        }
                    }
                    VdMirBaseFoldingSeparator::SetTimes => todo!(),
                    VdMirBaseFoldingSeparator::TensorOtimes => todo!(),
                }
            }
            VdBsqExprFldData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature,
            } => {
                let leader_equivalence =
                    self.transcribe_expr_term_derivation(leader, hypothesis_constructor);
                let follower_equivalences = followers
                    .iter()
                    .map(|&(func, follower)| {
                        (
                            func,
                            self.transcribe_expr_term_derivation(follower, hypothesis_constructor),
                        )
                    })
                    .collect::<Vec<_>>();
                VdMirTermDerivationConstruction::ChainingSeparatedList {
                    leader_equivalence,
                    follower_equivalences,
                }
            }
        }
    }
}

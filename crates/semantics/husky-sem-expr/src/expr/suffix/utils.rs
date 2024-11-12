use super::*;
use husky_sem_opr::suffix::SemaSuffixOpr;

impl<'a> SemExprBuilder<'a> {
    pub(super) fn calc_ambiguous_suffix_expr_ty<F1, F2, F3>(
        &mut self,
        opd: SynExprIdx,
        opr_regional_token_idx: RegionalTokenIdx,
        final_destination: FinalDestination,
        naive_suffix_f_given_opd_ty: F1,
        naive_suffix_f: F2,
        application_composition_f_given_opd_ty: F3,
    ) -> (SemExprDataResult<SemExprData>, SemExprTypeResult<FlyTerm>)
    where
        F1: FnOnce(
            &mut Self,
            FlyTerm,
        ) -> (SemExprDataResult<SemaSuffixOpr>, SemExprTypeResult<FlyTerm>),
        F2: FnOnce(
            &mut Self,
            SynExprIdx,
            RegionalTokenIdx,
        ) -> (SemExprDataResult<SemExprData>, SemExprTypeResult<FlyTerm>),
        F3: FnOnce(
            &mut Self,
            FlyTerm,
        ) -> (SemExprDataResult<SemaSuffixOpr>, SemExprTypeResult<FlyTerm>),
    {
        match final_destination {
            FinalDestination::Sort => {
                let (opd_sem_expr_idx, opd_ty) =
                    self.build_expr_with_ty(opd, ExpectFinalDestination::new(final_destination));
                match opd_ty {
                    Some(opd_ty) => match opd_ty.base_term_data(self) {
                        FlyTermData::Literal(_) => todo!(),
                        FlyTermData::TypeOntology { .. } => {
                            let (sem_opr_result, ty_result) =
                                naive_suffix_f_given_opd_ty(self, opd_ty);
                            (
                                sem_opr_result.map(|opr| SemExprData::Suffix {
                                    opd: opd_sem_expr_idx,
                                    opr,
                                    opr_regional_token_idx,
                                }),
                                ty_result,
                            )
                        }
                        FlyTermData::Curry { .. } => todo!(),
                        FlyTermData::Hole(_, _) => todo!(),
                        FlyTermData::Sort(_) => todo!(),
                        FlyTermData::Ritchie {
                            ritchie_kind,
                            parameter_contracted_tys,
                            return_ty,
                        } => todo!(),
                        FlyTermData::SymbolicVariable { .. } => todo!(),
                        FlyTermData::AbstractVariable { .. } => todo!(),
                        FlyTermData::TypeVariant { path } => todo!(),
                        FlyTermData::MajorTypeVar(_) => todo!(),
                        FlyTermData::Trait { .. } => todo!(),
                    },
                    None => (
                        todo!(),
                        Err(DerivedSemExprTypeError::UnableToInferSuffixOperandType.into()),
                    ),
                }
            }
            _ => naive_suffix_f(self, opd, opr_regional_token_idx),
        }
    }
}

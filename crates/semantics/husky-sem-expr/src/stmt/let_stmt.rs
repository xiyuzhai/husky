use super::*;
use husky_regional_token::{EqRegionalToken, LetRegionalToken};

impl<'a> SemExprBuilder<'a> {
    pub(super) fn build_let_stmt(
        &mut self,
        let_token: LetRegionalToken,
        let_pattern_syndicate: &'a SynExprResult<LetPatternSyndicate>,
        eq_token: &SynExprResult<EqRegionalToken>,
        initial_value: SynExprIdx,
    ) -> (SemExprDataResult<SemStmtData>, SemExprTypeResult<FlyTerm>) {
        let (let_pattern, annotated_pattern_ty) = match let_pattern_syndicate.as_ref() {
            Ok(let_pattern) => {
                let let_pattern_sem_obelisk = match self.build_let_pattern_obelisk(let_pattern) {
                    Ok(let_pattern_sem_obelisk) => let_pattern_sem_obelisk,
                    Err(_) => todo!(),
                };
                (
                    let_pattern_sem_obelisk,
                    match let_pattern_sem_obelisk.ty_sem_expr_idx() {
                        Some(ty_sem_expr_idx) => self.infer_expr_term(ty_sem_expr_idx),
                        None => None,
                    },
                )
            }
            Err(_) => {
                return (
                    Err(DerivedSemExprDataError::SynPatternError.into()),
                    Err(DerivedSemExprTypeError::SynPatternError.into()),
                )
            }
        };
        let contract = self.syn_expr_region_data().pattern_contract(
            let_pattern_syndicate
                .as_ref()
                .expect("must be okay")
                .syn_pattern_root()
                .syn_pattern_idx(),
        );
        let ((initial_value, pattern_ty), coercion_outcome) = match annotated_pattern_ty {
            Some(annotated_pattern_ty) => {
                let (initial_value, coercion_outcome) = self.build_expr_with_outcome(
                    initial_value,
                    ExpectCoercion::new(contract, annotated_pattern_ty),
                );
                let pattern_ty = match coercion_outcome {
                    Some(ref coercion_outcome) => Some(
                        annotated_pattern_ty
                            .with_quary(coercion_outcome.coercion().quary_after_coercion()),
                    ),
                    None => None,
                };
                ((initial_value, pattern_ty), coercion_outcome)
            }
            None => {
                (
                    self.build_expr_with_ty(
                        initial_value,
                        // ad hoc
                        ExpectAnyOriginal,
                    ),
                    None,
                )
            }
        };
        let ty_result = match pattern_ty {
            Some(ty) if ty == self.term_menu().never().into() => {
                Ok(self.term_menu().never().into())
            }
            Some(ty) => {
                match let_pattern_syndicate {
                    Ok(let_variables_pattern) => self.infer_variable_pattern_root_and_symbols_ty(
                        let_variables_pattern.syn_pattern_root(),
                        ty,
                        let_variables_pattern.variables(),
                    ),
                    Err(_) => todo!(),
                };
                Ok(self.term_menu().unit_ty_ontology().into())
            }
            None => Ok(self.term_menu().unit_ty_ontology().into()),
        };
        let eq_token = match eq_token {
            Ok(eq_token) => *eq_token,
            Err(_) => todo!(),
        };
        (
            Ok(SemStmtData::Let {
                let_token,
                let_pattern_sem_obelisk: let_pattern,
                contract,
                eq_token,
                initial_value,
                coercion_outcome,
            }),
            ty_result,
        )
    }
}

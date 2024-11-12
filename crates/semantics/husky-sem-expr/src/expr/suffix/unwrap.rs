use super::*;

impl<'a> SemExprBuilder<'a> {
    pub(super) fn calc_unwrap_expr_ty_given_opd_ty(
        &mut self,
        opd_ty: FlyTerm,
    ) -> (SemExprDataResult<SemaSuffixOpr>, SemExprTypeResult<FlyTerm>) {
        todo!()
    }

    pub(super) fn calc_unwrap_expr_ty(
        &mut self,
        opd: SynExprIdx,
        opr_regional_token_idx: RegionalTokenIdx,
    ) -> (SemExprDataResult<SemExprData>, SemExprTypeResult<FlyTerm>) {
        let (opd_sem_expr_idx, opd_ty) = self.build_expr_with_ty(opd, ExpectAnyOriginal);
        let Some(opd_ty) = opd_ty else {
            return (
                Err(todo!()),
                Err(DerivedSemExprTypeError::UnableToInferUnwrapOperand.into()),
            );
        };
        match opd_ty.base_term_data(self) {
            FlyTermData::Literal(_) => todo!(),
            FlyTermData::TypeOntology {
                ty_path,
                refined_ty_path,
                ty_arguments,
                ty_ethereal_term,
            } => match refined_ty_path {
                Left(PreludeTypePath::Option | PreludeTypePath::Result) => {
                    let ty = ty_arguments[0];
                    let expr_ty = match ty.quary() {
                        Some(_) => ty,
                        None => ty.with_quary(opd_ty.quary().unwrap()),
                    };
                    (
                        Ok(SemExprData::Unwrap {
                            opd: opd_sem_expr_idx,
                            opr_regional_token_idx,
                            // unwrap_method_path: todo!(),
                            // instantiation: todo!(),
                        }),
                        Ok(expr_ty),
                    )
                }
                _ => return (todo!(), Err(OriginalSemExprTypeError::CannotUnwrap.into())),
            },
            FlyTermData::Curry {
                toolchain,
                curry_kind,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => todo!(),
            FlyTermData::Hole(_, _) => todo!(),
            FlyTermData::Sort(_) => todo!(),
            FlyTermData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => todo!(),
            FlyTermData::SymbolicVariable {
                symbolic_variable: term,
                ty,
            } => todo!(),
            FlyTermData::AbstractVariable { .. } => todo!(),
            FlyTermData::TypeVariant { path } => todo!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
            FlyTermData::Trait { .. } => todo!(),
        }
    }
}

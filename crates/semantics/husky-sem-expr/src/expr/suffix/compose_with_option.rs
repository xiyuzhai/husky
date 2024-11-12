use super::*;
use husky_sem_opr::suffix::SemaSuffixOpr;

impl<'a> SemExprBuilder<'a> {
    pub(super) fn calc_compose_with_option_expr_ty(
        &mut self,
        opd: SynExprIdx,
        final_destination: FinalDestination,
    ) -> (SemExprDataResult<SemExprData>, SemExprTypeResult<FlyTerm>) {
        todo!()
    }

    pub(super) fn calc_compose_with_option_expr_ty_given_opd_ty(
        &mut self,
        opd_ty: FlyTerm,
    ) -> (SemExprDataResult<SemaSuffixOpr>, SemExprTypeResult<FlyTerm>) {
        match opd_ty.base_term_data(self) {
            FlyTermData::Literal(_) => todo!(),
            FlyTermData::TypeOntology {
                ty_path: path,
                refined_ty_path: refined_path,
                ty_arguments: arguments,
                ty_ethereal_term,
            } => todo!(),
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
                ..
            } => todo!(),
            FlyTermData::SymbolicVariable { .. } => todo!(),
            FlyTermData::AbstractVariable { .. } => todo!(),
            FlyTermData::TypeVariant { path } => todo!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
            FlyTermData::Trait { .. } => todo!(),
        }
    }
}

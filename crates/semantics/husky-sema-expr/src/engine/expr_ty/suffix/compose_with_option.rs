use super::*;

impl<'a> ExprTypeEngine<'a> {
    pub(super) fn calc_compose_with_option_expr_ty(
        &mut self,
        opd: SynExprIdx,
        final_destination: FinalDestination,
    ) -> SemaExprResult<(SynExprDisambiguation, SemaExprResult<FluffyTerm>)> {
        todo!()
    }

    pub(super) fn calc_compose_with_option_expr_ty_give_opd_ty(
        &mut self,
        opd_ty: FluffyTerm,
    ) -> SemaExprResult<(SynExprDisambiguation, SemaExprResult<FluffyTerm>)> {
        match opd_ty.data(self) {
            FluffyTermData::Literal(_) => todo!(),
            FluffyTermData::TypeOntology {
                ty_path: path,
                refined_ty_path: refined_path,
                ty_arguments: arguments,
                ty_ethereal_term,
            } => todo!(),
            FluffyTermData::Curry {
                curry_kind,
                variance,
                parameter_variable,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => todo!(),
            FluffyTermData::Hole(_, _) => todo!(),
            FluffyTermData::Category(_) => todo!(),
            FluffyTermData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
                ..
            } => todo!(),
            FluffyTermData::Symbol { .. } => todo!(),
            FluffyTermData::Variable { ty } => todo!(),
            FluffyTermData::TypeVariant { path } => todo!(),
        }
    }
}
use super::*;

impl HasFlyTypeMethodDispatch for HolTerm {
    fn ty_method_dispatch(
        self,
        engine: &mut impl FlyTermEngineMut,
        expr_idx: SynExprIdx,
        ident_token: IdentRegionalToken,
        indirections: FlyIndirections,
    ) -> FlyTermMaybeResult<MethodFlyInstanceDispatch> {
        match self.fly_base_ty_data(engine.db(), engine.fly_terms()) {
            FlyBaseTypeData::TypeOntology {
                ty_path,
                refined_ty_path,
                ty_arguments,
                ty_ethereal_term,
            } => {
                p!(self
                    .fly_base_ty_data(engine.db(), engine.fly_terms())
                    .debug(engine.db()));
                todo!()
            }
            FlyBaseTypeData::Curry {
                curry_kind,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => todo!(),
            FlyBaseTypeData::Hole(hole_kind, hole) => {
                let db = engine.db();
                let term_menu = engine.term_menu();
                engine
                    .fly_term_region_mut()
                    .terms
                    .fill_hole_by_force(hole, db, term_menu);
                // ad hoc, needs improvement
                Into::<FlyTerm>::into(self).ty_method_dispatch(
                    engine,
                    expr_idx,
                    ident_token,
                    indirections,
                )
            }
            FlyBaseTypeData::Sort(_) => todo!(),
            FlyBaseTypeData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => todo!(),
            FlyBaseTypeData::SymbolicVariable {
                symbolic_variable: term,
            } => todo!(),
            FlyBaseTypeData::AbstractVariable {
                abstract_variable: hvar,
            } => todo!(),
        }
    }
}

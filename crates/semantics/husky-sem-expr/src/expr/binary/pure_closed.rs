use super::*;

impl<'a> SemExprBuilder<'a> {
    pub(super) fn calc_binary_closed_expr_ty(
        &mut self,
        lopd: SynExprIdx,
        ropd: SynExprIdx,
        opr: BinaryClosedOpr,
        menu: &EthTermMenu,
    ) -> (
        SemExprIdx,
        SemBinaryOpr,
        SemExprIdx,
        SemExprDataResult<SemaBinaryOprInstanceDispatch>,
        SemExprTypeResult<FlyTerm>,
    ) {
        let lopd_syn_expr_idx = lopd;
        let (lopd, lopd_ty) = self.build_expr_with_ty(lopd, ExpectAnyOriginal);
        let Some(lopd_ty) = lopd_ty else {
            let ropd = self.build_expr(ropd, ExpectAnyDerived);
            return (
                lopd,
                SemBinaryOpr::Closed(opr),
                ropd,
                todo!(),
                Err(DerivedSemExprTypeError::BinaryOperationLeftOperandTypeNotInferred.into()),
            );
        };
        let ropd = self.build_expr(ropd, ExpectCoercion::new_pure(self, lopd_ty));
        let ty_result = match lopd_ty.base_term_data(self) {
            FlyTermData::Literal(_) => todo!(),
            FlyTermData::TypeOntology {
                ty_path,
                refined_ty_path: Left(PreludeTypePath::Num(_)),
                ..
            } => Ok(FlyTerm::from_eth_transient(
                ItemPathTerm::TypeOntology(ty_path).into(),
            )),
            FlyTermData::TypeOntology {
                ty_path: path,
                refined_ty_path: refined_path,
                ty_arguments: arguments,
                ..
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
            FlyTermData::Hole(hole_kind, _) => match hole_kind {
                HoleKind::UnspecifiedIntegerType | HoleKind::UnspecifiedFloatType => Ok(lopd_ty),
                HoleKind::ImplicitType => todo!(),
                HoleKind::AnyOriginal => todo!(),
                HoleKind::AnyDerived => todo!(),
            },
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
        };
        (
            lopd,
            SemBinaryOpr::Closed(opr),
            ropd,
            Ok(SemaBinaryOprInstanceDispatch::builtin()),
            ty_result,
        )
    }
}

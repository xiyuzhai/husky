use super::*;

impl<'a> SemExprBuilder<'a> {
    pub(super) fn calc_binary_shift_expr_ty(
        &mut self,
        lopd: SynExprIdx,
        ropd: SynExprIdx,
        opr: BinaryShiftOpr,
        menu: &EthTermMenu,
    ) -> (
        SemExprIdx,
        SemBinaryOpr,
        SemExprIdx,
        SemExprDataResult<SemaBinaryOprInstanceDispatch>,
        SemExprTypeResult<FlyTerm>,
    ) {
        // todo: don't use resolved
        let (lopd_sem_expr_idx, lopd_ty) = self.build_expr_with_ty(lopd, ExpectAnyOriginal);
        let Some(lopd_ty) = lopd_ty else {
            match self.syn_expr_region_data()[lopd] {
                SynExprData::CurrentVariable {
                    ident,
                    regional_token_idx,
                    current_variable_idx,
                    current_variable_kind,
                } => {
                    todo!()
                }
                _ => todo!(),
            }
            let ropd_sem_expr_idx = self.build_expr(ropd, ExpectAnyDerived);
            return (
                lopd_sem_expr_idx,
                SemBinaryOpr::Shift(opr),
                ropd_sem_expr_idx,
                todo!(),
                Err(DerivedSemExprTypeError::BinaryOperationLeftOperandTypeNotInferred.into()),
            );
        };
        match lopd_ty.base_term_data(self) {
            FlyTermData::TypeOntology {
                refined_ty_path: Left(PreludeTypePath::Num(_)),
                ..
            }
            | FlyTermData::Hole(HoleKind::UnspecifiedIntegerType, _) => {
                let ropd_sem_expr_idx = self.build_expr(ropd, ExpectIntType);
                (
                    lopd_sem_expr_idx,
                    SemBinaryOpr::Shift(opr),
                    ropd_sem_expr_idx,
                    Ok(SemaBinaryOprInstanceDispatch::builtin()),
                    Ok(lopd_ty),
                )
            }
            FlyTermData::Hole(HoleKind::UnspecifiedFloatType, _) => todo!(),
            // FlyTermData::TypeOntologyAtPlace {
            //     place,
            //     ty_path: path,
            //     refined_ty_path: Left(PreludeTypePath::Num(_)),
            //     ..
            // } => {
            //     self.calc_num_ty_binary_shift_ropd_ty(ropd)?;
            //     Ok(TermEntityPath::TypeOntology(path).into())
            // }
            FlyTermData::TypeOntology { .. }
            | FlyTermData::Hole(_, _)
            | FlyTermData::Literal(_)
            | FlyTermData::Curry { .. }
            | FlyTermData::Sort(_) => todo!(),
            FlyTermData::Ritchie { .. } => todo!(),
            FlyTermData::SymbolicVariable { .. } => todo!(),
            FlyTermData::AbstractVariable { .. } => todo!(),
            FlyTermData::TypeVariant { path } => todo!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
            FlyTermData::Trait { .. } => todo!(),
        }
    }

    // pub(super) fn calc_num_ty_binary_shift_ropd_ty(
    //     &mut self,
    //     ropd: SynExprIdx,
    // ) -> SemExprTypeResult<()> {
    //     match ropd_ty.data(self) {
    //         FlyTermData::Literal(_) => todo!(),
    //         FlyTermData::TypeOntology {
    //             refined_ty_path: Left(PreludeTypePath::Num(PreludeNumTypePath::Int(_))),
    //             ..
    //         }
    //         | FlyTermData::Hole(HoleKind::UnspecifiedIntegerType, _) => Ok(()),
    //         FlyTermData::TypeOntology { .. } => todo!(),
    //         FlyTermData::Curry { .. } => todo!(),
    //         FlyTermData::Hole(_, _) => todo!(),
    //         FlyTermData::Category(_) => todo!(),
    //         FlyTermData::Ritchie { .. } => todo!(),
    //         FlyTermData::Symbol { .. } => todo!(),
    //         FlyTermData::Variable { ty } => todo!(),
    //         FlyTermData::TypeVariant { path } => todo!(),
    //     }
    // }
}

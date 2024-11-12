use super::*;
use husky_entity_path::path::major_item::ty::PreludeIntTypePath;
use husky_sem_opr::prefix::SemaPrefixOpr;
use husky_syn_opr::SynPrefixOpr;

/// # type

impl<'a> SemExprBuilder<'a> {
    pub(super) fn build_prefix_expr(
        &mut self,
        expr_idx: SynExprIdx,
        opr: SynPrefixOpr,
        opd: SynExprIdx,
        final_destination: FinalDestination,
    ) -> (
        SemExprDataResult<(SemExprIdx, SemaPrefixOpr)>,
        SemExprTypeResult<FlyTerm>,
    ) {
        match opr {
            SynPrefixOpr::Minus => {
                let (opd_sem_expr_idx, opd_ty) = self.build_expr_with_ty(opd, ExpectAnyOriginal);
                let Some(opd_ty) = opd_ty else {
                    return (
                        Err(todo!()),
                        Err(DerivedSemExprTypeError::PrefixOperandTypeNotInferred.into()),
                    );
                };
                match opd_ty.base_term_data(self) {
                    FlyTermData::Literal(_) => todo!(),
                    FlyTermData::TypeOntology {
                        ty_path,
                        refined_ty_path,
                        ty_arguments: arguments,
                        ty_ethereal_term,
                    } => match refined_ty_path {
                        Left(PreludeTypePath::Num(num_ty_path)) => {
                            (Ok((opd_sem_expr_idx, SemaPrefixOpr::Minus)), Ok(opd_ty))
                        }
                        _ => todo!(),
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
                    FlyTermData::Hole(hole_kind, _) => match hole_kind {
                        HoleKind::UnspecifiedIntegerType | HoleKind::UnspecifiedFloatType => {
                            (Ok((opd_sem_expr_idx, SemaPrefixOpr::Minus)), Ok(opd_ty))
                        }
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
                }
            }
            SynPrefixOpr::Not => {
                let opd_sem_expr_idx = self.build_expr(opd, ExpectConditionType);
                // here we differs from Rust, but agrees with C
                (
                    Ok((opd_sem_expr_idx, SemaPrefixOpr::Not)),
                    Ok(self.term_menu().bool_ty_ontology().into()),
                )
            }
            SynPrefixOpr::Tilde => match final_destination {
                FinalDestination::Sort | FinalDestination::SortOrTrait => {
                    let (opd_sem_expr_idx, ty_result) = self.calc_function_application_expr_ty_aux(
                        expr_idx,
                        Variance::Covariant,
                        None,
                        self.term_menu().ty0().into(),
                        self.term_menu().ty0().into(),
                        opd,
                    );
                    (Ok((opd_sem_expr_idx, SemaPrefixOpr::LeashType)), ty_result)
                }
                FinalDestination::TypeOntology
                | FinalDestination::AnyOriginal
                | FinalDestination::AnyDerived => {
                    let (opd_sem_expr_idx, opd_ty) = self.build_expr_with_ty(opd, ExpectIntType);
                    (
                        Ok((opd_sem_expr_idx, SemaPrefixOpr::BitNot)),
                        self.calc_bitnot_expr_ty(opd_ty),
                    )
                }
                FinalDestination::Ritchie(_) => todo!(),
            },
            SynPrefixOpr::Ref => {
                let opd_sem_expr_idx = self.build_expr(opd, self.expect_ty0_subtype());
                // Should consider more cases, could also be taking references
                (
                    Ok((opd_sem_expr_idx, SemaPrefixOpr::RefType)),
                    Ok(self.term_menu().ty0().into()),
                )
            }
            SynPrefixOpr::Option => {
                // todo!("consider universe");
                let opd_sem_expr_idx = self.build_expr(opd, self.expect_ty0_subtype());
                (
                    Ok((opd_sem_expr_idx, SemaPrefixOpr::OptionType)),
                    Ok(self.term_menu().ty0().into()),
                )
            }
        }
    }

    fn calc_bitnot_expr_ty(&mut self, opd_ty: Option<FlyTerm>) -> SemExprTypeResult<FlyTerm> {
        let opd_ty = opd_ty.ok_or(DerivedSemExprTypeError::BitNotOperandTypeNotInferred)?;
        match opd_ty.base_term_data(self) {
            FlyTermData::TypeOntology {
                refined_ty_path: Left(prelude_ty_path),
                ..
            } => match prelude_ty_path {
                PreludeTypePath::Num(PreludeNumTypePath::Int(
                    PreludeIntTypePath::R8
                    | PreludeIntTypePath::R16
                    | PreludeIntTypePath::R32
                    | PreludeIntTypePath::R64
                    | PreludeIntTypePath::R128
                    | PreludeIntTypePath::RSize,
                )) => Ok(opd_ty),
                _ => Err(OriginalSemExprTypeError::BitOperationOnlyWorksForRawBitsOrCustom)?,
            },
            _ => todo!(),
        }
    }
}

/// # term

impl<'a> SemExprBuilder<'a> {
    pub(super) fn calc_prefix_expr_term(
        &mut self,
        expr_idx: SemExprIdx,
        opr: SemaPrefixOpr,
        opd: SemExprIdx,
    ) -> SemExprTermResult<FlyTerm> {
        let Some(opd_term) = self.infer_expr_term(opd) else {
            return Err(DerivedSemExprTermError::PrefixOprTermNotInferred.into());
        };
        match opr {
            SemaPrefixOpr::Minus => todo!(),
            SemaPrefixOpr::Not => todo!(),
            SemaPrefixOpr::BitNot => todo!(),
            SemaPrefixOpr::LeashType => Ok(opd_term.leashed(self)?),
            SemaPrefixOpr::RefType => {
                // let opd_ty = self.infer
                // match
                todo!()
            }
            SemaPrefixOpr::OptionType => {
                Ok(
                    FlyTerm::new_application(self, self.term_menu().option_ty_ontology(), opd_term)
                        .map_err(|e| DerivedSemExprTermError::OptionApplicationTerm(e))?
                        .into(),
                )
            }
        }
    }
}

use super::*;

impl<'a> ExprTypeEngine<'a> {
    pub(super) fn calc_prefix_expr_ty(
        &mut self,
        expr_idx: SynExprIdx,
        opr: PrefixOpr,
        opd: SynExprIdx,
        final_destination: FinalDestination,
    ) -> SemaExprResult<(SynExprDisambiguation, SemaExprResult<FluffyTerm>)> {
        match opr {
            PrefixOpr::Minus => {
                let opd_ty = self
                    .infer_new_expr_ty(opd, ExpectAnyOriginal)
                    .ok_or(DerivedSemaExprError::PrefixOperandTypeNotInferred)?;
                match opd_ty.data(self) {
                    FluffyTermData::Literal(_) => todo!(),
                    FluffyTermData::TypeOntology {
                        ty_path,
                        refined_ty_path,
                        ty_arguments: arguments,
                        ty_ethereal_term,
                    } => match refined_ty_path {
                        Left(PreludeTypePath::Num(num_ty_path)) => {
                            Ok((SynExprDisambiguation::Trivial, Ok(opd_ty)))
                        }
                        _ => todo!(),
                    },
                    FluffyTermData::Curry {
                        curry_kind,
                        variance,
                        parameter_variable,
                        parameter_ty,
                        return_ty,
                        ty_ethereal_term,
                    } => todo!(),
                    FluffyTermData::Hole(hole_kind, _) => match hole_kind {
                        HoleKind::UnspecifiedIntegerType | HoleKind::UnspecifiedFloatType => {
                            Ok((SynExprDisambiguation::Trivial, Ok(opd_ty)))
                        }
                        HoleKind::ImplicitType => todo!(),
                        HoleKind::Any => todo!(),
                    },
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
            PrefixOpr::Not => {
                self.infer_new_expr_ty_discarded(opd, ExpectConditionType);
                // here we differs from Rust, but agrees with C
                Ok((
                    SynExprDisambiguation::Trivial,
                    Ok(self.term_menu.bool_ty_ontology().into()),
                ))
            }
            PrefixOpr::Tilde => match final_destination {
                FinalDestination::Sort => Ok((
                    SynExprDisambiguation::Tilde(TildeDisambiguation::Leash),
                    self.calc_function_application_expr_ty_aux(
                        expr_idx,
                        Variance::Covariant,
                        None,
                        self.term_menu.ty0().into(),
                        self.term_menu.ty0().into(),
                        opd,
                    ),
                )),
                FinalDestination::TypeOntology
                | FinalDestination::AnyOriginal
                | FinalDestination::AnyDerived => Ok((
                    SynExprDisambiguation::Tilde(TildeDisambiguation::BitNot),
                    self.calc_bitnot_expr_ty(opd),
                )),
                FinalDestination::Ritchie(_) => todo!(),
            },
            PrefixOpr::Ref => {
                self.infer_new_expr_ty_discarded(opd, self.expect_ty0_subtype());
                // Should consider more cases, could also be taking references
                Ok((
                    SynExprDisambiguation::Trivial,
                    Ok(self.term_menu.ty0().into()),
                ))
            }
            PrefixOpr::Vector => todo!(),
            PrefixOpr::Slice => todo!(),
            PrefixOpr::CyclicSlice => todo!(),
            PrefixOpr::Array(_) => todo!(),
            PrefixOpr::Option => {
                // todo!("consider universe");
                self.infer_new_expr_ty_discarded(opd, self.expect_ty0_subtype());
                Ok((
                    SynExprDisambiguation::Trivial,
                    Ok(self.term_menu.ty0().into()),
                ))
            }
        }
    }

    fn calc_bitnot_expr_ty(&mut self, opd: SynExprIdx) -> SemaExprResult<FluffyTerm> {
        let Some(ty) = self.infer_new_expr_ty(opd, ExpectIntType) else {
            Err(DerivedSemaExprError::BitNotOperandTypeNotInferred)?
        };
        match ty.data(self) {
            FluffyTermData::Literal(_) => todo!(),
            FluffyTermData::TypeOntology {
                ty_path,
                refined_ty_path,
                ty_arguments,
                ..
            } => match refined_ty_path {
                Left(prelude_ty_path) => match prelude_ty_path {
                    PreludeTypePath::Basic(_) => todo!(),
                    PreludeTypePath::Num(num_ty_path) => match num_ty_path {
                        PreludeNumTypePath::Int(int_ty_path) => match int_ty_path {
                            PreludeIntTypePath::I8 => todo!(),
                            PreludeIntTypePath::I16 => todo!(),
                            PreludeIntTypePath::I32 => todo!(),
                            PreludeIntTypePath::I64 => todo!(),
                            PreludeIntTypePath::I128 => todo!(),
                            PreludeIntTypePath::ISize => todo!(),
                            PreludeIntTypePath::U8 => todo!(),
                            PreludeIntTypePath::U16 => todo!(),
                            PreludeIntTypePath::U32 => todo!(),
                            PreludeIntTypePath::U64 => todo!(),
                            PreludeIntTypePath::U128 => todo!(),
                            PreludeIntTypePath::USize => todo!(),
                            raw_bit_ty_path @ (PreludeIntTypePath::R8
                            | PreludeIntTypePath::R16
                            | PreludeIntTypePath::R32
                            | PreludeIntTypePath::R64
                            | PreludeIntTypePath::R128
                            | PreludeIntTypePath::RSize) => Ok(ty),
                        },
                        PreludeNumTypePath::Float(_) => todo!(),
                    },
                    PreludeTypePath::Indirection(_) => todo!(),
                    PreludeTypePath::Nat => todo!(),
                    PreludeTypePath::Lifetime => todo!(),
                    PreludeTypePath::Module => todo!(),
                    PreludeTypePath::Trait => todo!(),
                    PreludeTypePath::List => todo!(),
                    PreludeTypePath::Arr(_) => todo!(),
                    PreludeTypePath::StringLiteral => todo!(),
                    PreludeTypePath::Str => todo!(),
                    PreludeTypePath::Option => todo!(),
                    PreludeTypePath::Result => todo!(),
                },
                Right(_) => todo!(),
            },
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
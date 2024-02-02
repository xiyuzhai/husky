use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
#[salsa::debug_with_db]
pub struct ExpectEqsFunctionType {
    final_destination: FinalDestination,
}

impl ExpectEqsFunctionType {
    pub fn new(final_destination: FinalDestination) -> Self {
        Self { final_destination }
    }
}

impl ExpectFlyTerm for ExpectEqsFunctionType {
    type Outcome = ExpectEqsFunctionTypeOutcome;

    #[inline(always)]
    fn retrieve_outcome(outcome: &ExpectationOutcome) -> &Self::Outcome {
        match outcome {
            ExpectationOutcome::EqsFunctionCallType(outcome) => outcome,
            _ => unreachable!(),
        }
    }

    #[inline(always)]
    fn final_destination_inner(&self, db: &::salsa::Db, terms: &FlyTerms) -> FinalDestination {
        self.final_destination
    }

    #[inline(always)]
    fn destination(&self) -> Option<FlyTerm> {
        None
    }

    fn resolve(
        &self,
        db: &::salsa::Db,
        terms: &mut FlyTerms,
        state: &mut ExpectationState,
    ) -> AltOption<FlyTermEffect> {
        match state.expectee().base_ty_data_inner(db, terms) {
            FlyBaseTypeData::Curry {
                curry_kind: CurryKind::Explicit,
                variance,
                parameter_rune,
                parameter_ty,
                return_ty,
                ..
            } => state.set_ok(
                ExpectEqsFunctionTypeOutcome {
                    return_ty,
                    variant: ExpectEqsFunctionTypeOutcomeData::ExplicitCurry {
                        variance,
                        parameter_rune,
                        parameter_ty,
                        return_ty,
                    },
                },
                smallvec![],
            ),
            FlyBaseTypeData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
                ..
            } => state.set_ok(
                ExpectEqsFunctionTypeOutcome {
                    return_ty,
                    variant: ExpectEqsFunctionTypeOutcomeData::TypeRitchie {
                        ritchie_kind,
                        parameter_contracted_tys: parameter_contracted_tys.to_vec(),
                    },
                },
                smallvec![],
            ),
            _ => state.set_err(
                OriginalFlyTermExpectationError::ExpectedFunctionType,
                smallvec![],
            ),
        }
    }
}

#[salsa::debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ExpectEqsFunctionTypeOutcome {
    pub(crate) return_ty: FlyTerm,
    pub(crate) variant: ExpectEqsFunctionTypeOutcomeData,
}

impl ExpectEqsFunctionTypeOutcome {
    pub fn variant(&self) -> &ExpectEqsFunctionTypeOutcomeData {
        &self.variant
    }

    pub fn return_ty(&self) -> FlyTerm {
        self.return_ty
    }
}

#[salsa::debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ExpectEqsFunctionTypeOutcomeData {
    TypeRitchie {
        ritchie_kind: RitchieKind,
        parameter_contracted_tys: Vec<FlyRitchieParameter>,
    },
    ExplicitCurry {
        variance: Variance,
        parameter_rune: Option<RuneFlyTerm>,
        parameter_ty: FlyTerm,
        return_ty: FlyTerm,
    },
}
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectAnyDerived;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectAnyDerivedOutcome;

impl ExpectFlyTerm for ExpectAnyDerived {
    type Outcome = ExpectAnyDerivedOutcome;

    fn initial_resolve_progress() -> ExpectationProgress {
        ExpectationProgress::Resolved(Ok(ExpectAnyDerivedOutcome.into()))
    }

    #[inline(always)]
    fn retrieve_outcome(_outcome: &ExpectationOutcome) -> &Self::Outcome {
        &ExpectAnyDerivedOutcome
    }

    #[inline(always)]
    fn final_destination_inner(&self, db: &::salsa::Db, terms: &FlyTerms) -> FinalDestination {
        FinalDestination::AnyDerived
    }

    #[inline(always)]
    fn destination(&self) -> FlyTermDestination {
        FlyTermDestination::AnyDerived
    }

    fn resolve(
        &self,
        db: &::salsa::Db,
        fly_terms: &mut FlyTerms,
        state: &mut ExpectationState,
    ) -> AltOption<FlyTermEffect> {
        AltNone
    }
}

use path::major_item::ty::PreludeTypePath;

use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectSortOrTrait;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExpectSortOrTraitOutcome {
    Sort,
    Trait,
}

impl ExpectFlyTerm for ExpectSortOrTrait {
    type Outcome = ExpectSortOrTraitOutcome;

    fn retrieve_outcome(outcome: &ExpectationOutcome) -> &Self::Outcome {
        match outcome {
            ExpectationOutcome::SortOrTrait(outcome) => outcome,
            _ => unreachable!(),
        }
    }

    fn final_destination_inner(&self, db: &salsa::Db, terms: &FlyTerms) -> FinalDestination {
        FinalDestination::SortOrTrait
    }

    fn destination(&self) -> FlyTermDestination {
        todo!()
    }

    fn resolve(
        &self,
        db: &salsa::Db,
        terms: &mut FlyTerms,
        state: &mut ExpectationState,
    ) -> AltOption<FlyTermEffect> {
        match state.expectee().base_resolved_inner(terms) {
            FlyTermBase::Eth(EthTerm::Sort(sort)) => {
                state.set_ok(ExpectSortOrTraitOutcome::Sort, smallvec![])
            }
            FlyTermBase::Eth(EthTerm::ItemPath(ItemPathTerm::TypeOntology(path)))
                if path.refine(db) == Left(PreludeTypePath::TRAIT) =>
            {
                state.set_ok(ExpectSortOrTraitOutcome::Trait, smallvec![])
            }
            _ => todo!("check if equal to Trait type"),
            _ => state.set_err(
                OriginalFlyTermExpectationError::ExpectedCategory {
                    expectee: state.expectee(),
                },
                smallvec![],
            ),
        }
    }
}

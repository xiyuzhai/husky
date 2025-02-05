pub mod litnum_bound;
pub mod litnum_equality;

use self::{litnum_bound::*, litnum_equality::*};
use super::{
    stack::{VdBsqActiveHypotheses, VdBsqHypothesisStackRecord},
    VdBsqHypothesisEntry,
};
use crate::elaborator::VdBsqElaboratorInner;
use crate::hypothesis::stack::VdBsqHypothesisStack;
use floated_sequential::db::FloaterDb;
use std::marker::PhantomData;
use visored_baseq_elaborator_macros::stashes;

#[stashes]
pub struct VdBsqHypothesisStashes<'sess> {
    litnum_equality: VdBsqLitnumEqualityHypothesisStash<'sess>,
    litnum_bound: VdBsqLitnumBoundHypothesisStash<'sess>,
}

impl<'sess> VdBsqHypothesisStashes<'sess> {
    pub(super) fn new() -> Self {
        Self {
            litnum_equality: VdBsqLitnumEqualityHypothesisStash::new(),
            litnum_bound: VdBsqLitnumBoundHypothesisStash::new(),
        }
    }
}

impl<'sess> VdBsqHypothesisStashes<'sess> {
    pub fn litnum_equality(&self) -> &VdBsqLitnumEqualityHypothesisStash<'sess> {
        &self.litnum_equality
    }

    pub fn litnum_bound(&self) -> &VdBsqLitnumBoundHypothesisStash<'sess> {
        &self.litnum_bound
    }
}

impl<'sess> VdBsqHypothesisStashes<'sess> {
    pub(super) fn add_hypothesis(
        &mut self,
        hypothesis_stack_record: VdBsqHypothesisStackRecord<'sess>,
        hypothesis_entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
    ) {
        self._add_hypothesis(
            hypothesis_stack_record,
            hypothesis_entry,
            db,
            active_hypotheses,
        );
    }
}

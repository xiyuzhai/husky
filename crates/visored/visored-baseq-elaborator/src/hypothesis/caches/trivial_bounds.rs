//! this stores the naives bounds for terms
use super::*;
use crate::{hypothesis::VdBsqHypothesisIdx, term::comnum::VdBsqComnumTerm, Elr};
use rustc_hash::FxHashMap;

#[derive(Debug, PartialEq, Eq)]
pub struct VdBsqTrivialBounds<'sess>(Vec<VdBsqHypothesisIdx<'sess>>);

#[derive(Debug, Default)]
pub struct VdBsqTrivialBoundsHypothesisCache<'sess> {
    data: FxHashMap<VdBsqComnumTerm<'sess>, VdBsqTrivialBounds<'sess>>,
}

impl<'sess> VdBsqTrivialBoundsHypothesisCache<'sess> {
    fn contains(&self, term: VdBsqComnumTerm<'sess>) -> bool {
        self.data.contains_key(&term)
    }
}

impl<'db, 'sess> VdBsqTrivialBoundsHypothesisCache<'sess> {
    pub fn cache_trivial_bounds(
        term: VdBsqComnumTerm<'sess>,
        f: impl FnOnce(&mut Elr<'db, 'sess>) -> Vec<VdBsqHypothesisIdx<'sess>>,
        elr: &mut Elr<'db, 'sess>,
    ) {
        if !elr
            .hc
            .stack_mut()
            .caches_mut()
            .trivial_bounds
            .contains(term)
        {
            let bounds = f(elr);
            elr.hc
                .stack_mut()
                .caches_mut()
                .trivial_bounds
                .data
                .insert(term, VdBsqTrivialBounds(bounds));
        }
    }
}

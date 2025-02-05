//! this stores the naives bounds for terms
use super::*;
use crate::{hypothesis::VdBsqHypothesisIdx, term::comnum::VdBsqComnumTerm};
use rustc_hash::FxHashMap;

#[derive(Debug, PartialEq, Eq)]
pub struct VdBsqTrivialBounds<'sess>(Vec<VdBsqHypothesisIdx<'sess>>);

#[derive(Debug, Default)]
pub struct VdBsqTrivialBoundsHypothesisCache<'sess> {
    data: FxHashMap<VdBsqComnumTerm<'sess>, VdBsqTrivialBounds<'sess>>,
}

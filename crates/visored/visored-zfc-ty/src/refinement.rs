use crate::{term::VdZfcTermId, ty::VdZfcTypeData};

/// It's a term of type A -> B, where $A$ is the base type.
pub struct ZfcTypeRefinement {}

impl ZfcTypeRefinement {
    pub fn new(term: VdZfcTermId, data: &VdZfcTypeData, prev_refinements: &[Self]) -> Self {
        todo!()
    }
}

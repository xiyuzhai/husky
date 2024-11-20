use crate::{term::VdTermId, ty::VdTypeData};

/// It's a term of type A -> B, where $A$ is the base type.
pub struct ZfcTypeRefinement {}

impl ZfcTypeRefinement {
    pub fn new(term: VdTermId, data: &VdTypeData, prev_refinements: &[Self]) -> Self {
        todo!()
    }
}

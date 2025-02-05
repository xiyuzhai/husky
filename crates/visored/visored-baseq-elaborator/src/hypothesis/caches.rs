mod trivial_bounds;

use self::trivial_bounds::VdBsqTrivialBoundsHypothesisCache;

#[derive(Debug, Default)]
pub struct VdBsqHypothesisCaches<'sess> {
    trivial_bounds: VdBsqTrivialBoundsHypothesisCache<'sess>,
}

impl<'sess> VdBsqHypothesisCaches<'sess> {
    pub fn trivial_bounds_mut(&mut self) -> &mut VdBsqTrivialBoundsHypothesisCache<'sess> {
        &mut self.trivial_bounds
    }
}

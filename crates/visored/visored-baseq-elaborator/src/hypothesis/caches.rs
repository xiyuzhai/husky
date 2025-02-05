mod trivial_bounds;

use self::trivial_bounds::VdBsqTrivialBoundsCache;

#[derive(Debug, Default)]
pub struct VdBsqHypothesisCaches<'sess> {
    trivial_bounds: VdBsqTrivialBoundsCache<'sess>,
}

impl<'sess> VdBsqHypothesisCaches<'sess> {
    pub fn trivial_bounds_mut(&mut self) -> &mut VdBsqTrivialBoundsCache<'sess> {
        &mut self.trivial_bounds
    }
}

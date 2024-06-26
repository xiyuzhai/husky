use crate::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct RegionalTokenIdx(NonZeroU32);

impl RegionalTokenIdx {
    pub const START: Self = RegionalTokenIdx(unsafe { NonZeroU32::new_unchecked(1) });

    pub fn index(self) -> usize {
        self.0.get() as usize - 1
    }

    pub fn token_idx(self, base: RegionalTokenIdxBase) -> TokenIdx {
        unsafe { TokenIdx::from_usize_index_ext(self.index() + base.index_base()) }
    }

    pub(crate) fn from_index(index: usize) -> Self {
        debug_assert!(index < (u32::MAX - 1) as usize);
        unsafe { Self(NonZeroU32::new_unchecked((index + 1) as u32)) }
    }

    pub fn from_token_idx(
        token_idx: TokenIdx,
        regional_token_idx_base: RegionalTokenIdxBase,
    ) -> RegionalTokenIdx {
        Self::from_index(token_idx.index() - regional_token_idx_base.index_base())
    }
}

impl std::ops::Add<usize> for RegionalTokenIdx {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        Self::from_index(self.index() + rhs)
    }
}

impl std::ops::Sub<usize> for RegionalTokenIdx {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        Self::from_index(self.index() - rhs)
    }
}

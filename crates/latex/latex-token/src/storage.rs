use crate::{
    data::{code::LxCodeTokenData, LxTokenData},
    idx::{LxCodeTokenIdx, LxRoseTokenIdx, LxTokenIdxRange},
};
use crate::{
    data::{math::LxMathTokenData, rose::LxRoseTokenData},
    idx::{LxMathTokenIdx, LxTokenIdx},
};
use husky_text_protocol::{offset::TextOffsetRange, range::TextRange};

#[salsa::derive_debug_with_db]
#[derive(Default, Debug)]
pub struct LxTokenStorage {
    ranged_tokens: Vec<(TextOffsetRange, TextRange, LxTokenData)>,
}

impl std::ops::Index<LxMathTokenIdx> for LxTokenStorage {
    type Output = LxMathTokenData;

    fn index(&self, idx: LxMathTokenIdx) -> &Self::Output {
        match &self.ranged_tokens[idx.0.index()].2 {
            LxTokenData::Math(data) => data,
            _ => unreachable!(),
        }
    }
}

impl std::ops::Index<LxRoseTokenIdx> for LxTokenStorage {
    type Output = LxRoseTokenData;

    fn index(&self, idx: LxRoseTokenIdx) -> &Self::Output {
        match &self.ranged_tokens[idx.0.index()].2 {
            LxTokenData::Rose(data) => data,
            _ => unreachable!(),
        }
    }
}

impl std::ops::Index<LxTokenIdx> for LxTokenStorage {
    type Output = (TextOffsetRange, TextRange, LxTokenData);

    fn index(&self, idx: LxTokenIdx) -> &Self::Output {
        &self.ranged_tokens[idx.index()]
    }
}

/// # getters

impl LxTokenStorage {
    pub fn ranged_tokens(&self) -> &[(TextOffsetRange, TextRange, LxTokenData)] {
        &self.ranged_tokens
    }

    pub fn whole_token_idx_range(&self) -> LxTokenIdxRange {
        LxTokenIdxRange::new(0..self.ranged_tokens.len())
    }

    #[track_caller]
    pub fn token_offset_range(
        &self,
        token_idx: impl std::borrow::Borrow<LxTokenIdx>,
    ) -> TextOffsetRange {
        self.ranged_tokens[token_idx.borrow().index()].0
    }

    pub fn token_idx_range_offset_range(&self, range: LxTokenIdxRange) -> TextOffsetRange {
        match range.last() {
            Some(last) => {
                let first = self.token_offset_range(range.start());
                let last = self.token_offset_range(last);
                first.join(last)
            }
            None => TextOffsetRange::new(0.into(), 0.into()),
        }
    }
}

/// # actions

impl LxTokenStorage {
    pub(crate) fn alloc_math_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxMathTokenData,
    ) -> LxMathTokenIdx {
        let idx = LxMathTokenIdx(LxTokenIdx::from_index(self.ranged_tokens.len()));
        self.ranged_tokens
            .push((offset_range, range, token_data.into()));
        idx
    }

    pub(crate) fn alloc_rose_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxRoseTokenData,
    ) -> LxRoseTokenIdx {
        let idx = LxRoseTokenIdx(LxTokenIdx::from_index(self.ranged_tokens.len()));
        self.ranged_tokens
            .push((offset_range, range, token_data.into()));
        idx
    }

    pub(crate) fn alloc_code_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxCodeTokenData,
    ) -> LxCodeTokenIdx {
        let idx = LxCodeTokenIdx(LxTokenIdx::from_index(self.ranged_tokens.len()));
        self.ranged_tokens
            .push((offset_range, range, token_data.into()));
        idx
    }
}

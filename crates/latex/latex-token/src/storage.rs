use crate::lane::{LxTokenAnnotationLane, LxTokenLane};
use crate::{
    idx::{
        LxLispTokenIdx, LxNameTokenIdx, LxRootTokenIdx, LxRoseTokenIdx, LxSpecTokenIdx,
        LxTokenIdxRange,
    },
    token::{
        lisp::LxLispTokenData, name::LxNameTokenData, root::LxRootTokenData, spec::LxSpecTokenData,
        LxTokenData,
    },
};
use crate::{
    idx::{LxMathTokenIdx, LxTokenIdx},
    token::{math::LxMathTokenData, rose::LxRoseTokenData},
};
use husky_text_protocol::{offset::TextOffsetRange, range::TextRange};
use rustc_hash::FxHashMap;

#[salsa::derive_debug_with_db]
#[derive(Default, Debug)]
pub struct LxTokenStorage {
    main_ranged_tokens: Vec<LxTokenEntry>,
    annotation_ranged_tokens: FxHashMap<LxTokenAnnotationLane, Vec<LxTokenEntry>>,
}

#[derive(Debug)]
pub struct LxTokenEntry {
    text_offset_range: TextOffsetRange,
    text_range: TextRange,
    data: LxTokenData,
}

impl LxTokenEntry {
    pub fn text_offset_range(&self) -> TextOffsetRange {
        self.text_offset_range
    }

    pub fn text_range(&self) -> TextRange {
        self.text_range
    }

    pub fn data(&self) -> LxTokenData {
        self.data
    }
}

impl std::ops::Index<LxTokenIdx> for LxTokenStorage {
    type Output = LxTokenEntry;

    fn index(&self, idx: LxTokenIdx) -> &Self::Output {
        match idx.lane() {
            LxTokenLane::Main => &self.main_ranged_tokens[idx.index()],
            LxTokenLane::Annotation(lx_token_annotation_lane) => {
                &self.annotation_ranged_tokens[&lx_token_annotation_lane][idx.index()]
            }
        }
    }
}

impl std::ops::Index<LxTokenLane> for LxTokenStorage {
    type Output = Vec<LxTokenEntry>;

    fn index(&self, lane: LxTokenLane) -> &Self::Output {
        match lane {
            LxTokenLane::Main => &self.main_ranged_tokens,
            LxTokenLane::Annotation(lane) => self.annotation_ranged_tokens.get(&lane).unwrap(),
        }
    }
}

impl std::ops::IndexMut<LxTokenLane> for LxTokenStorage {
    fn index_mut(&mut self, lane: LxTokenLane) -> &mut Self::Output {
        match lane {
            LxTokenLane::Main => &mut self.main_ranged_tokens,
            LxTokenLane::Annotation(lane) => self.annotation_ranged_tokens.get_mut(&lane).unwrap(),
        }
    }
}

impl std::ops::Index<LxMathTokenIdx> for LxTokenStorage {
    type Output = LxMathTokenData;

    fn index(&self, idx: LxMathTokenIdx) -> &Self::Output {
        match self[*idx].data {
            LxTokenData::Math(ref data) => data,
            _ => unreachable!(),
        }
    }
}

impl std::ops::Index<LxRoseTokenIdx> for LxTokenStorage {
    type Output = LxRoseTokenData;

    fn index(&self, idx: LxRoseTokenIdx) -> &Self::Output {
        match self[*idx].data {
            LxTokenData::Rose(ref data) => data,
            _ => unreachable!(),
        }
    }
}

/// # getters

impl LxTokenStorage {
    // pub fn ranged_tokens(&self) -> &[(TextOffsetRange, TextRange, LxTokenData)] {
    //     &self.ranged_tokens
    // }

    pub fn whole_token_idx_range(&self, lane: LxTokenLane) -> LxTokenIdxRange {
        LxTokenIdxRange::from_usize_range(lane, 0..self[lane].len())
    }

    #[track_caller]
    pub fn token_offset_range(
        &self,
        token_idx: impl std::borrow::Borrow<LxTokenIdx>,
    ) -> TextOffsetRange {
        self[*token_idx.borrow()].text_offset_range
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
        lane: LxTokenLane,
        text_offset_range: TextOffsetRange,
        text_range: TextRange,
        token_data: LxMathTokenData,
    ) -> LxMathTokenIdx {
        let ranged_tokens = &mut self[lane];
        let idx = LxMathTokenIdx(LxTokenIdx::from_index(lane, ranged_tokens.len()));
        ranged_tokens.push(LxTokenEntry {
            text_offset_range,
            text_range,
            data: token_data.into(),
        });
        idx
    }

    pub(crate) fn alloc_rose_token(
        &mut self,
        lane: LxTokenLane,
        text_offset_range: TextOffsetRange,
        text_range: TextRange,
        token_data: LxRoseTokenData,
    ) -> LxRoseTokenIdx {
        let ranged_tokens = &mut self[lane];
        let idx = LxRoseTokenIdx(LxTokenIdx::from_index(lane, ranged_tokens.len()));
        ranged_tokens.push(LxTokenEntry {
            text_offset_range,
            text_range,
            data: token_data.into(),
        });
        idx
    }

    pub(crate) fn alloc_coword_token(
        &mut self,
        lane: LxTokenLane,
        text_offset_range: TextOffsetRange,
        text_range: TextRange,
        token_data: LxNameTokenData,
    ) -> LxNameTokenIdx {
        let ranged_tokens = &mut self[lane];
        let idx = LxNameTokenIdx(LxTokenIdx::from_index(lane, ranged_tokens.len()));
        ranged_tokens.push(LxTokenEntry {
            text_offset_range,
            text_range,
            data: token_data.into(),
        });
        idx
    }

    pub(crate) fn alloc_lisp_token(
        &mut self,
        lane: LxTokenLane,
        text_offset_range: TextOffsetRange,
        text_range: TextRange,
        token_data: LxLispTokenData,
    ) -> LxLispTokenIdx {
        let ranged_tokens = &mut self[lane];
        let idx = LxLispTokenIdx(LxTokenIdx::from_index(lane, ranged_tokens.len()));
        ranged_tokens.push(LxTokenEntry {
            text_offset_range,
            text_range,
            data: token_data.into(),
        });
        idx
    }

    pub(crate) fn alloc_root_token(
        &mut self,
        lane: LxTokenLane,
        text_offset_range: TextOffsetRange,
        text_range: TextRange,
        token_data: LxRootTokenData,
    ) -> LxRootTokenIdx {
        let ranged_tokens = &mut self[lane];
        let idx = LxRootTokenIdx(LxTokenIdx::from_index(lane, ranged_tokens.len()));
        ranged_tokens.push(LxTokenEntry {
            text_offset_range,
            text_range,
            data: token_data.into(),
        });
        idx
    }

    pub(crate) fn alloc_spec_token(
        &mut self,
        lane: LxTokenLane,
        text_offset_range: TextOffsetRange,
        text_range: TextRange,
        token_data: LxSpecTokenData,
    ) -> LxSpecTokenIdx {
        let ranged_tokens = &mut self[lane];
        let idx = LxSpecTokenIdx(LxTokenIdx::from_index(lane, ranged_tokens.len()));
        ranged_tokens.push(LxTokenEntry {
            text_offset_range,
            text_range,
            data: token_data.into(),
        });
        idx
    }
}

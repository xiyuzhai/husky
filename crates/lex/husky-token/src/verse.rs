//! a token verse is tokens in a verse, where a verse is a line or a group of lines,
//! determined by the tokens
mod builder;
pub mod idx;
pub mod iter;
mod sequence;
pub mod start;

use self::{builder::*, idx::TokenVerseIdx};
use self::{iter::TokenVerseIter, start::*};
use crate::{
    verse::sequence::{MainTokenVerseSequence, NestedTokenVerseSequence},
    *,
};
use vec_like::{AsVecMapEntry, VecMap};

/// 0-based
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct TokenVerseRelativeTokenIndex(usize);

impl TokenVerseRelativeTokenIndex {
    pub(crate) fn new(base: TokenVerseStart, token_idx: TokenIdx) -> Self {
        debug_assert!(base.token_idx() <= token_idx);
        Self(token_idx.index() - base.index())
    }

    pub(crate) fn index(self) -> usize {
        self.0
    }

    pub(crate) fn token_idx(self, base: TokenVerseStart) -> TokenIdx {
        base.token_idx() + self.0
    }
}

impl std::ops::AddAssign<usize> for TokenVerseRelativeTokenIndex {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs
    }
}

impl std::ops::SubAssign<usize> for TokenVerseRelativeTokenIndex {
    fn sub_assign(&mut self, rhs: usize) {
        self.0 -= rhs
    }
}

pub struct TokenVerse<'a> {
    tokens: &'a [TokenData],
    indent: u32,
}

/// # getters
impl<'a> TokenVerse<'a> {
    pub fn first(&self) -> TokenData {
        *self.tokens.first().unwrap()
    }

    pub fn second(&self) -> Option<TokenData> {
        self.tokens.get(1).copied()
    }

    pub fn last(&self) -> TokenData {
        *self.tokens.last().unwrap()
    }

    pub fn indent(&self) -> u32 {
        self.indent
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct TokenVerses {
    main_sequence: MainTokenVerseSequence,
    nested_sequences: VecMap<NestedTokenVerseSequence>,
}

/// # constructor
impl TokenVerses {
    pub(crate) fn new(tokens_data: &[TokenData], token_ranges: &[TextPositionRange]) -> Self {
        let line_starts = produce_line_starts(token_ranges);
        TokenVersesBuilder::new(tokens_data, token_ranges, &line_starts).build_all()
    }
}

/// # getters
impl TokenVerses {
    pub fn get(&self, idx: TokenVerseIdx) -> Option<&TokenVerseData> {
        match idx.lcurl() {
            Some(lcurl) => self.nested_sequences[lcurl].verses_data().get(idx.index()),
            None => self.main_sequence.verses_data().get(idx.index()),
        }
    }

    pub fn main_sequence(&self) -> &MainTokenVerseSequence {
        &self.main_sequence
    }

    pub fn main_token_verse_iter<'a>(&'a self, tokens: &'a [TokenData]) -> TokenVerseIter<'a> {
        self.main_sequence.token_verse_iter(tokens)
    }

    pub fn nested_sequences(&self) -> &VecMap<NestedTokenVerseSequence> {
        &self.nested_sequences
    }

    pub fn token_verse_idx(&self, token_idx: TokenIdx) -> TokenVerseIdx {
        assert!(self.main_sequence.verses_data()[0].start().index() == 0);
        let t = |verses_data: &[TokenVerseData]| -> usize {
            match verses_data.binary_search_by(|base| base.start().token_idx().cmp(&token_idx)) {
                Ok(i) => i,
                Err(i) => {
                    assert!(i > 0);
                    i - 1
                }
            }
        };
        // mutable because it might be overriden by searching in nested token verses
        let mut token_verse_idx = TokenVerseIdx::new(None, t(self.main_sequence.verses_data()));
        for nested_sequence in self.nested_sequences.iter() {
            let verses_data = nested_sequence.verses_data();
            if token_idx < nested_sequence.end() && token_idx >= verses_data[0].start().token_idx()
            {
                // Invariant: this block is entered at most once per function call
                token_verse_idx = TokenVerseIdx::new(
                    Some(nested_sequence.lcurl()),
                    t(self.main_sequence.verses_data()),
                );
            }
        }
        token_verse_idx
    }

    pub fn token_verse_token_idx_range(
        &self,
        token_verse_idx: TokenVerseIdx,
        tokens_len: usize,
    ) -> TokenIdxRange {
        let verses_data = match token_verse_idx.lcurl() {
            None => self.main_sequence.verses_data(),
            Some(lcurl) => self.nested_sequences[lcurl].verses_data(),
        };
        let token_verse_index = token_verse_idx.index();
        let start = verses_data[token_verse_index].start().index();
        let end = verses_data
            .get(token_verse_index + 1)
            .map(|end| end.start().index())
            .unwrap_or(tokens_len);
        TokenIdxRange::from_indices(start, end)
    }
}

impl std::ops::Index<TokenVerseIdx> for TokenVerses {
    type Output = TokenVerseData;

    #[track_caller]
    fn index(&self, idx: TokenVerseIdx) -> &Self::Output {
        self.get(idx).unwrap()
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct TokenVerseData {
    start: TokenVerseStart,
    indent: u32,
}

/// # getters
impl TokenVerseData {
    pub fn new(start: TokenVerseStart, indent: u32) -> Self {
        Self { start, indent }
    }

    pub fn start(&self) -> TokenVerseStart {
        self.start
    }

    pub fn indent(&self) -> u32 {
        self.indent
    }
}

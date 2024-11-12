//! `Region` is a concept coined to achieve fast incremental compilation, it is the smallest unit of change.
//!
//!
mod base;
#[cfg(test)]
mod tests;
mod token;
mod token_idx;
mod token_idx_range;
mod tokens_data;
mod verse;

pub use self::base::*;
pub use self::token::*;
pub use self::token_idx::*;
pub use self::token_idx_range::*;
pub use self::tokens_data::*;
pub use self::verse::*;

#[cfg(test)]
use crate::tests::*;
use husky_coword::Ident;
use husky_token::verse::{idx::TokenVerseIdx, start::TokenVerseStart};
use husky_token::*;
use husky_token_data::{delimiter::Delimiter, *};
#[cfg(test)]
use parsec::TryParseOptionFromStream;
use parsec::{HasStreamState, IsStreamParser};
use shifted_unsigned_int::ShiftedU32;
use std::num::NonZeroU32;
use verse::{start::RegionalTokenVerseStart, token_index::RegionalTokenVerseRelativeTokenIndex};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegionalTokenVerseIdxBase(u32);

impl RegionalTokenVerseIdxBase {
    pub fn index(self) -> usize {
        self.0 as usize
    }

    fn from_index(index: usize) -> Self {
        debug_assert!(index <= u32::MAX as usize);
        Self(index as u32)
    }

    pub fn from_token_verse_idx(token_verse_idx: TokenVerseIdx) -> Self {
        Self::from_index(token_verse_idx.index())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RegionalTokenVerseIdx {
    /// None if the verse is main,
    ///
    /// Some(_) if the verse is nested
    lcurl: Option<RegionalTokenIdx>,
    /// if `lcurl` is `Some(_)`, this is equal to raw of `TokenVerseIdx`
    raw: ShiftedU32,
}

impl RegionalTokenVerseIdx {
    pub fn new(
        token_verse_idx: TokenVerseIdx,
        regional_token_verse_idx_base: RegionalTokenVerseIdxBase,
        regional_token_idx_base: RegionalTokenIdxBase,
    ) -> Self {
        let lcurl = token_verse_idx
            .lcurl()
            .map(|lcurl| RegionalTokenIdx::from_token_idx(lcurl, regional_token_idx_base));
        let index = match lcurl {
            Some(_) => token_verse_idx.index(), // nested verse sequence is contained entirely in one region
            None => token_verse_idx.index() - regional_token_verse_idx_base.index(),
        };
        debug_assert!(index <= u32::MAX as usize);
        Self {
            lcurl,
            raw: index.into(),
        }
    }

    pub fn index(self) -> usize {
        self.raw.into()
    }

    pub fn lcurl(self) -> Option<RegionalTokenIdx> {
        self.lcurl
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct RegionalTokenStreamState {
    next_regional_token_idx: RegionalTokenIdx,
    drained: bool,
}

impl RegionalTokenStreamState {
    pub fn from_token_stream_state(
        token_stream_state: TokenStreamState,
        regional_token_idx_base: RegionalTokenIdxBase,
    ) -> Self {
        Self {
            next_regional_token_idx: RegionalTokenIdx::from_token_idx(
                token_stream_state.next_token_idx(),
                regional_token_idx_base,
            ),
            drained: token_stream_state.drained(),
        }
    }

    pub fn next_regional_token_idx(self) -> RegionalTokenIdx {
        self.next_regional_token_idx
    }

    pub fn drained(self) -> bool {
        self.drained
    }

    pub fn token_stream_state(self, base: RegionalTokenIdxBase) -> TokenStreamState {
        unsafe { TokenStreamState::new(self.next_regional_token_idx.token_idx(base), self.drained) }
    }
}

pub struct RegionalTokenStream<'a> {
    start: RegionalTokenVerseStart,
    tokens: &'a [TokenData],
    next_relative: RegionalTokenVerseRelativeTokenIndex,
}

impl<'a> HasStreamState for RegionalTokenStream<'a> {
    type State = RegionalTokenStreamState;

    fn state(&self) -> Self::State {
        RegionalTokenStreamState {
            next_regional_token_idx: self.next_relative.regional_token_idx(self.start),
            drained: self.next_relative.index() >= self.tokens.len(),
        }
    }

    fn rollback(&mut self, state: Self::State) {
        self.rollback_raw(state.next_regional_token_idx)
    }
}

impl<'a> Iterator for RegionalTokenStream<'a> {
    type Item = &'a TokenData;

    fn next(&mut self) -> Option<&'a TokenData> {
        if self.next_relative.index() < self.tokens.len() {
            let next = self.next_relative;
            self.next_relative += 1;
            Some(&self.tokens[next.index()])
        } else {
            None
        }
    }
}

impl<'a> RegionalTokenStream<'a> {
    pub fn new_snippet_regional_token_stream(tokens: &'a [TokenData]) -> Self {
        let start = RegionalTokenVerseStart::from_index(0);
        Self {
            start,
            tokens,
            next_relative: Default::default(),
        }
    }

    pub fn new_crate_decl_regional_token_stream(
        tokens: &'a [TokenData],
        start: RegionalTokenVerseStart,
    ) -> Self {
        Self {
            start,
            tokens,
            next_relative: Default::default(),
        }
    }

    pub fn new_item_decl_regional_token_stream(
        tokens: &'a [TokenData],
        saved_regional_token_stream_state: Option<RegionalTokenStreamState>,
    ) -> Self {
        let start = RegionalTokenVerseStart::from_index(0);
        Self {
            start,
            tokens,
            next_relative: saved_regional_token_stream_state
                .map(|regional_token_stream_state| {
                    RegionalTokenVerseRelativeTokenIndex::new(
                        start,
                        regional_token_stream_state.next_regional_token_idx(),
                    )
                })
                .unwrap_or_default(),
        }
    }

    pub fn new_item_defn_regional_token_stream(
        tokens: &'a [TokenData],
        start: RegionalTokenVerseStart,
    ) -> Self {
        Self {
            start,
            tokens,
            next_relative: Default::default(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.next_relative.index() >= self.tokens.len()
    }

    pub fn token_position(&self) -> usize {
        self.next_relative.index()
    }

    pub fn try_get_one_token_with_indexed<S>(
        &mut self,
        f: impl Fn(&TokenData) -> Option<S>,
    ) -> Option<(RegionalTokenIdx, S)> {
        let (token_idx, token) = self.next_indexed()?;
        if let Some(s) = f(&token) {
            Some((token_idx, s))
        } else {
            self.go_back();
            None
        }
    }

    pub fn try_eat_with(
        &mut self,
        predicate: impl FnOnce(&TokenData) -> bool,
    ) -> Option<&'a TokenData> {
        let token = self.peek()?;
        if predicate(&token) {
            self.next();
            Some(token)
        } else {
            None
        }
    }

    pub fn try_eat_special(&mut self, punc: Punctuation) -> Option<&'a TokenData> {
        self.try_eat_with(|token_kind| token_kind == &TokenData::Punctuation(punc))
    }

    pub fn go_back(&mut self) {
        assert!(self.next_relative.index() > 0);
        self.next_relative -= 1;
    }

    pub fn rollback(&mut self, state: RegionalTokenIdx) {
        self.set_state(state)
    }

    pub fn set_state(&mut self, state: RegionalTokenIdx) {
        self.next_relative = RegionalTokenVerseRelativeTokenIndex::new(self.start, state);
    }

    pub fn next_index(&self) -> RegionalTokenIdx {
        self.next_relative.regional_token_idx(self.start)
    }

    pub fn next_indexed(&mut self) -> Option<(RegionalTokenIdx, TokenData)> {
        if self.next_relative.index() < self.tokens.len() {
            let next = self.next_relative;
            self.next_relative += 1;
            Some((
                next.regional_token_idx(self.start),
                self.tokens[next.index()],
            ))
        } else {
            None
        }
    }

    pub fn step_back(&mut self) {
        assert!(self.next_relative.index() > 0);
        self.next_relative -= 1
    }

    pub fn peek(&self) -> Option<&'a TokenData> {
        if self.next_relative.index() < self.tokens.len() {
            Some(&self.tokens[self.next_relative.index()])
        } else {
            None
        }
    }

    pub fn peek_next_bra(&mut self) -> Option<Delimiter> {
        if self.next_relative.index() < self.tokens.len() {
            match self.tokens[self.next_relative.index()] {
                TokenData::Punctuation(_punct) => todo!(),
                //  punct.opt_bra(),
                _ => None,
            }
        } else {
            None
        }
    }

    pub fn is_next_ident(&mut self) -> bool {
        match self.peek() {
            Some(token) => match token {
                TokenData::Ident(_) => true,
                _ => false,
            },
            None => false,
        }
    }

    pub fn tokens(&self) -> &[TokenData] {
        self.tokens
    }

    pub fn rollback_raw(&mut self, token_idx: RegionalTokenIdx) {
        self.next_relative = RegionalTokenVerseRelativeTokenIndex::new(self.start, token_idx)
    }
}

pub trait RegionalTokenStreamParser<'a>:
    HasStreamState<State = RegionalTokenStreamState>
    + IsStreamParser
    + core::borrow::BorrowMut<RegionalTokenStream<'a>>
{
    fn token_stream(&self) -> &RegionalTokenStream<'a> {
        self.borrow()
    }

    fn token_stream_mut(&mut self) -> &mut RegionalTokenStream<'a> {
        self.borrow_mut()
    }
}

// impl<'a> TokenParseContext<'a> for TokenIter<'a> {}

impl<'a, T> RegionalTokenStreamParser<'a> for T where
    T: HasStreamState<State = RegionalTokenStreamState>
        + IsStreamParser
        + core::borrow::BorrowMut<RegionalTokenStream<'a>>
{
}

#[cfg(test)]
fn quick_parse<T, Error>(db: &::salsa::Db, input: &str) -> Result<Option<T>, Error>
where
    T: for<'a> TryParseOptionFromStream<RegionalTokenStream<'a>, Error = Error>,
{
    use husky_vfs::{
        script::{Script, ScriptSource},
        test_helpers::VfsTestUtilsDb,
    };

    let token_sheet = db.chunk_token_sheet_data(Script::new(
        db,
        ScriptSource::Snippet {
            toolchain: db.dev_toolchain().unwrap(),
        },
        input.to_owned(),
    ));
    RegionalTokenStream::new_snippet_regional_token_stream(token_sheet.tokens()).try_parse_option()
}

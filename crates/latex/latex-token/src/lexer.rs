use crate::{
    idx::{
        LxLispTokenIdx, LxMathTokenIdx, LxNameTokenIdx, LxRootTokenIdx, LxRoseTokenIdx,
        LxSpecTokenIdx,
    },
    lane::LxTokenLane,
    storage::LxTokenStorage,
    stream::{
        lisp::LxLispTokenStream, math::LxMathTokenStream, root::LxRootTokenStream,
        rose::LxRoseTokenStream, word::LxWordTokenStream,
    },
    token::{
        lisp::LxLispTokenData,
        math::{LxMathTokenData, LxMathTokenError},
        name::LxNameTokenData,
        root::LxRootTokenData,
        rose::LxRoseTokenData,
        spec::LxSpecTokenData,
    },
};
use husky_coword::Coword;
use husky_text_protocol::{char::TextCharIter, offset::TextOffsetRange, range::TextRange};
use latex_prelude::mode::LxMode;

pub struct LxLexer<'a> {
    pub(crate) db: &'a ::salsa::Db,
    pub(crate) chars: TextCharIter<'a>,
    lane: LxTokenLane,
    pub(crate) storage: &'a mut LxTokenStorage,
}

/// # constructor
impl<'a> LxLexer<'a> {
    pub fn new(
        db: &'a ::salsa::Db,
        input: &'a str,
        lane: LxTokenLane,
        storage: &'a mut LxTokenStorage,
    ) -> Self {
        Self {
            db,
            chars: TextCharIter::new(input),
            lane,
            storage,
        }
    }
}

/// # actions
impl<'a> LxLexer<'a> {
    pub(crate) fn next_coword_with(&mut self, predicate: impl Fn(char) -> bool) -> Option<Coword> {
        let coword_str_slice = self.chars.next_str_slice_while(predicate);
        if coword_str_slice.is_empty() {
            return None;
        }
        Some(Coword::from_ref(self.db, coword_str_slice))
    }

    pub(crate) fn eat_spaces_and_tabs(&mut self) {
        self.chars.eat_chars_while(|c| c == ' ' || c == '\t');
    }

    pub(crate) fn eat_spaces_and_tabs_and_comments(&mut self) {
        loop {
            self.chars.eat_chars_while(|c| c == ' ' || c == '\t');
            if self.chars.peek() == Some('%') {
                self.chars.eat_chars_while(|c| c != '\n');
            } else {
                break;
            }
        }
    }

    pub(crate) fn eat_spaces_and_tabs_and_lines_and_comments(&mut self) {
        loop {
            self.chars
                .eat_chars_while(|c| c == ' ' || c == '\t' || c == '\n');
            if self.chars.peek() == Some('%') {
                self.chars.eat_chars_while(|c| c != '\n');
            } else {
                break;
            }
        }
    }

    pub(crate) fn alloc_root_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxRootTokenData,
    ) -> LxRootTokenIdx {
        self.storage
            .alloc_root_token(self.lane, offset_range, range, token_data)
    }

    pub(crate) fn alloc_rose_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxRoseTokenData,
    ) -> LxRoseTokenIdx {
        self.storage
            .alloc_rose_token(self.lane, offset_range, range, token_data)
    }

    pub(crate) fn alloc_math_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxMathTokenData,
    ) -> LxMathTokenIdx {
        self.storage
            .alloc_math_token(self.lane, offset_range, range, token_data)
    }

    pub(crate) fn alloc_name_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxNameTokenData,
    ) -> LxNameTokenIdx {
        self.storage
            .alloc_coword_token(self.lane, offset_range, range, token_data)
    }

    pub(crate) fn alloc_spec_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxSpecTokenData,
    ) -> LxSpecTokenIdx {
        self.storage
            .alloc_spec_token(self.lane, offset_range, range, token_data)
    }

    pub(crate) fn alloc_lisp_token(
        &mut self,
        offset_range: TextOffsetRange,
        range: TextRange,
        token_data: LxLispTokenData,
    ) -> LxLispTokenIdx {
        self.storage
            .alloc_lisp_token(self.lane, offset_range, range, token_data)
    }

    pub(crate) fn into_word_stream(self) -> LxWordTokenStream<'a> {
        LxWordTokenStream::new(self)
    }

    pub fn into_math_stream(self) -> LxMathTokenStream<'a> {
        LxMathTokenStream::new(self)
    }

    pub(crate) fn into_root_stream(self) -> LxRootTokenStream<'a> {
        LxRootTokenStream::new(self)
    }

    pub(crate) fn into_rose_stream(self) -> LxRoseTokenStream<'a> {
        LxRoseTokenStream::new(self)
    }

    pub(crate) fn into_lisp_stream(self) -> LxLispTokenStream<'a> {
        LxLispTokenStream::new(self)
    }
}

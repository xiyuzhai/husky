use crate::{
    data::{
        code::LxCodeTokenData,
        math::{LxMathTokenData, LxMathTokenError},
        rose::LxRoseTokenData,
    },
    idx::{LxCodeTokenIdx, LxMathTokenIdx, LxRoseTokenIdx},
    storage::LxTokenStorage,
    stream::{code::LxCodeTokenStream, math::LxMathTokenStream, rose::LxRoseTokenStream},
};
use husky_coword::Coword;
use husky_text_protocol::{char::TextCharIter, offset::TextOffsetRange, range::TextRange};
use latex_prelude::mode::LxMode;

pub struct LxLexer<'a> {
    pub(crate) db: &'a ::salsa::Db,
    pub(crate) chars: TextCharIter<'a>,
    pub(crate) storage: &'a mut LxTokenStorage,
}

/// # constructor
impl<'a> LxLexer<'a> {
    pub fn new(db: &'a ::salsa::Db, input: &'a str, storage: &'a mut LxTokenStorage) -> Self {
        Self {
            db,
            chars: TextCharIter::new(input),
            storage,
        }
    }
}

/// # actions
impl<'a> LxLexer<'a> {
    pub fn next_math_token(&mut self) -> Option<(LxMathTokenIdx, LxMathTokenData)> {
        let (offset_range, range, token_data) = self.next_math_token_aux()?;
        Some((
            self.storage
                .alloc_math_token(offset_range, range, token_data),
            token_data,
        ))
    }

    fn next_math_token_aux(&mut self) -> Option<(TextOffsetRange, TextRange, LxMathTokenData)> {
        self.chars.eat_chars_while(|c| c == ' ');
        let mut start_offset = self.chars.current_offset();
        let mut start_position = self.chars.current_position();
        let token_data = if self.chars.eat_char_if(|c| c == '\n') {
            self.chars.eat_chars_while(|c| c == ' ');
            if self.chars.eat_char_if(|c| c == '\n') {
                Some(LxMathTokenData::Error(
                    LxMathTokenError::UnexpectedNewParagraph,
                ))
            } else {
                self.next_math_token_data()
            }
        } else {
            self.next_math_token_data()
        }?;
        let end_offset = self.chars.current_offset();
        let range = TextRange {
            start: start_position,
            end: self.chars.current_position(),
        };
        Some(((start_offset..end_offset).into(), range, token_data))
    }

    pub fn peek_math_token_data(&mut self) -> Option<LxMathTokenData> {
        let chars = self.chars.clone();
        let (_, _, token_data) = self.next_math_token_aux()?;
        self.chars = chars;
        Some(token_data)
    }

    pub fn next_rose_token(&mut self) -> Option<(LxRoseTokenIdx, LxRoseTokenData)> {
        let (offset_range, range, token_data) = self.next_rose_token_aux()?;
        Some((
            self.storage
                .alloc_rose_token(offset_range, range, token_data),
            token_data,
        ))
    }

    fn next_rose_token_aux(&mut self) -> Option<(TextOffsetRange, TextRange, LxRoseTokenData)> {
        self.chars.eat_chars_while(|c| c == ' ');
        let mut start_offset = self.chars.current_offset();
        let mut start_position = self.chars.current_position();

        let token_data = if self.chars.eat_char_if(|c| c == '\n') {
            self.chars.eat_chars_while(|c| c == ' ');
            if self.chars.eat_char_if(|c| c == '\n') {
                self.chars.eat_chars_while(|c| c == '\n' || c == ' ');
                LxRoseTokenData::NewParagraph
            } else {
                start_offset = self.chars.current_offset();
                start_position = self.chars.current_position();
                self.next_rose_token_data()?
            }
        } else {
            self.next_rose_token_data()?
        };
        let end_offset = self.chars.current_offset();
        let range = TextRange {
            start: start_position,
            end: self.chars.current_position(),
        };
        Some(((start_offset..end_offset).into(), range, token_data))
    }

    pub fn peek_rose_token_data(&mut self) -> Option<LxRoseTokenData> {
        let chars = self.chars.clone();
        let (_, _, token_data) = self.next_rose_token_aux()?;
        self.chars = chars;
        Some(token_data)
    }

    pub fn next_code_token(&mut self) -> Option<(LxCodeTokenIdx, LxCodeTokenData)> {
        let (offset_range, range, token_data) = self.next_code_token_aux()?;
        Some((
            self.storage
                .alloc_code_token(offset_range, range, token_data),
            token_data,
        ))
    }

    fn next_code_token_aux(&mut self) -> Option<(TextOffsetRange, TextRange, LxCodeTokenData)> {
        self.chars.eat_chars_while(|c| c == ' ');
        let mut start_offset = self.chars.current_offset();
        let mut start_position = self.chars.current_position();
        let token_data = if self.chars.eat_char_if(|c| c == '\n') {
            self.chars.eat_chars_while(|c| c == ' ');
            if self.chars.eat_char_if(|c| c == '\n') {
                todo!()
                // Some(LxCodeTokenData::Error(
                //     LxCodeTokenError::UnexpectedNewParagraph,
                // ))
            } else {
                self.next_code_token_data()
            }
        } else {
            self.next_code_token_data()
        }?;
        let end_offset = self.chars.current_offset();
        let range = TextRange {
            start: start_position,
            end: self.chars.current_position(),
        };
        Some(((start_offset..end_offset).into(), range, token_data))
    }

    pub(crate) fn next_coword_with(&mut self, predicate: impl Fn(char) -> bool) -> Option<Coword> {
        let coword_str_slice = self.chars.next_str_slice_while(|c| c.is_alphanumeric());
        if coword_str_slice.is_empty() {
            return None;
        }
        Some(Coword::from_ref(self.db, coword_str_slice))
    }

    pub fn into_math_stream(self) -> LxMathTokenStream<'a> {
        LxMathTokenStream::new(self)
    }

    pub(crate) fn into_rose_stream(self) -> LxRoseTokenStream<'a> {
        LxRoseTokenStream::new(self)
    }

    pub(crate) fn into_code_stream(self) -> LxCodeTokenStream<'a> {
        LxCodeTokenStream::new(self)
    }
}

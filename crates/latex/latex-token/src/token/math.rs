pub mod digit;

use self::digit::LxMathDigit;
use super::*;
use crate::idx::LxMathTokenIdx;
use husky_text_protocol::{offset::TextOffsetRange, range::TextPositionRange};
use latex_command::path::{LxCommandName, LxCommandNameResult};
use latex_math_letter::letter::LxMathLetter;
use latex_math_punctuation::LxMathPunctuation;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxMathTokenData {
    Command(LxCommandName),
    LeftDelimiter(LxMathDelimiter),
    RightDelimiter(LxMathDelimiter),
    Letter(LxMathLetter),
    Punctuation(LxMathPunctuation),
    Digit(LxMathDigit),
    Other(char),
    Subscript,
    Superscript,
    Error(LxMathTokenError),
    MathModeEnd,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxMathDelimiter {
    /// `{`,  `}`
    Curl,
}

impl LxMathDelimiter {
    pub fn left_latex_code(&self) -> &'static str {
        match self {
            LxMathDelimiter::Curl => "{",
        }
    }

    pub fn right_latex_code(&self) -> &'static str {
        match self {
            LxMathDelimiter::Curl => "}",
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxMathTokenError {
    UnexpectedNewParagraph,
}

impl<'a> LxLexer<'a> {
    pub fn next_math_token(&mut self) -> Option<(LxMathTokenIdx, LxMathTokenData)> {
        let (offset_range, range, token_data) = self.next_ranged_math_token_data()?;
        Some((
            self.alloc_math_token(offset_range, range, token_data),
            token_data,
        ))
    }

    fn next_ranged_math_token_data(
        &mut self,
    ) -> Option<(TextOffsetRange, TextPositionRange, LxMathTokenData)> {
        self.eat_spaces_and_tabs();
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
        let range = TextPositionRange {
            start: start_position,
            end: self.chars.current_position(),
        };
        Some(((start_offset..end_offset).into(), range, token_data))
    }

    pub fn peek_math_token_data(&mut self) -> Option<LxMathTokenData> {
        let chars = self.chars.clone();
        let (_, _, token_data) = self.next_ranged_math_token_data()?;
        self.chars = chars;
        Some(token_data)
    }
    pub(crate) fn next_math_token_data(&mut self) -> Option<LxMathTokenData> {
        let s = self.chars.peek_str();
        if s.starts_with("\\]") || s.starts_with("$") {
            return None;
        }
        match self.chars.peek()? {
            '\\' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some(c) => match c {
                        c if c.is_ascii_alphabetic() => {
                            let Ok(command_name) = LxCommandName::new2(
                                self.chars.next_str_slice_while(|c| c.is_ascii_alphabetic()),
                            ) else {
                                todo!()
                            };
                            Some(LxMathTokenData::Command(command_name))
                        }
                        c => {
                            self.chars.eat_char();
                            match c {
                                '{' => Some(LxMathTokenData::Punctuation(
                                    LxMathPunctuation::EscapedLcurl,
                                )),
                                '}' => Some(LxMathTokenData::Punctuation(
                                    LxMathPunctuation::EscapedRcurl,
                                )),
                                // TODO: handle `@` and others seen as command names
                                // latex really sucks
                                _ => todo!("c={c}"),
                            }
                        }
                    },
                    None => todo!(),
                }
            }
            n if n.is_ascii_digit() => {
                self.chars.eat_char();
                Some(LxMathTokenData::Digit(n.try_into().unwrap()))
            }
            c => {
                self.chars.eat_char();
                match c {
                    '.' => Some(LxMathTokenData::Punctuation(LxMathPunctuation::Ldot)),
                    '_' => Some(LxMathTokenData::Subscript),
                    '^' => Some(LxMathTokenData::Superscript),
                    '{' => Some(LxMathTokenData::LeftDelimiter(LxMathDelimiter::Curl)),
                    '}' => Some(LxMathTokenData::RightDelimiter(LxMathDelimiter::Curl)),
                    c => {
                        if let Some(letter) = LxMathLetter::try_from_char(c) {
                            Some(LxMathTokenData::Letter(letter))
                        } else if let Some(opr) = LxMathPunctuation::try_from_char(c) {
                            Some(LxMathTokenData::Punctuation(opr))
                        } else {
                            Some(LxMathTokenData::Other(c))
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn next_math_token_data_works() {
    fn t(input: &str, expected: &Expect) {
        use crate::lane::LxTokenLane;

        let mut storage = LxTokenStorage::default();
        let stream = LxLexer::new(input, LxTokenLane::Main, &mut storage).into_math_stream();
        let tokens: Vec<_> = stream.map(|(_, token_data)| token_data).collect();
        expected.assert_debug_eq(&tokens);
    }
    t(
        "hello",
        &expect![[r#"
            [
                Letter(
                    LowerLatin(
                        H,
                    ),
                ),
                Letter(
                    LowerLatin(
                        E,
                    ),
                ),
                Letter(
                    LowerLatin(
                        L,
                    ),
                ),
                Letter(
                    LowerLatin(
                        L,
                    ),
                ),
                Letter(
                    LowerLatin(
                        O,
                    ),
                ),
            ]
        "#]],
    );
    t(
        "0",
        &expect![[r#"
            [
                Digit(
                    Zero,
                ),
            ]
        "#]],
    );
    t(
        "0",
        &expect![[r#"
            [
                Digit(
                    Zero,
                ),
            ]
        "#]],
    );
    t(
        "0 0",
        &expect![[r#"
            [
                Digit(
                    Zero,
                ),
                Digit(
                    Zero,
                ),
            ]
        "#]],
    );
    t(
        "0\n0",
        &expect![[r#"
            [
                Digit(
                    Zero,
                ),
                Digit(
                    Zero,
                ),
            ]
        "#]],
    );
    t(
        "0\n\n0",
        &expect![[r#"
            [
                Digit(
                    Zero,
                ),
                Error(
                    UnexpectedNewParagraph,
                ),
                Digit(
                    Zero,
                ),
            ]
        "#]],
    );
    t(
        "{",
        &expect![[r#"
            [
                LeftDelimiter(
                    Curl,
                ),
            ]
        "#]],
    );
    t(
        "}",
        &expect![[r#"
            [
                RightDelimiter(
                    Curl,
                ),
            ]
        "#]],
    );
    t(
        "(",
        &expect![[r#"
            [
                Punctuation(
                    Lpar,
                ),
            ]
        "#]],
    );
    t(
        ")",
        &expect![[r#"
            [
                Punctuation(
                    Rpar,
                ),
            ]
        "#]],
    );
    t(
        "[",
        &expect![[r#"
            [
                Punctuation(
                    Lbox,
                ),
            ]
        "#]],
    );
    t(
        "]",
        &expect![[r#"
            [
                Punctuation(
                    Rbox,
                ),
            ]
        "#]],
    );
    t(
        "\\{",
        &expect![[r#"
            [
                Punctuation(
                    EscapedLcurl,
                ),
            ]
        "#]],
    );
    t(
        "\\}",
        &expect![[r#"
            [
                Punctuation(
                    EscapedRcurl,
                ),
            ]
        "#]],
    );
    t(
        "+",
        &expect![[r#"
            [
                Punctuation(
                    Add,
                ),
            ]
        "#]],
    );
    t(
        "x+1",
        &expect![[r#"
            [
                Letter(
                    LowerLatin(
                        X,
                    ),
                ),
                Punctuation(
                    Add,
                ),
                Digit(
                    One,
                ),
            ]
        "#]],
    );
    t(
        "x_1^a+1",
        &expect![[r#"
            [
                Letter(
                    LowerLatin(
                        X,
                    ),
                ),
                Subscript,
                Digit(
                    One,
                ),
                Superscript,
                Letter(
                    LowerLatin(
                        A,
                    ),
                ),
                Punctuation(
                    Add,
                ),
                Digit(
                    One,
                ),
            ]
        "#]],
    );
    t(
        "\\int",
        &expect![[r#"
            [
                Command(
                    LettersOnly(
                        LettersOnlyLxCommandName(
                            Coword(
                                "int",
                            ),
                        ),
                    ),
                ),
            ]
        "#]],
    );
    t(
        "\\int x^3\\sin^3xdx",
        &expect![[r#"
            [
                Command(
                    LettersOnly(
                        LettersOnlyLxCommandName(
                            Coword(
                                "int",
                            ),
                        ),
                    ),
                ),
                Letter(
                    LowerLatin(
                        X,
                    ),
                ),
                Superscript,
                Digit(
                    Three,
                ),
                Command(
                    LettersOnly(
                        LettersOnlyLxCommandName(
                            Coword(
                                "sin",
                            ),
                        ),
                    ),
                ),
                Superscript,
                Digit(
                    Three,
                ),
                Letter(
                    LowerLatin(
                        X,
                    ),
                ),
                Letter(
                    LowerLatin(
                        D,
                    ),
                ),
                Letter(
                    LowerLatin(
                        X,
                    ),
                ),
            ]
        "#]],
    );
}

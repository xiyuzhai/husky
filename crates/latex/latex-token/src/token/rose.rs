use super::*;
use crate::idx::LxRoseTokenIdx;
use husky_coword::Coword;
use husky_text_protocol::{offset::TextOffsetRange, range::TextRange};
use latex_command::path::LxCommandName;
use latex_rose_punctuation::LxRosePunctuation;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxRoseTokenData {
    Word(Coword),
    Command(LxCommandName),
    Nat32(u32),
    NewParagraph,
    Punctuation(LxRosePunctuation),
    LeftDelimiter(LxRoseDelimiter),
    RightDelimiter(LxRoseDelimiter),
    EmbeddedMathDelimiter(LxRoseEmbeddedMathDelimiter),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxRoseDelimiter {
    Curl,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxRoseEmbeddedMathDelimiter {
    /// `$`
    Dollar,
    /// `$$`
    DollarDollar,
    /// `\[`
    EscapedLbox,
    /// `\]`
    EscapedRbox,
}
impl LxRoseEmbeddedMathDelimiter {
    pub fn is_matching(self, right_delimiter: LxRoseEmbeddedMathDelimiter) -> bool {
        matches!(
            (self, right_delimiter),
            (
                LxRoseEmbeddedMathDelimiter::Dollar,
                LxRoseEmbeddedMathDelimiter::Dollar
            ) | (
                LxRoseEmbeddedMathDelimiter::DollarDollar,
                LxRoseEmbeddedMathDelimiter::DollarDollar
            ) | (
                LxRoseEmbeddedMathDelimiter::EscapedLbox,
                LxRoseEmbeddedMathDelimiter::EscapedRbox
            )
        )
    }
}

impl<'a> LxLexer<'a> {
    pub fn next_rose_token(&mut self) -> Option<(LxRoseTokenIdx, LxRoseTokenData)> {
        let (offset_range, range, token_data) = self.next_ranged_rose_token_data()?;
        Some((
            self.alloc_rose_token(offset_range, range, token_data),
            token_data,
        ))
    }

    fn next_ranged_rose_token_data(
        &mut self,
    ) -> Option<(TextOffsetRange, TextRange, LxRoseTokenData)> {
        self.eat_spaces_and_tabs_and_comments();
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
        let (_, _, token_data) = self.next_ranged_rose_token_data()?;
        self.chars = chars;
        Some(token_data)
    }
    pub(crate) fn next_rose_token_data(&mut self) -> Option<LxRoseTokenData> {
        let db = self.db;
        match self.chars.peek()? {
            '\\' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some(c) => match c {
                        c if c.is_ascii_alphabetic() => Some(LxRoseTokenData::Command(
                            LxCommandName::new(
                                self.next_coword_with(|c| c.is_ascii_alphabetic()).unwrap(),
                                db,
                            )
                            .unwrap(),
                        )),
                        '[' => {
                            self.chars.eat_char();
                            Some(LxRoseTokenData::EmbeddedMathDelimiter(
                                LxRoseEmbeddedMathDelimiter::EscapedLbox,
                            ))
                        }
                        ']' => {
                            self.chars.eat_char();
                            Some(LxRoseTokenData::EmbeddedMathDelimiter(
                                LxRoseEmbeddedMathDelimiter::EscapedRbox,
                            ))
                        }
                        c if c.is_numeric() => todo!("latex might allow single digit command"),
                        c => todo!("latex one digit non letter command: {}", c),
                    },
                    None => todo!(),
                }
            }
            n if n.is_numeric() => {
                let numeric_str_slice = self.chars.next_numeric_str_slice();
                match numeric_str_slice.parse::<u32>() {
                    Ok(number) => Some(LxRoseTokenData::Nat32(number)),
                    Err(_) => todo!(),
                }
            }
            a if a.is_ascii_alphabetic() => Some(LxRoseTokenData::Word(Coword::from_ref(
                self.db,
                self.chars.next_str_slice_while(|c| c.is_ascii_alphabetic()),
            ))),
            '$' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some('$') => {
                        self.chars.eat_char();
                        Some(LxRoseTokenData::EmbeddedMathDelimiter(
                            LxRoseEmbeddedMathDelimiter::DollarDollar,
                        ))
                    }
                    _ => Some(LxRoseTokenData::EmbeddedMathDelimiter(
                        LxRoseEmbeddedMathDelimiter::Dollar,
                    )),
                }
            }
            '{' => {
                self.chars.eat_char();
                Some(LxRoseTokenData::LeftDelimiter(LxRoseDelimiter::Curl))
            }
            '}' => {
                self.chars.eat_char();
                Some(LxRoseTokenData::RightDelimiter(LxRoseDelimiter::Curl))
            }
            '%' => {
                unreachable!()
            }
            c if let Some(punctuation) = LxRosePunctuation::try_from_char(c) => {
                self.chars.eat_char();
                Some(LxRoseTokenData::Punctuation(punctuation))
            }
            c => {
                use husky_print_utils::p;
                p!(c);
                todo!("unexpected char: {}", c)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(input: &str, expected: &Expect) {
        use crate::lane::LxTokenLane;

        let db = &DB::default();
        let mut storage = LxTokenStorage::default();
        let mut stream = LxLexer::new(db, input, LxTokenLane::Main, &mut storage)
            .into_rose_stream()
            .map(|(_, token_data)| token_data);
        let mut tokens: Vec<_> = stream.collect();
        expected.assert_debug_eq(&(tokens.debug(db)));
    }

    #[test]
    fn next_rose_token_data_works() {
        t(
            "",
            &expect![[r#"
        []
    "#]],
        );
        t(
            " ",
            &expect![[r#"
        []
    "#]],
        );
        t(
            "  ",
            &expect![[r#"
        []
    "#]],
        );
        t(
            "\n",
            &expect![[r#"
        []
    "#]],
        );
        t(
            "\n\n",
            &expect![[r#"
            [
                LxRoseTokenData::NewParagraph,
            ]
        "#]],
        );
        t(
            r#"

"#,
            &expect![[r#"
            [
                LxRoseTokenData::NewParagraph,
            ]
        "#]],
        );
        t(
            "hello",
            &expect![[r#"
            [
                LxRoseTokenData::Word(
                    Coword(
                        "hello",
                    ),
                ),
            ]
        "#]],
        );
        t(
            "0",
            &expect![[r#"
            [
                LxRoseTokenData::Nat32(
                    0,
                ),
            ]
        "#]],
        );
        t(
            " 0",
            &expect![[r#"
            [
                LxRoseTokenData::Nat32(
                    0,
                ),
            ]
        "#]],
        );
        t(
            "0 0",
            &expect![[r#"
            [
                LxRoseTokenData::Nat32(
                    0,
                ),
                LxRoseTokenData::Nat32(
                    0,
                ),
            ]
        "#]],
        );
        t(
            "0\n0",
            &expect![[r#"
            [
                LxRoseTokenData::Nat32(
                    0,
                ),
                LxRoseTokenData::Nat32(
                    0,
                ),
            ]
        "#]],
        );
        t(
            "0  0",
            &expect![[r#"
            [
                LxRoseTokenData::Nat32(
                    0,
                ),
                LxRoseTokenData::Nat32(
                    0,
                ),
            ]
        "#]],
        );
        t(
            "\\emph",
            &expect![[r#"
            [
                LxRoseTokenData::Command(
                    LxCommandName::LettersOnly(
                        LettersOnlyLxCommandName(
                            Coword(
                                "emph",
                            ),
                        ),
                    ),
                ),
            ]
        "#]],
        );
        t(
            "\\emph",
            &expect![[r#"
            [
                LxRoseTokenData::Command(
                    LxCommandName::LettersOnly(
                        LettersOnlyLxCommandName(
                            Coword(
                                "emph",
                            ),
                        ),
                    ),
                ),
            ]
        "#]],
        );
    }

    #[test]
    fn comment_works() {
        t(
            r#"%"#,
            &expect![[r#"
                []
            "#]],
        );
    }
}

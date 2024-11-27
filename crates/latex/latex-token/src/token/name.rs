use super::*;
use crate::idx::LxNameTokenIdx;
use coword::Coword;
use husky_text_protocol::{offset::TextOffsetRange, range::TextPositionRange};
use latex_command::path::LxCommandPath;
use latex_rose_punctuation::LxRosePunctuation;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxNameTokenData {
    Name(Coword),
    // Command(LxCommandPath),
}

impl<'a> LxLexer<'a> {
    pub fn next_name_token(&mut self) -> Option<(LxNameTokenIdx, LxNameTokenData)> {
        let (offset_range, range, token_data) = self.next_ranged_name_token_data()?;
        Some((
            self.alloc_name_token(offset_range, range, token_data),
            token_data,
        ))
    }

    fn next_ranged_name_token_data(
        &mut self,
    ) -> Option<(TextOffsetRange, TextPositionRange, LxNameTokenData)> {
        self.eat_spaces_and_tabs();
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
                self.next_word_token_data()
            }
        } else {
            self.next_word_token_data()
        }?;
        let end_offset = self.chars.current_offset();
        let range = TextPositionRange {
            start: start_position,
            end: self.chars.current_position(),
        };
        Some(((start_offset..end_offset).into(), range, token_data))
    }

    pub(crate) fn next_word_token_data(&mut self) -> Option<LxNameTokenData> {
        match self.chars.peek()? {
            '\\' => {
                todo!()
                // self.chars.eat_char();
                // match self.chars.peek() {
                //     Some(c) => match c {
                //         c if c.is_ascii_alphabetic() => Some(
                //             LxCommandPath::new_prelude(
                //                 self.next_coword_with(|c| c.is_ascii_alphabetic()).unwrap(),
                //                 db,
                //             )
                //             .into(),
                //         ),
                //         c if c.is_ascii_digit() => todo!("latex might allow single digit command"),
                //         _ => todo!("latex one digit non letter command"),
                //     },
                //     None => todo!(),
                // }
            }
            n if n.is_ascii_digit() => {
                todo!()
                // let numeric_str_slice = self.chars.next_numeric_str_slice();
                // match numeric_str_slice.parse::<u32>() {
                //     Ok(number) => Some(number.into()), // ad hoc
                //     Err(_) => todo!(),
                // }
            }
            a if a.is_ascii_alphabetic() => Some(
                Coword::from_ref(self.chars.next_str_slice_while(|c| c.is_ascii_alphabetic()))
                    .into(),
            ),
            c => {
                use husky_print_utils::p;

                p!(c);
                todo!()
            }
        }
    }
}

#[test]
#[ignore]
fn next_word_token_data_works() {
    fn t(input: &str, expected: &Expect) {
        use crate::lane::LxTokenLane;

        let mut storage = LxTokenStorage::default();
        let mut stream = LxLexer::new(input, LxTokenLane::Main, &mut storage)
            .into_word_stream()
            .map(|(_, token_data)| token_data);
        let mut tokens: Vec<_> = stream.collect();
        expected.assert_debug_eq(&tokens);
    }
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
                    LxCommandPath {
                        package: Prelude,
                        name: LxCommandName::LettersOnly(
                            LettersOnlyLxCommandName(
                                Coword(
                                    "emph",
                                ),
                            ),
                        ),
                    },
                ),
            ]
        "#]],
    );
    t(
        "\\emph",
        &expect![[r#"
            [
                LxRoseTokenData::Command(
                    LxCommandPath {
                        package: Prelude,
                        name: LxCommandName::LettersOnly(
                            LettersOnlyLxCommandName(
                                Coword(
                                    "emph",
                                ),
                            ),
                        ),
                    },
                ),
            ]
        "#]],
    );
}

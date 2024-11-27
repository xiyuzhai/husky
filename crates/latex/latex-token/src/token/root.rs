use super::*;
use crate::idx::LxRootTokenIdx;
use husky_text_protocol::{offset::TextOffsetRange, range::TextPositionRange};
use latex_command::path::LxCommandName;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxRootTokenData {
    Command(LxCommandName),
    LeftDelimiter(LxRootDelimiter),
    RightDelimiter(LxRootDelimiter),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxRootDelimiter {
    /// `{`,  `}`
    Curl,
    /// `[`, `]`
    Box,
}

impl<'a> LxLexer<'a> {
    pub fn next_root_token(&mut self) -> Option<(LxRootTokenIdx, LxRootTokenData)> {
        let (offset_range, range, token_data) = self.next_ranged_root_token()?;
        Some((
            self.alloc_root_token(offset_range, range, token_data),
            token_data,
        ))
    }

    fn next_ranged_root_token(
        &mut self,
    ) -> Option<(TextOffsetRange, TextPositionRange, LxRootTokenData)> {
        self.eat_spaces_and_tabs_and_lines_and_comments();
        let mut start_offset = self.chars.current_offset();
        let mut start_position = self.chars.current_position();
        let token_data = self.next_root_token_data()?;
        let end_offset = self.chars.current_offset();
        let range = TextPositionRange {
            start: start_position,
            end: self.chars.current_position(),
        };
        Some(((start_offset..end_offset).into(), range, token_data))
    }

    pub fn peek_root_token_data(&mut self) -> Option<LxRootTokenData> {
        let chars = self.chars.clone();
        let (_, _, token_data) = self.next_ranged_root_token()?;
        self.chars = chars;
        Some(token_data)
    }
    pub(crate) fn next_root_token_data(&mut self) -> Option<LxRootTokenData> {
        match self.chars.peek()? {
            '\\' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some(c) => match c {
                        c if c.is_ascii_alphabetic() => Some(LxRootTokenData::Command(
                            LxCommandName::new(
                                self.next_coword_with(|c| c.is_ascii_alphabetic()).unwrap(),
                            )
                            .unwrap(),
                        )),
                        c if c.is_ascii_digit() => todo!("latex might allow single digit command"),
                        _ => todo!("latex one digit non letter command"),
                    },
                    None => todo!(),
                }
            }
            '{' => {
                self.chars.eat_char();
                Some(LxRootTokenData::LeftDelimiter(LxRootDelimiter::Curl))
            }
            '}' => {
                self.chars.eat_char();
                Some(LxRootTokenData::RightDelimiter(LxRootDelimiter::Curl))
            }
            '[' => {
                self.chars.eat_char();
                Some(LxRootTokenData::LeftDelimiter(LxRootDelimiter::Box))
            }
            ']' => {
                self.chars.eat_char();
                Some(LxRootTokenData::RightDelimiter(LxRootDelimiter::Box))
            }
            c => todo!("c: {:?}", c),
        }
    }
}

#[test]
pub fn next_root_token_data_works() {
    fn t(input: &str, expected: &Expect) {
        use crate::lane::LxTokenLane;

        let mut storage = LxTokenStorage::default();
        let stream = LxLexer::new(input, LxTokenLane::Main, &mut storage)
            .into_root_stream()
            .map(|(_, token_data)| token_data);
        let tokens: Vec<_> = stream.collect();
        expected.assert_debug_eq(&tokens);
    }
    t(
        "\\usepackage",
        &expect![[r#"
            [
                Command(
                    LettersOnly(
                        LettersOnlyLxCommandName(
                            Coword(
                                "usepackage",
                            ),
                        ),
                    ),
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
}

#[test]
pub fn next_root_token_data_with_comments_works() {
    fn t(input_with_comments: &str, input_without_comments: &str) {
        fn f(input: &str) -> Vec<LxRootTokenData> {
            use crate::lane::LxTokenLane;

            let mut storage = LxTokenStorage::default();
            let stream = LxLexer::new(input, LxTokenLane::Main, &mut storage)
                .into_root_stream()
                .map(|(_, token_data)| token_data);
            stream.collect()
        }
        let tokens_with_comments = f(input_with_comments);
        let tokens_without_comments = f(input_without_comments);
        assert_eq!(tokens_with_comments, tokens_without_comments);
    }
    t(
        r#"% foo
\usepackage"#,
        r#"\usepackage"#,
    );
    t(
        r#"% foo
\usepackage"#,
        r#"\usepackage"#,
    );
}

use super::*;
use husky_coword::Coword;
use latex_command::path::LxCommandPath;
use latex_rose_punctuation::LxRosePunctuation;

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxRoseTokenData {
    Word(Coword),
    Command(LxCommandPath),
    /// `$`
    Dollar,
    /// `\(`
    EscapedLpar,
    /// `\[`
    EscapedLbox,
    Nat32(u32),
    NewParagraph,
    Punctuation(LxRosePunctuation),
}

impl<'a> LxLexer<'a> {
    pub(crate) fn next_rose_token_data(&mut self) -> Option<LxRoseTokenData> {
        let db = self.db;
        match self.chars.peek()? {
            '\\' => {
                self.chars.eat_char();
                match self.chars.peek() {
                    Some(c) => match c {
                        c if c.is_alphabetic() => Some(
                            LxCommandPath::new_prelude(
                                self.next_coword_with(|c| c.is_alphabetic()).unwrap(),
                                db,
                            )
                            .into(),
                        ),
                        c if c.is_numeric() => todo!("latex might allow single digit command"),
                        _ => todo!("latex one digit non letter command"),
                    },
                    None => todo!(),
                }
            }
            n if n.is_numeric() => {
                let numeric_str_slice = self.chars.next_numeric_str_slice();
                match numeric_str_slice.parse::<u32>() {
                    Ok(number) => Some(number.into()), // ad hoc
                    Err(_) => todo!(),
                }
            }
            a if a.is_alphabetic() => Some(
                Coword::from_ref(
                    self.db,
                    self.chars.next_str_slice_while(|c| c.is_alphabetic()),
                )
                .into(),
            ),
            '$' => {
                self.chars.eat_char();
                Some(LxRoseTokenData::Dollar)
            }
            c if let Some(punctuation) = LxRosePunctuation::try_from_char(c) => {
                self.chars.eat_char();
                Some(LxRoseTokenData::Punctuation(punctuation))
            }
            c => {
                use husky_print_utils::p;

                p!(c);
                todo!()
            }
        }
    }
}

#[test]
fn next_text_token_data_works() {
    fn t(input: &str, expected: &Expect) {
        let db = &DB::default();
        let mut storage = LxTokenStorage::default();
        let mut stream = LxLexer::new(db, input, &mut storage)
            .into_rose_stream()
            .map(|(_, token_data)| token_data);
        let mut tokens: Vec<_> = stream.collect();
        expected.assert_debug_eq(&(tokens.debug(db)));
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

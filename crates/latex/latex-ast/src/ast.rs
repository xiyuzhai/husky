pub mod math;
pub mod rose;
#[cfg(test)]
pub mod tests;

use self::{
    math::{LxMathAstArena, LxMathAstArenaMap, LxMathAstArenaRef, LxMathAstData},
    rose::{LxRoseAstArena, LxRoseAstArenaMap, LxRoseAstArenaRef, LxRoseAstData},
};
use crate::parser::LxAstParser;
#[cfg(test)]
use crate::*;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use latex_command::{
    path::menu::{command_path_menu, LxCommandPathMenu},
    signature::table::LxCommandSignatureTable,
};
use latex_environment::signature::table::LxEnvironmentSignatureTable;
use latex_math_letter::letter::LxMathLetter;
use latex_math_punctuation::LxMathPunctuation;
use latex_prelude::{mode::LxMode, script::LxScriptKind};
use latex_token::{
    data::{
        math::{LxMathDelimiter, LxMathTokenData},
        rose::LxRoseTokenData,
    },
    storage::LxTokenStorage,
};
use math::{LxMathAstIdx, LxMathAstIdxRange};
use rose::{LxRoseAstIdx, LxRoseAstIdxRange};

#[enum_class::from_variants]
#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LxAstData {
    Math(LxMathAstData),
    Rose(LxRoseAstData),
}

#[salsa::derive_debug_with_db]
#[derive(Default, Debug)]
pub struct LxAstArena {
    pub(crate) math: LxMathAstArena,
    pub(crate) rose: LxRoseAstArena,
}
impl LxAstArena {
    pub fn as_arena_ref(&self) -> LxAstArenaRef {
        LxAstArenaRef {
            math: self.math.as_arena_ref(),
            rose: self.rose.as_arena_ref(),
        }
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LxAstArenaRef<'a> {
    math: LxMathAstArenaRef<'a>,
    rose: LxRoseAstArenaRef<'a>,
}

impl<'a> std::ops::Index<LxMathAstIdx> for LxAstArenaRef<'a> {
    type Output = LxMathAstData;

    fn index(&self, index: LxMathAstIdx) -> &Self::Output {
        &self.math[index]
    }
}

impl<'a> std::ops::Index<LxRoseAstIdx> for LxAstArenaRef<'a> {
    type Output = LxRoseAstData;

    fn index(&self, index: LxRoseAstIdx) -> &Self::Output {
        &self.rose[index]
    }
}

impl<'a> LxAstArenaRef<'a> {
    pub fn math(&self) -> LxMathAstArenaRef<'a> {
        self.math
    }

    pub fn rose(&self) -> LxRoseAstArenaRef<'a> {
        self.rose
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct LxAstArenaMap<T> {
    pub(crate) math: LxMathAstArenaMap<T>,
    pub(crate) rose: LxRoseAstArenaMap<T>,
}

impl<T> LxAstArenaMap<T> {
    pub(crate) fn new(arena: &LxAstArena) -> Self {
        Self {
            math: LxMathAstArenaMap::new(&arena.math),
            rose: LxRoseAstArenaMap::new(&arena.rose),
        }
    }
}

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxAstIdx {
    Math(LxMathAstIdx),
    Rose(LxRoseAstIdx),
}

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxAstIdxRange {
    Math(LxMathAstIdxRange),
    Rose(LxRoseAstIdxRange),
}

pub fn parse_latex_input_into_asts<'a>(
    db: &'a ::salsa::Db,
    command_signature_table: &'a LxCommandSignatureTable,
    environment_signature_table: &'a LxEnvironmentSignatureTable,
    input: &'a str,
    mode: LxMode,
    token_storage: &'a mut LxTokenStorage,
    arena: &'a mut LxAstArena,
) -> LxAstIdxRange {
    let mut parser = LxAstParser::new(
        db,
        command_signature_table,
        environment_signature_table,
        input,
        mode,
        token_storage,
        arena,
    );
    parser.parse_asts()
}

impl<'a> LxAstParser<'a> {
    pub(crate) fn parse_asts(&mut self) -> LxAstIdxRange {
        match self.mode() {
            LxMode::Rose => self.parse_rose_asts().into(),
            LxMode::Math => self.parse_math_asts().into(),
        }
    }
}

// TODO replace it with example
#[test]
fn parse_tex_input_into_asts_works() {
    use expect_test::Expect;

    fn t(input: &str, mode: LxMode, expected: Expect) {
        let db = &DB::default();
        let mut arena = LxAstArena::default();
        let mut token_storage = LxTokenStorage::default();
        let command_signature_table = &LxCommandSignatureTable::new_default(db);
        let environment_signature_table = &LxEnvironmentSignatureTable::new_default(db);
        let asts = parse_latex_input_into_asts(
            db,
            command_signature_table,
            environment_signature_table,
            input,
            mode,
            &mut token_storage,
            &mut arena,
        );
        expected.assert_debug_eq(&((token_storage, arena, asts).debug(db)));
    }
    t(
        "",
        LxMode::Math,
        expect![[r#"
            (
                LxTokenStorage {
                    ranged_tokens: [],
                },
                LxAstArena {
                    math: Arena {
                        data: [],
                    },
                    rose: Arena {
                        data: [],
                    },
                },
                LxAstIdxRange::Math(
                    ArenaIdxRange(
                        0..0,
                    ),
                ),
            )
        "#]],
    );
    t(
        "1",
        LxMode::Math,
        expect![[r#"
            (
                LxTokenStorage {
                    ranged_tokens: [
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    0,
                                ),
                                end: TextOffset(
                                    1,
                                ),
                            },
                            [1:1, 1:2),
                            Math(
                                Digit(
                                    One,
                                ),
                            ),
                        ),
                    ],
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            LxMathAstData::Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        0,
                                    ),
                                ),
                                One,
                            ),
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                },
                LxAstIdxRange::Math(
                    ArenaIdxRange(
                        0..1,
                    ),
                ),
            )
        "#]],
    );
    t(
        "x",
        LxMode::Math,
        expect![[r#"
            (
                LxTokenStorage {
                    ranged_tokens: [
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    0,
                                ),
                                end: TextOffset(
                                    1,
                                ),
                            },
                            [1:1, 1:2),
                            Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        ),
                    ],
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            LxMathAstData::PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                },
                LxAstIdxRange::Math(
                    ArenaIdxRange(
                        0..1,
                    ),
                ),
            )
        "#]],
    );
    t(
        "x+1",
        LxMode::Math,
        expect![[r#"
            (
                LxTokenStorage {
                    ranged_tokens: [
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    0,
                                ),
                                end: TextOffset(
                                    1,
                                ),
                            },
                            [1:1, 1:2),
                            Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    1,
                                ),
                                end: TextOffset(
                                    2,
                                ),
                            },
                            [1:2, 1:3),
                            Math(
                                Punctuation(
                                    Add,
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    2,
                                ),
                                end: TextOffset(
                                    3,
                                ),
                            },
                            [1:3, 1:4),
                            Math(
                                Digit(
                                    One,
                                ),
                            ),
                        ),
                    ],
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            LxMathAstData::PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                            LxMathAstData::Punctuation(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        1,
                                    ),
                                ),
                                Add,
                            ),
                            LxMathAstData::Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        2,
                                    ),
                                ),
                                One,
                            ),
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                },
                LxAstIdxRange::Math(
                    ArenaIdxRange(
                        0..3,
                    ),
                ),
            )
        "#]],
    );
    t(
        "x^2",
        LxMode::Math,
        expect![[r#"
            (
                LxTokenStorage {
                    ranged_tokens: [
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    0,
                                ),
                                end: TextOffset(
                                    1,
                                ),
                            },
                            [1:1, 1:2),
                            Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    1,
                                ),
                                end: TextOffset(
                                    2,
                                ),
                            },
                            [1:2, 1:3),
                            Math(
                                Superscript,
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    2,
                                ),
                                end: TextOffset(
                                    3,
                                ),
                            },
                            [1:3, 1:4),
                            Math(
                                Digit(
                                    Two,
                                ),
                            ),
                        ),
                    ],
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            LxMathAstData::PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                            LxMathAstData::Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        2,
                                    ),
                                ),
                                Two,
                            ),
                            LxMathAstData::Attach {
                                base: 0,
                                scripts: [
                                    (
                                        LxScriptKind::Superscript,
                                        1,
                                    ),
                                ],
                            },
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                },
                LxAstIdxRange::Math(
                    ArenaIdxRange(
                        2..3,
                    ),
                ),
            )
        "#]],
    );
    t(
        "x_2",
        LxMode::Math,
        expect![[r#"
            (
                LxTokenStorage {
                    ranged_tokens: [
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    0,
                                ),
                                end: TextOffset(
                                    1,
                                ),
                            },
                            [1:1, 1:2),
                            Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    1,
                                ),
                                end: TextOffset(
                                    2,
                                ),
                            },
                            [1:2, 1:3),
                            Math(
                                Subscript,
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    2,
                                ),
                                end: TextOffset(
                                    3,
                                ),
                            },
                            [1:3, 1:4),
                            Math(
                                Digit(
                                    Two,
                                ),
                            ),
                        ),
                    ],
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            LxMathAstData::PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                            LxMathAstData::Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        2,
                                    ),
                                ),
                                Two,
                            ),
                            LxMathAstData::Attach {
                                base: 0,
                                scripts: [
                                    (
                                        LxScriptKind::Subscript,
                                        1,
                                    ),
                                ],
                            },
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                },
                LxAstIdxRange::Math(
                    ArenaIdxRange(
                        2..3,
                    ),
                ),
            )
        "#]],
    );
    t(
        "x^{i+2}",
        LxMode::Math,
        expect![[r#"
            (
                LxTokenStorage {
                    ranged_tokens: [
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    0,
                                ),
                                end: TextOffset(
                                    1,
                                ),
                            },
                            [1:1, 1:2),
                            Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    1,
                                ),
                                end: TextOffset(
                                    2,
                                ),
                            },
                            [1:2, 1:3),
                            Math(
                                Superscript,
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    2,
                                ),
                                end: TextOffset(
                                    3,
                                ),
                            },
                            [1:3, 1:4),
                            Math(
                                LeftDelimiter(
                                    Curl,
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    3,
                                ),
                                end: TextOffset(
                                    4,
                                ),
                            },
                            [1:4, 1:5),
                            Math(
                                Letter(
                                    LowerLatin(
                                        I,
                                    ),
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    4,
                                ),
                                end: TextOffset(
                                    5,
                                ),
                            },
                            [1:5, 1:6),
                            Math(
                                Punctuation(
                                    Add,
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    5,
                                ),
                                end: TextOffset(
                                    6,
                                ),
                            },
                            [1:6, 1:7),
                            Math(
                                Digit(
                                    Two,
                                ),
                            ),
                        ),
                        (
                            TextOffsetRange {
                                start: TextOffset(
                                    6,
                                ),
                                end: TextOffset(
                                    7,
                                ),
                            },
                            [1:7, 1:8),
                            Math(
                                RightDelimiter(
                                    Curl,
                                ),
                            ),
                        ),
                    ],
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            LxMathAstData::PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                            LxMathAstData::PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        3,
                                    ),
                                ),
                                LowerLatin(
                                    I,
                                ),
                            ),
                            LxMathAstData::Punctuation(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        4,
                                    ),
                                ),
                                Add,
                            ),
                            LxMathAstData::Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        5,
                                    ),
                                ),
                                Two,
                            ),
                            LxMathAstData::Delimited {
                                left_delimiter_token_idx: LxMathTokenIdx(
                                    LxTokenIdx(
                                        2,
                                    ),
                                ),
                                left_delimiter: Curl,
                                asts: ArenaIdxRange(
                                    1..4,
                                ),
                                right_delimiter_token_idx: LxMathTokenIdx(
                                    LxTokenIdx(
                                        6,
                                    ),
                                ),
                                right_delimiter: Curl,
                            },
                            LxMathAstData::Attach {
                                base: 0,
                                scripts: [
                                    (
                                        LxScriptKind::Superscript,
                                        4,
                                    ),
                                ],
                            },
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                },
                LxAstIdxRange::Math(
                    ArenaIdxRange(
                        5..6,
                    ),
                ),
            )
        "#]],
    );
}

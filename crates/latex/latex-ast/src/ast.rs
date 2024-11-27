pub mod lisp;
pub mod math;
pub mod root;
pub mod rose;
pub mod spec;
#[cfg(test)]
pub mod tests;

use self::{
    lisp::{
        LxLispAstArena, LxLispAstArenaMap, LxLispAstArenaRef, LxLispAstData, LxLispAstIdx,
        LxLispAstIdxRange,
    },
    math::{
        LxMathAstArena, LxMathAstArenaMap, LxMathAstArenaRef, LxMathAstData, LxMathAstIdx,
        LxMathAstIdxRange,
    },
    root::{
        LxRootAstArena, LxRootAstArenaMap, LxRootAstArenaRef, LxRootAstData, LxRootAstIdx,
        LxRootAstIdxRange,
    },
    rose::{
        LxRoseAstArena, LxRoseAstArenaMap, LxRoseAstArenaRef, LxRoseAstData, LxRoseAstIdx,
        LxRoseAstIdxRange,
    },
};
use crate::parser::LxAstParser;
#[cfg(test)]
use crate::*;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use latex_command::{path::menu::LxCommandPathMenu, signature::table::LxCommandSignatureTable};
use latex_environment::signature::table::LxEnvironmentSignatureTable;
use latex_math_letter::letter::LxMathLetter;
use latex_math_punctuation::LxMathPunctuation;
use latex_prelude::{mode::LxMode, script::LxScriptKind};
use latex_token::{
    lane::LxTokenLane,
    storage::LxTokenStorage,
    token::{
        math::{LxMathDelimiter, LxMathTokenData},
        rose::LxRoseTokenData,
    },
};

#[enum_class::from_variants]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LxAstData {
    Math(LxMathAstData),
    Rose(LxRoseAstData),
}

#[derive(Default, Debug)]
pub struct LxAstArena {
    pub(crate) math: LxMathAstArena,
    pub(crate) rose: LxRoseAstArena,
    pub(crate) lisp: LxLispAstArena,
    pub(crate) root: LxRootAstArena,
}
impl LxAstArena {
    pub fn as_arena_ref(&self) -> LxAstArenaRef {
        LxAstArenaRef {
            math: self.math.as_arena_ref(),
            rose: self.rose.as_arena_ref(),
            lisp: self.lisp.as_arena_ref(),
            root: self.root.as_arena_ref(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LxAstArenaRef<'a> {
    math: LxMathAstArenaRef<'a>,
    rose: LxRoseAstArenaRef<'a>,
    lisp: LxLispAstArenaRef<'a>,
    root: LxRootAstArenaRef<'a>,
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

    pub fn lisp(&self) -> LxLispAstArenaRef<'a> {
        self.lisp
    }

    pub fn root(&self) -> LxRootAstArenaRef<'a> {
        self.root
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct LxAstArenaMap<T> {
    pub(crate) math: LxMathAstArenaMap<T>,
    pub(crate) rose: LxRoseAstArenaMap<T>,
    pub(crate) lisp: LxLispAstArenaMap<T>,
    pub(crate) root: LxRootAstArenaMap<T>,
}

impl<T> LxAstArenaMap<T> {
    pub(crate) fn new(arena: &LxAstArena) -> Self {
        Self {
            math: LxMathAstArenaMap::new(&arena.math),
            rose: LxRoseAstArenaMap::new(&arena.rose),
            lisp: LxLispAstArenaMap::new(&arena.lisp),
            root: LxRootAstArenaMap::new(&arena.root),
        }
    }
}

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxAstIdx {
    Math(LxMathAstIdx),
    Rose(LxRoseAstIdx),
    Lisp(LxLispAstIdx),
    Root(LxRootAstIdx),
}

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxAstIdxRange {
    Math(LxMathAstIdxRange),
    Root(LxRootAstIdxRange),
    Rose(LxRoseAstIdxRange),
    Lisp(LxLispAstIdxRange),
}

pub fn parse_latex_input_into_asts<'a>(
    command_signature_table: &'a LxCommandSignatureTable,
    environment_signature_table: &'a LxEnvironmentSignatureTable,
    input: &'a str,
    lane: LxTokenLane,
    mode: LxMode,
    token_storage: &'a mut LxTokenStorage,
    arena: &'a mut LxAstArena,
) -> LxAstIdxRange {
    let mut parser = LxAstParser::new(
        command_signature_table,
        environment_signature_table,
        input,
        lane,
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
            LxMode::Name => todo!(),
            LxMode::Lisp => self.parse_lisp_asts().into(),
            LxMode::Root => self.parse_root_asts().into(),
        }
    }
}

// TODO replace it with example
#[test]
fn parse_tex_input_into_asts_works() {
    use expect_test::Expect;

    fn t(input: &str, mode: LxMode, expected: Expect) {
        use husky_path_utils::HuskyLangDevPaths;

        let dev_paths = HuskyLangDevPaths::new();
        let complete_commands_path = &dev_paths.specs_dir().join("latex/complete-commands.lpcsv");
        let mut arena = LxAstArena::default();
        let mut token_storage = LxTokenStorage::default();
        let command_signature_table =
            &LxCommandSignatureTable::new_from_lp_csv_file_paths(complete_commands_path);
        let environment_signature_table = &LxEnvironmentSignatureTable::new_default();
        let asts = parse_latex_input_into_asts(
            command_signature_table,
            environment_signature_table,
            input,
            LxTokenLane::Main,
            mode,
            &mut token_storage,
            &mut arena,
        );
        expected.assert_debug_eq(&(token_storage, arena, asts));
    }
    t(
        "",
        LxMode::Math,
        expect![[r#"
            (
                LxTokenStorage {
                    main_ranged_tokens: [],
                    annotation_ranged_tokens: {},
                },
                LxAstArena {
                    math: Arena {
                        data: [],
                    },
                    rose: Arena {
                        data: [],
                    },
                    lisp: Arena {
                        data: [],
                    },
                    root: Arena {
                        data: [],
                    },
                },
                Math(
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
                    main_ranged_tokens: [
                        LxTokenEntry {
                            text_offset_range: 0..1,
                            text_range: [1:1, 1:2),
                            data: Math(
                                Digit(
                                    One,
                                ),
                            ),
                        },
                    ],
                    annotation_ranged_tokens: {},
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
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
                    lisp: Arena {
                        data: [],
                    },
                    root: Arena {
                        data: [],
                    },
                },
                Math(
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
                    main_ranged_tokens: [
                        LxTokenEntry {
                            text_offset_range: 0..1,
                            text_range: [1:1, 1:2),
                            data: Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        },
                    ],
                    annotation_ranged_tokens: {},
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
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
                    lisp: Arena {
                        data: [],
                    },
                    root: Arena {
                        data: [],
                    },
                },
                Math(
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
                    main_ranged_tokens: [
                        LxTokenEntry {
                            text_offset_range: 0..1,
                            text_range: [1:1, 1:2),
                            data: Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 1..2,
                            text_range: [1:2, 1:3),
                            data: Math(
                                Punctuation(
                                    Add,
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 2..3,
                            text_range: [1:3, 1:4),
                            data: Math(
                                Digit(
                                    One,
                                ),
                            ),
                        },
                    ],
                    annotation_ranged_tokens: {},
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                            Punctuation(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        1,
                                    ),
                                ),
                                Add,
                            ),
                            Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
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
                    lisp: Arena {
                        data: [],
                    },
                    root: Arena {
                        data: [],
                    },
                },
                Math(
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
                    main_ranged_tokens: [
                        LxTokenEntry {
                            text_offset_range: 0..1,
                            text_range: [1:1, 1:2),
                            data: Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 1..2,
                            text_range: [1:2, 1:3),
                            data: Math(
                                Superscript,
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 2..3,
                            text_range: [1:3, 1:4),
                            data: Math(
                                Digit(
                                    Two,
                                ),
                            ),
                        },
                    ],
                    annotation_ranged_tokens: {},
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                            Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        2,
                                    ),
                                ),
                                Two,
                            ),
                            Attach {
                                base: 0,
                                scripts: [
                                    (
                                        Superscript,
                                        1,
                                    ),
                                ],
                            },
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                    lisp: Arena {
                        data: [],
                    },
                    root: Arena {
                        data: [],
                    },
                },
                Math(
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
                    main_ranged_tokens: [
                        LxTokenEntry {
                            text_offset_range: 0..1,
                            text_range: [1:1, 1:2),
                            data: Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 1..2,
                            text_range: [1:2, 1:3),
                            data: Math(
                                Subscript,
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 2..3,
                            text_range: [1:3, 1:4),
                            data: Math(
                                Digit(
                                    Two,
                                ),
                            ),
                        },
                    ],
                    annotation_ranged_tokens: {},
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                            Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        2,
                                    ),
                                ),
                                Two,
                            ),
                            Attach {
                                base: 0,
                                scripts: [
                                    (
                                        Subscript,
                                        1,
                                    ),
                                ],
                            },
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                    lisp: Arena {
                        data: [],
                    },
                    root: Arena {
                        data: [],
                    },
                },
                Math(
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
                    main_ranged_tokens: [
                        LxTokenEntry {
                            text_offset_range: 0..1,
                            text_range: [1:1, 1:2),
                            data: Math(
                                Letter(
                                    LowerLatin(
                                        X,
                                    ),
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 1..2,
                            text_range: [1:2, 1:3),
                            data: Math(
                                Superscript,
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 2..3,
                            text_range: [1:3, 1:4),
                            data: Math(
                                LeftDelimiter(
                                    Curl,
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 3..4,
                            text_range: [1:4, 1:5),
                            data: Math(
                                Letter(
                                    LowerLatin(
                                        I,
                                    ),
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 4..5,
                            text_range: [1:5, 1:6),
                            data: Math(
                                Punctuation(
                                    Add,
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 5..6,
                            text_range: [1:6, 1:7),
                            data: Math(
                                Digit(
                                    Two,
                                ),
                            ),
                        },
                        LxTokenEntry {
                            text_offset_range: 6..7,
                            text_range: [1:7, 1:8),
                            data: Math(
                                RightDelimiter(
                                    Curl,
                                ),
                            ),
                        },
                    ],
                    annotation_ranged_tokens: {},
                },
                LxAstArena {
                    math: Arena {
                        data: [
                            PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        0,
                                    ),
                                ),
                                LowerLatin(
                                    X,
                                ),
                            ),
                            PlainLetter(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        3,
                                    ),
                                ),
                                LowerLatin(
                                    I,
                                ),
                            ),
                            Punctuation(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        4,
                                    ),
                                ),
                                Add,
                            ),
                            Digit(
                                LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        5,
                                    ),
                                ),
                                Two,
                            ),
                            Delimited {
                                left_delimiter_token_idx: LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        2,
                                    ),
                                ),
                                left_delimiter: Curl,
                                asts: ArenaIdxRange(
                                    1..4,
                                ),
                                right_delimiter_token_idx: LxMathTokenIdx(
                                    LxTokenIdx(
                                        Main,
                                        6,
                                    ),
                                ),
                                right_delimiter: Curl,
                            },
                            Attach {
                                base: 0,
                                scripts: [
                                    (
                                        Superscript,
                                        4,
                                    ),
                                ],
                            },
                        ],
                    },
                    rose: Arena {
                        data: [],
                    },
                    lisp: Arena {
                        data: [],
                    },
                    root: Arena {
                        data: [],
                    },
                },
                Math(
                    ArenaIdxRange(
                        5..6,
                    ),
                ),
            )
        "#]],
    );
}

use crate::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LpCsvFile {
    input: String,
    data: LpCsvFileData,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LpCsvFileData {
    Rows(Vec<LpCsvRow>),
}

impl LpCsvFile {
    pub fn input(&self) -> &str {
        &self.input
    }

    pub fn data(&self) -> &LpCsvFileData {
        &self.data
    }
}

impl<'a> LpCsvParser<'a> {
    pub(crate) fn parse_file(mut self) -> LpCsvResult<LpCsvFile> {
        let mut rows = Vec::new();
        while let Some(row) = self.parse_row().into_result_option()? {
            rows.push(row);
        }
        Ok(LpCsvFile {
            input: self.input.to_string(),
            data: LpCsvFileData::Rows(rows),
        })
    }
}

#[test]
fn parse_lp_csv_file_works() {
    fn t(input: &str, expected: Expect) {
        let mut parser = LpCsvParser::new(input);
        let file = parser.parse_file().unwrap();
        expected.assert_debug_eq(&file);
    }
    t(
        "1,2",
        expect![[r#"
            LpCsvFile {
                input: "1,2",
                data: Rows(
                    [
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Literal(
                                        Integer(
                                            1,
                                        ),
                                    ),
                                    offset_range: 0..1,
                                    position_range: [1:1, 1:2),
                                },
                                LpCsvExpr {
                                    data: Literal(
                                        Integer(
                                            2,
                                        ),
                                    ),
                                    offset_range: 2..3,
                                    position_range: [1:3, 1:4),
                                },
                            ],
                        ),
                    ],
                ),
            }
        "#]],
    );
    t(
        r#"mathbb,1,2
mathcal,1,2"#,
        expect![[r#"
            LpCsvFile {
                input: "mathbb,1,2\nmathcal,1,2",
                data: Rows(
                    [
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "mathbb",
                                    ),
                                    offset_range: 0..6,
                                    position_range: [1:1, 1:7),
                                },
                                LpCsvExpr {
                                    data: Literal(
                                        Integer(
                                            1,
                                        ),
                                    ),
                                    offset_range: 7..8,
                                    position_range: [1:8, 1:9),
                                },
                                LpCsvExpr {
                                    data: Literal(
                                        Integer(
                                            2,
                                        ),
                                    ),
                                    offset_range: 9..10,
                                    position_range: [1:10, 1:11),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "mathcal",
                                    ),
                                    offset_range: 11..18,
                                    position_range: [2:1, 2:8),
                                },
                                LpCsvExpr {
                                    data: Literal(
                                        Integer(
                                            1,
                                        ),
                                    ),
                                    offset_range: 19..20,
                                    position_range: [2:9, 2:10),
                                },
                                LpCsvExpr {
                                    data: Literal(
                                        Integer(
                                            2,
                                        ),
                                    ),
                                    offset_range: 21..22,
                                    position_range: [2:11, 2:12),
                                },
                            ],
                        ),
                    ],
                ),
            }
        "#]],
    );
    t(
        r#"
//! format:
//! <instance-ident> = <instantiation>, <signature-data-variant-path> <arg0> <arg1> ...
//! <instantiation> = <item-path> <arg0> <arg1> ...
# instances of lisp-csv

## prefix operators
### pos
int_pos = ring_pos int, base_prefix_opr int int
rat_pos = ring_pos rat, base_prefix_opr rat rat
real_pos = ring_pos real, base_prefix_opr real real
complex_pos = ring_pos complex, base_prefix_opr complex complex
"#,
        expect![[r#"
            LpCsvFile {
                input: "\n//! format:\n//! <instance-ident> = <instantiation>, <signature-data-variant-path> <arg0> <arg1> ...\n//! <instantiation> = <item-path> <arg0> <arg1> ...\n# instances of lisp-csv\n\n## prefix operators\n### pos\nint_pos = ring_pos int, base_prefix_opr int int\nrat_pos = ring_pos rat, base_prefix_opr rat rat\nreal_pos = ring_pos real, base_prefix_opr real real\ncomplex_pos = ring_pos complex, base_prefix_opr complex complex\n",
                data: Rows(
                    [
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "int_pos",
                                    ),
                                    offset_range: 206..213,
                                    position_range: [9:1, 9:8),
                                },
                                LpCsvExpr {
                                    data: Application(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "ring_pos",
                                                ),
                                                offset_range: 216..224,
                                                position_range: [9:11, 9:19),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "int",
                                                ),
                                                offset_range: 225..228,
                                                position_range: [9:20, 9:23),
                                            },
                                        ],
                                    ),
                                    offset_range: 216..228,
                                    position_range: [9:11, 9:23),
                                },
                                LpCsvExpr {
                                    data: Application(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "base_prefix_opr",
                                                ),
                                                offset_range: 230..245,
                                                position_range: [9:25, 9:40),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "int",
                                                ),
                                                offset_range: 246..249,
                                                position_range: [9:41, 9:44),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "int",
                                                ),
                                                offset_range: 250..253,
                                                position_range: [9:45, 9:48),
                                            },
                                        ],
                                    ),
                                    offset_range: 230..253,
                                    position_range: [9:25, 9:48),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "rat_pos",
                                    ),
                                    offset_range: 254..261,
                                    position_range: [10:1, 10:8),
                                },
                                LpCsvExpr {
                                    data: Application(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "ring_pos",
                                                ),
                                                offset_range: 264..272,
                                                position_range: [10:11, 10:19),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "rat",
                                                ),
                                                offset_range: 273..276,
                                                position_range: [10:20, 10:23),
                                            },
                                        ],
                                    ),
                                    offset_range: 264..276,
                                    position_range: [10:11, 10:23),
                                },
                                LpCsvExpr {
                                    data: Application(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "base_prefix_opr",
                                                ),
                                                offset_range: 278..293,
                                                position_range: [10:25, 10:40),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "rat",
                                                ),
                                                offset_range: 294..297,
                                                position_range: [10:41, 10:44),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "rat",
                                                ),
                                                offset_range: 298..301,
                                                position_range: [10:45, 10:48),
                                            },
                                        ],
                                    ),
                                    offset_range: 278..301,
                                    position_range: [10:25, 10:48),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "real_pos",
                                    ),
                                    offset_range: 302..310,
                                    position_range: [11:1, 11:9),
                                },
                                LpCsvExpr {
                                    data: Application(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "ring_pos",
                                                ),
                                                offset_range: 313..321,
                                                position_range: [11:12, 11:20),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "real",
                                                ),
                                                offset_range: 322..326,
                                                position_range: [11:21, 11:25),
                                            },
                                        ],
                                    ),
                                    offset_range: 313..326,
                                    position_range: [11:12, 11:25),
                                },
                                LpCsvExpr {
                                    data: Application(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "base_prefix_opr",
                                                ),
                                                offset_range: 328..343,
                                                position_range: [11:27, 11:42),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "real",
                                                ),
                                                offset_range: 344..348,
                                                position_range: [11:43, 11:47),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "real",
                                                ),
                                                offset_range: 349..353,
                                                position_range: [11:48, 11:52),
                                            },
                                        ],
                                    ),
                                    offset_range: 328..353,
                                    position_range: [11:27, 11:52),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "complex_pos",
                                    ),
                                    offset_range: 354..365,
                                    position_range: [12:1, 12:12),
                                },
                                LpCsvExpr {
                                    data: Application(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "ring_pos",
                                                ),
                                                offset_range: 368..376,
                                                position_range: [12:15, 12:23),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "complex",
                                                ),
                                                offset_range: 377..384,
                                                position_range: [12:24, 12:31),
                                            },
                                        ],
                                    ),
                                    offset_range: 368..384,
                                    position_range: [12:15, 12:31),
                                },
                                LpCsvExpr {
                                    data: Application(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "base_prefix_opr",
                                                ),
                                                offset_range: 386..401,
                                                position_range: [12:33, 12:48),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "complex",
                                                ),
                                                offset_range: 402..409,
                                                position_range: [12:49, 12:56),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "complex",
                                                ),
                                                offset_range: 410..417,
                                                position_range: [12:57, 12:64),
                                            },
                                        ],
                                    ),
                                    offset_range: 386..417,
                                    position_range: [12:33, 12:64),
                                },
                            ],
                        ),
                    ],
                ),
            }
        "#]],
    );
    t(
        r#"
//! Format:
//!
//! <command-ident>, [<allowed-modes>,...], [<parameter-modes>,...]
// - root
usepackage, [root], [name]
documentclass, [root], [name]
newtheorem, [root], [name, name]
// - divisions
part, [root], [rose]
chapter, [root], [rose]
section, [root], [rose]
subsection, [root], [rose]
subsubsection, [root], [rose]
// - operators
// -- relations
eq, [math], []
ne, [math], []
le, [math], []
ge, [math], []
"#,
        expect![[r#"
            LpCsvFile {
                input: "\n//! Format:\n//!\n//! <command-ident>, [<allowed-modes>,...], [<parameter-modes>,...]\n// - root\nusepackage, [root], [name]\ndocumentclass, [root], [name]\nnewtheorem, [root], [name, name]\n// - divisions\npart, [root], [rose]\nchapter, [root], [rose]\nsection, [root], [rose]\nsubsection, [root], [rose]\nsubsubsection, [root], [rose]\n// - operators\n// -- relations\neq, [math], []\nne, [math], []\nle, [math], []\nge, [math], []\n",
                data: Rows(
                    [
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "usepackage",
                                    ),
                                    offset_range: 95..105,
                                    position_range: [6:1, 6:11),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "root",
                                                ),
                                                offset_range: 108..112,
                                                position_range: [6:14, 6:18),
                                            },
                                        ],
                                    ),
                                    offset_range: 107..113,
                                    position_range: [6:13, 6:19),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "name",
                                                ),
                                                offset_range: 116..120,
                                                position_range: [6:22, 6:26),
                                            },
                                        ],
                                    ),
                                    offset_range: 115..121,
                                    position_range: [6:21, 6:27),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "documentclass",
                                    ),
                                    offset_range: 122..135,
                                    position_range: [7:1, 7:14),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "root",
                                                ),
                                                offset_range: 138..142,
                                                position_range: [7:17, 7:21),
                                            },
                                        ],
                                    ),
                                    offset_range: 137..143,
                                    position_range: [7:16, 7:22),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "name",
                                                ),
                                                offset_range: 146..150,
                                                position_range: [7:25, 7:29),
                                            },
                                        ],
                                    ),
                                    offset_range: 145..151,
                                    position_range: [7:24, 7:30),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "newtheorem",
                                    ),
                                    offset_range: 152..162,
                                    position_range: [8:1, 8:11),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "root",
                                                ),
                                                offset_range: 165..169,
                                                position_range: [8:14, 8:18),
                                            },
                                        ],
                                    ),
                                    offset_range: 164..170,
                                    position_range: [8:13, 8:19),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "name",
                                                ),
                                                offset_range: 173..177,
                                                position_range: [8:22, 8:26),
                                            },
                                            LpCsvExpr {
                                                data: Ident(
                                                    "name",
                                                ),
                                                offset_range: 179..183,
                                                position_range: [8:28, 8:32),
                                            },
                                        ],
                                    ),
                                    offset_range: 172..184,
                                    position_range: [8:21, 8:33),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "part",
                                    ),
                                    offset_range: 200..204,
                                    position_range: [10:1, 10:5),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "root",
                                                ),
                                                offset_range: 207..211,
                                                position_range: [10:8, 10:12),
                                            },
                                        ],
                                    ),
                                    offset_range: 206..212,
                                    position_range: [10:7, 10:13),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "rose",
                                                ),
                                                offset_range: 215..219,
                                                position_range: [10:16, 10:20),
                                            },
                                        ],
                                    ),
                                    offset_range: 214..220,
                                    position_range: [10:15, 10:21),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "chapter",
                                    ),
                                    offset_range: 221..228,
                                    position_range: [11:1, 11:8),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "root",
                                                ),
                                                offset_range: 231..235,
                                                position_range: [11:11, 11:15),
                                            },
                                        ],
                                    ),
                                    offset_range: 230..236,
                                    position_range: [11:10, 11:16),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "rose",
                                                ),
                                                offset_range: 239..243,
                                                position_range: [11:19, 11:23),
                                            },
                                        ],
                                    ),
                                    offset_range: 238..244,
                                    position_range: [11:18, 11:24),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "section",
                                    ),
                                    offset_range: 245..252,
                                    position_range: [12:1, 12:8),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "root",
                                                ),
                                                offset_range: 255..259,
                                                position_range: [12:11, 12:15),
                                            },
                                        ],
                                    ),
                                    offset_range: 254..260,
                                    position_range: [12:10, 12:16),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "rose",
                                                ),
                                                offset_range: 263..267,
                                                position_range: [12:19, 12:23),
                                            },
                                        ],
                                    ),
                                    offset_range: 262..268,
                                    position_range: [12:18, 12:24),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "subsection",
                                    ),
                                    offset_range: 269..279,
                                    position_range: [13:1, 13:11),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "root",
                                                ),
                                                offset_range: 282..286,
                                                position_range: [13:14, 13:18),
                                            },
                                        ],
                                    ),
                                    offset_range: 281..287,
                                    position_range: [13:13, 13:19),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "rose",
                                                ),
                                                offset_range: 290..294,
                                                position_range: [13:22, 13:26),
                                            },
                                        ],
                                    ),
                                    offset_range: 289..295,
                                    position_range: [13:21, 13:27),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "subsubsection",
                                    ),
                                    offset_range: 296..309,
                                    position_range: [14:1, 14:14),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "root",
                                                ),
                                                offset_range: 312..316,
                                                position_range: [14:17, 14:21),
                                            },
                                        ],
                                    ),
                                    offset_range: 311..317,
                                    position_range: [14:16, 14:22),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "rose",
                                                ),
                                                offset_range: 320..324,
                                                position_range: [14:25, 14:29),
                                            },
                                        ],
                                    ),
                                    offset_range: 319..325,
                                    position_range: [14:24, 14:30),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "eq",
                                    ),
                                    offset_range: 357..359,
                                    position_range: [17:1, 17:3),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "math",
                                                ),
                                                offset_range: 362..366,
                                                position_range: [17:6, 17:10),
                                            },
                                        ],
                                    ),
                                    offset_range: 361..367,
                                    position_range: [17:5, 17:11),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [],
                                    ),
                                    offset_range: 369..371,
                                    position_range: [17:13, 17:15),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "ne",
                                    ),
                                    offset_range: 372..374,
                                    position_range: [18:1, 18:3),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "math",
                                                ),
                                                offset_range: 377..381,
                                                position_range: [18:6, 18:10),
                                            },
                                        ],
                                    ),
                                    offset_range: 376..382,
                                    position_range: [18:5, 18:11),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [],
                                    ),
                                    offset_range: 384..386,
                                    position_range: [18:13, 18:15),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "le",
                                    ),
                                    offset_range: 387..389,
                                    position_range: [19:1, 19:3),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "math",
                                                ),
                                                offset_range: 392..396,
                                                position_range: [19:6, 19:10),
                                            },
                                        ],
                                    ),
                                    offset_range: 391..397,
                                    position_range: [19:5, 19:11),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [],
                                    ),
                                    offset_range: 399..401,
                                    position_range: [19:13, 19:15),
                                },
                            ],
                        ),
                        SeparatedExprs(
                            [
                                LpCsvExpr {
                                    data: Ident(
                                        "ge",
                                    ),
                                    offset_range: 402..404,
                                    position_range: [20:1, 20:3),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [
                                            LpCsvExpr {
                                                data: Ident(
                                                    "math",
                                                ),
                                                offset_range: 407..411,
                                                position_range: [20:6, 20:10),
                                            },
                                        ],
                                    ),
                                    offset_range: 406..412,
                                    position_range: [20:5, 20:11),
                                },
                                LpCsvExpr {
                                    data: List(
                                        [],
                                    ),
                                    offset_range: 414..416,
                                    position_range: [20:13, 20:15),
                                },
                            ],
                        ),
                    ],
                ),
            }
        "#]],
    );
}

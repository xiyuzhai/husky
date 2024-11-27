use husky_text_protocol::{offset::TextOffsetRange, range::TextPositionRange};
use token::LpCsvToken;

use crate::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LpCsvExpr {
    pub data: LpCsvExprData,
    pub offset_range: TextOffsetRange,
    pub position_range: TextPositionRange,
}
impl LpCsvExpr {
    pub fn application_expansion(&self) -> (&LpCsvExpr, &[LpCsvExpr]) {
        match &self.data {
            LpCsvExprData::Ident(ident) => (self, &[]),
            LpCsvExprData::Application(exprs) => (&exprs[0], &exprs[1..]),
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LpCsvExprData {
    Literal(LpCsvLiteral),
    Application(Vec<LpCsvExpr>),
    List(Vec<LpCsvExpr>),
    Ident(String),
    Parenthesized(Box<LpCsvExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LpCsvLiteral {
    String(String),
    Integer(i64),
    Float(OrderedFloat<f64>),
}

impl<'a> LpCsvParser<'a> {
    pub(crate) fn parse_expr(&mut self) -> Option<LpCsvExpr> {
        let mut list: Vec<LpCsvExpr> = vec![];
        self.ignore_whitespaces_and_tabs_and_comments();
        let offset_start = self.chars.current_offset();
        let position_start = self.chars.current_position();
        while let Some(expr) = self.parse_expr_aux() {
            list.push(expr);
        }
        let offset_end = self.chars.current_offset();
        let position_end = self.chars.current_position();
        match list.len() {
            0 => None,
            1 => list.pop(),
            _ => Some(LpCsvExpr {
                data: LpCsvExprData::Application(list),
                offset_range: TextOffsetRange::new(offset_start, offset_end),
                position_range: (position_start..position_end).into(),
            }),
        }
    }

    fn parse_expr_aux(&mut self) -> Option<LpCsvExpr> {
        self.ignore_whitespaces_and_tabs_and_comments();
        let offset_start = self.chars.current_offset();
        let position_start = self.chars.current_position();
        let data = self.parse_expr_data()?;
        let offset_end = self.chars.current_offset();
        let position_end = self.chars.current_position();
        Some(LpCsvExpr {
            data,
            offset_range: TextOffsetRange::new(offset_start, offset_end),
            position_range: (position_start..position_end).into(),
        })
    }

    fn parse_expr_data(&mut self) -> Option<LpCsvExprData> {
        match self.peek_token()? {
            LpCsvToken::Literal(literal) => {
                self.eat_token();
                Some(LpCsvExprData::Literal(literal))
            }
            // TODO: handle connectors followed by ident
            LpCsvToken::Ident(ident) => {
                self.eat_token();
                Some(LpCsvExprData::Ident(ident))
            }
            LpCsvToken::Connector(connector) => None,
            LpCsvToken::Separator(separator) => None,
            LpCsvToken::LeftParen => {
                self.eat_token();
                Some(LpCsvExprData::Parenthesized(
                    self.parse_parenthesized_expr(),
                ))
            }
            LpCsvToken::RightParen => None,
            LpCsvToken::LeftBracket => {
                self.eat_token();
                Some(LpCsvExprData::List(self.parse_list_expr()))
            }
            LpCsvToken::RightBracket => None,
        }
    }

    fn parse_parenthesized_expr(&mut self) -> Box<LpCsvExpr> {
        let Some(expr) = self.parse_expr() else {
            todo!()
        };
        let Some(token) = self.next_token() else {
            todo!()
        };
        if token != LpCsvToken::RightParen {
            todo!()
        }
        Box::new(expr)
    }

    fn parse_list_expr(&mut self) -> Vec<LpCsvExpr> {
        let mut list: Vec<LpCsvExpr> = vec![];
        while let Some(expr) = self.parse_expr() {
            list.push(expr);
            self.ignore_whitespaces_and_tabs_and_comments();
            match self.peek_token() {
                Some(token) => match token {
                    LpCsvToken::Separator(lp_csv_separator) => {
                        self.eat_token();
                    }
                    LpCsvToken::RightBracket => break,
                    _ => todo!(),
                },
                None => todo!(),
                // Some(']') => break,
                // Some(c) if self.is_list_item_separator(c) => (),
                // _ => todo!(),
            }
        }
        let Some(token) = self.next_token() else {
            todo!()
        };
        if token != LpCsvToken::RightBracket {
            todo!()
        }
        list
    }
}

#[test]
fn parse_lp_csv_expr_works() {
    fn t(input: &str, expect: Expect) {
        let mut parser = LpCsvParser::new(input);
        let actual = parser.parse_expr();
        expect.assert_debug_eq(&actual);
    }
    t(
        "",
        expect!([r#"
        None
    "#]),
    );
    t(
        "1",
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Literal(
                        Integer(
                            1,
                        ),
                    ),
                    offset_range: 0..1,
                    position_range: [1:1, 1:2),
                },
            )
        "#]),
    );
    t(
        "1.2",
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Literal(
                        Float(
                            1.2,
                        ),
                    ),
                    offset_range: 0..3,
                    position_range: [1:1, 1:4),
                },
            )
        "#]),
    );
    t(
        r#""1%&safdh\\command""#,
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Literal(
                        String(
                            "1%&safdh\\command",
                        ),
                    ),
                    offset_range: 0..19,
                    position_range: [1:1, 1:20),
                },
            )
        "#]),
    );
    t(
        "x",
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Ident(
                        "x",
                    ),
                    offset_range: 0..1,
                    position_range: [1:1, 1:2),
                },
            )
        "#]),
    );
    t(
        "x1",
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Ident(
                        "x1",
                    ),
                    offset_range: 0..2,
                    position_range: [1:1, 1:3),
                },
            )
        "#]),
    );
    t(
        "hello_world",
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Ident(
                        "hello_world",
                    ),
                    offset_range: 0..11,
                    position_range: [1:1, 1:12),
                },
            )
        "#]),
    );
    t(
        "hello_world,",
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Ident(
                        "hello_world",
                    ),
                    offset_range: 0..11,
                    position_range: [1:1, 1:12),
                },
            )
        "#]),
    );
    t(
        "(define x)",
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Parenthesized(
                        LpCsvExpr {
                            data: Application(
                                [
                                    LpCsvExpr {
                                        data: Ident(
                                            "define",
                                        ),
                                        offset_range: 1..7,
                                        position_range: [1:2, 1:8),
                                    },
                                    LpCsvExpr {
                                        data: Ident(
                                            "x",
                                        ),
                                        offset_range: 8..9,
                                        position_range: [1:9, 1:10),
                                    },
                                ],
                            ),
                            offset_range: 1..9,
                            position_range: [1:2, 1:10),
                        },
                    ),
                    offset_range: 0..10,
                    position_range: [1:1, 1:11),
                },
            )
        "#]),
    );
    t(
        "(add (define x) 1)",
        expect!([r#"
            Some(
                LpCsvExpr {
                    data: Parenthesized(
                        LpCsvExpr {
                            data: Application(
                                [
                                    LpCsvExpr {
                                        data: Ident(
                                            "add",
                                        ),
                                        offset_range: 1..4,
                                        position_range: [1:2, 1:5),
                                    },
                                    LpCsvExpr {
                                        data: Parenthesized(
                                            LpCsvExpr {
                                                data: Application(
                                                    [
                                                        LpCsvExpr {
                                                            data: Ident(
                                                                "define",
                                                            ),
                                                            offset_range: 6..12,
                                                            position_range: [1:7, 1:13),
                                                        },
                                                        LpCsvExpr {
                                                            data: Ident(
                                                                "x",
                                                            ),
                                                            offset_range: 13..14,
                                                            position_range: [1:14, 1:15),
                                                        },
                                                    ],
                                                ),
                                                offset_range: 6..14,
                                                position_range: [1:7, 1:15),
                                            },
                                        ),
                                        offset_range: 5..15,
                                        position_range: [1:6, 1:16),
                                    },
                                    LpCsvExpr {
                                        data: Literal(
                                            Integer(
                                                1,
                                            ),
                                        ),
                                        offset_range: 16..17,
                                        position_range: [1:17, 1:18),
                                    },
                                ],
                            ),
                            offset_range: 1..17,
                            position_range: [1:2, 1:18),
                        },
                    ),
                    offset_range: 0..18,
                    position_range: [1:1, 1:19),
                },
            )
        "#]),
    );
    t(
        r#"1,2
3,4"#,
        expect![[r#"
            Some(
                LpCsvExpr {
                    data: Literal(
                        Integer(
                            1,
                        ),
                    ),
                    offset_range: 0..1,
                    position_range: [1:1, 1:2),
                },
            )
        "#]],
    );
    t(
        r#"x
3"#,
        expect![[r#"
            Some(
                LpCsvExpr {
                    data: Ident(
                        "x",
                    ),
                    offset_range: 0..1,
                    position_range: [1:1, 1:2),
                },
            )
        "#]],
    );
    t(
        "[1,2,3]",
        expect![[r#"
            Some(
                LpCsvExpr {
                    data: List(
                        [
                            LpCsvExpr {
                                data: Literal(
                                    Integer(
                                        1,
                                    ),
                                ),
                                offset_range: 1..2,
                                position_range: [1:2, 1:3),
                            },
                            LpCsvExpr {
                                data: Literal(
                                    Integer(
                                        2,
                                    ),
                                ),
                                offset_range: 3..4,
                                position_range: [1:4, 1:5),
                            },
                            LpCsvExpr {
                                data: Literal(
                                    Integer(
                                        3,
                                    ),
                                ),
                                offset_range: 5..6,
                                position_range: [1:6, 1:7),
                            },
                        ],
                    ),
                    offset_range: 0..7,
                    position_range: [1:1, 1:8),
                },
            )
        "#]],
    );
    t(
        "[]",
        expect![[r#"
            Some(
                LpCsvExpr {
                    data: List(
                        [],
                    ),
                    offset_range: 0..2,
                    position_range: [1:1, 1:3),
                },
            )
        "#]],
    );
    t(
        "f [1,2,3]",
        expect![[r#"
            Some(
                LpCsvExpr {
                    data: Application(
                        [
                            LpCsvExpr {
                                data: Ident(
                                    "f",
                                ),
                                offset_range: 0..1,
                                position_range: [1:1, 1:2),
                            },
                            LpCsvExpr {
                                data: List(
                                    [
                                        LpCsvExpr {
                                            data: Literal(
                                                Integer(
                                                    1,
                                                ),
                                            ),
                                            offset_range: 3..4,
                                            position_range: [1:4, 1:5),
                                        },
                                        LpCsvExpr {
                                            data: Literal(
                                                Integer(
                                                    2,
                                                ),
                                            ),
                                            offset_range: 5..6,
                                            position_range: [1:6, 1:7),
                                        },
                                        LpCsvExpr {
                                            data: Literal(
                                                Integer(
                                                    3,
                                                ),
                                            ),
                                            offset_range: 7..8,
                                            position_range: [1:8, 1:9),
                                        },
                                    ],
                                ),
                                offset_range: 2..9,
                                position_range: [1:3, 1:10),
                            },
                        ],
                    ),
                    offset_range: 0..9,
                    position_range: [1:1, 1:10),
                },
            )
        "#]],
    );
    t(
        r#"# comment
1"#,
        expect![[r#"
            None
        "#]],
    );
    t(
        r#"1# comment
1"#,
        expect![[r#"
            Some(
                LpCsvExpr {
                    data: Literal(
                        Integer(
                            1,
                        ),
                    ),
                    offset_range: 0..1,
                    position_range: [1:1, 1:2),
                },
            )
        "#]],
    );
    t(
        r#"// comment
1"#,
        expect![[r#"
            None
        "#]],
    );
    t(
        r#"1// comment"#,
        expect![[r#"
            Some(
                LpCsvExpr {
                    data: Literal(
                        Integer(
                            1,
                        ),
                    ),
                    offset_range: 0..1,
                    position_range: [1:1, 1:2),
                },
            )
        "#]],
    );
    t(
        r#"-- comment
1"#,
        expect![[r#"
            None
        "#]],
    );
    t(
        r#"1-- comment"#,
        expect![[r#"
            Some(
                LpCsvExpr {
                    data: Literal(
                        Integer(
                            1,
                        ),
                    ),
                    offset_range: 0..1,
                    position_range: [1:1, 1:2),
                },
            )
        "#]],
    );
}

use crate::*;
use maybe_result::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LpCsvRow {
    Expr(LpCsvExpr),
    SeparatedExprs(Vec<LpCsvExpr>),
}

impl<'a> LpCsvParser<'a> {
    pub(crate) fn parse_row(&mut self) -> LpCsvMaybeResult<LpCsvRow> {
        self.ignore_whitespaces_and_tabs_and_blank_lines_and_comments();
        let expr = self.parse_expr()?;
        self.ignore_whitespaces_and_tabs_and_comments();
        match self.chars.peek() {
            Some(c) if self.is_cell_separator(c) => {
                let mut exprs: Vec<LpCsvExpr> = vec![expr];
                loop {
                    self.ignore_separators();
                    let Some(expr) = self.parse_expr() else {
                        use husky_print_utils::{p, DisplayIt};
                        p!(self.input);
                        todo!("shouldn't end with separator, report as error")
                    };
                    exprs.push(expr);
                    self.ignore_whitespaces_and_tabs_and_comments();
                    match self.chars.peek() {
                        Some(c) if self.is_cell_separator(c) => (),
                        Some('\n') | None => break,
                        Some(c) => todo!("c: {c:?}"),
                    }
                }
                JustOk(LpCsvRow::SeparatedExprs(exprs))
            }
            Some('\n') | None => JustOk(LpCsvRow::Expr(expr)),
            Some(c) => todo!("c: {c:?}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(input: &str, expect: Expect) {
        let mut parser = LpCsvParser::new(input);
        let row = parser.parse_row();
        expect.assert_debug_eq(&row);
    }

    #[test]
    fn parse_lp_csv_row_works() {
        t(
            "",
            expect![[r#"
        Nothing
    "#]],
        );
        t(
            "1",
            expect![[r#"
            JustOk(
                Expr(
                    LpCsvExpr {
                        data: Literal(
                            Integer(
                                1,
                            ),
                        ),
                        offset_range: 0..1,
                        position_range: [1:1, 1:2),
                    },
                ),
            )
        "#]],
        );
        t(
            "1,2",
            expect![[r#"
            JustOk(
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
            )
        "#]],
        );
        t(
            "mathbb,1,2",
            expect![[r#"
            JustOk(
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
            )
        "#]],
        );
        t(
            r#"1,2
3,4"#,
            expect![[r#"
            JustOk(
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
            )
        "#]],
        );
        t(
            r#"1,2;3,4"#,
            expect![[r#"
            JustOk(
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
                        LpCsvExpr {
                            data: Literal(
                                Integer(
                                    3,
                                ),
                            ),
                            offset_range: 4..5,
                            position_range: [1:5, 1:6),
                        },
                        LpCsvExpr {
                            data: Literal(
                                Integer(
                                    4,
                                ),
                            ),
                            offset_range: 6..7,
                            position_range: [1:7, 1:8),
                        },
                    ],
                ),
            )
        "#]],
        );
        t(
            "# comment\n1",
            expect![[r#"
            JustOk(
                Expr(
                    LpCsvExpr {
                        data: Literal(
                            Integer(
                                1,
                            ),
                        ),
                        offset_range: 10..11,
                        position_range: [2:1, 2:2),
                    },
                ),
            )
        "#]],
        );
    }

    #[test]
    fn dbg() {
        t(
            "[]",
            expect![[r#"
            JustOk(
                Expr(
                    LpCsvExpr {
                        data: List(
                            [],
                        ),
                        offset_range: 0..2,
                        position_range: [1:1, 1:3),
                    },
                ),
            )
        "#]],
        );
    }
}

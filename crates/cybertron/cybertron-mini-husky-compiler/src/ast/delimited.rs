use token::delimiter::{LPAR, RPAR};

use super::*;

/// delimited items are ignored intentionally
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DelimitedFragment {
    LeftDelimiter(LeftDelimiter),
    Ast(AstData),
    Obstruction,
}

impl From<PreAst> for Option<DelimitedFragment> {
    fn from(pre_ast: PreAst) -> Self {
        match pre_ast {
            PreAst::Keyword(_) => Some(DelimitedFragment::Obstruction),
            PreAst::Opr(_) => Some(DelimitedFragment::Obstruction),
            PreAst::LeftDelimiter(left_delimiter) => {
                Some(DelimitedFragment::LeftDelimiter(left_delimiter))
            }
            PreAst::RightDelimiter(_) => Some(DelimitedFragment::Obstruction),
            PreAst::Ast(ast) => match ast {
                AstData::SeparatedItem { content, separator } => None,
                ast => Some(DelimitedFragment::Ast(ast)),
            },
            PreAst::Separator(_) => Some(DelimitedFragment::Obstruction),
        }
    }
}

pub(super) fn reduce_by_delimited(
    pre_asts: Seq<Option<PreAst>>,
    allocated_asts: Seq<Option<Ast>>,
) -> (Seq<Option<PreAst>>, Seq<Option<Ast>>) {
    let (pre_asts, allocated_asts) = reduce_pre_asts_by_delimited_item(pre_asts, allocated_asts);
    let fragments =
        pre_asts.map(|pre_ast| -> Option<DelimitedFragment> { pre_ast.map(Into::into).flatten() });
    let fragments_nearest_left2 = fragments.nearest_left2();
    let new_asts = new_ast_by_delimited.apply(fragments_nearest_left2, pre_asts);
    let (pre_asts, new_parents) = (|idx,
                                    pre_ast,
                                    fragment_nearest_left2: Option2<(Idx, DelimitedFragment)>,
                                    new_ast,
                                    new_ast_nearest_right|
     -> (Option<PreAst>, Option<Idx>) {
        if let Some(new_ast) = new_ast {
            return (Some(PreAst::Ast(new_ast)), None);
        }
        let Some((
            idx1,
            AstData::Delimited {
                left_delimiter_idx, ..
            },
        )) = new_ast_nearest_right
        else {
            return (pre_ast, None);
        };
        if left_delimiter_idx == idx {
            debug_assert!(matches!(pre_ast, Some(PreAst::LeftDelimiter(_))));
            return (None, None);
        }
        let Some(PreAst::Ast(ast)) = pre_ast else {
            return (pre_ast, None);
        };
        let Some((idx2, DelimitedFragment::LeftDelimiter(_))) = fragment_nearest_left2.first()
        else {
            return (pre_ast, None);
        };
        if left_delimiter_idx == idx2 {
            (None, Some(idx1))
        } else {
            (pre_ast, None)
        }
    })
    .apply_enumerated(
        pre_asts,
        fragments_nearest_left2,
        new_asts,
        new_asts.nearest_right(),
    )
    .decouple();
    let allocated_asts =
        (|allocated_ast: Option<Ast>, new_ast: Option<AstData>, new_parent| match allocated_ast {
            Some(allocated_ast) => {
                if new_ast.is_some() {
                    p!(allocated_ast, new_ast);
                }
                debug_assert!(new_ast.is_none());
                match new_parent {
                    Some(new_parent) => {
                        debug_assert!(allocated_ast.parent.is_none());
                        Some(Ast {
                            parent: Some(new_parent),
                            data: allocated_ast.data,
                        })
                    }
                    None => Some(allocated_ast),
                }
            }
            None => {
                debug_assert!(new_parent.is_none());
                Some(Ast {
                    parent: None,
                    data: new_ast?,
                })
            }
        })
        .apply(allocated_asts, new_asts, new_parents);
    (pre_asts, allocated_asts)
}

#[test]
fn reduce_by_delimited_works() {
    #[track_caller]
    fn t(
        pre_asts: Seq<Option<PreAst>>,
        allocated_asts: Seq<Option<Ast>>,
        pre_asts1_expected: Seq<Option<PreAst>>,
        allocated_asts1_expected: Seq<Option<Ast>>,
    ) {
        let (pre_asts1, allocated_asts1) = reduce_by_delimited(pre_asts, allocated_asts);
        assert_eq!(pre_asts1, pre_asts1_expected);
        assert_eq!(allocated_asts1, allocated_asts1_expected);
    }
    t(
        seq![
            Some(PreAst::LeftDelimiter(LPAR)),
            Some(PreAst::RightDelimiter(RPAR))
        ],
        seq![None, None],
        seq![
            None,
            Some(PreAst::Ast(AstData::Delimited {
                left_delimiter_idx: idx!(0),
                left_delimiter: LPAR,
                right_delimiter: RPAR
            }))
        ],
        seq![
            None,
            Some(Ast {
                parent: None,
                data: AstData::Delimited {
                    left_delimiter_idx: idx!(0),
                    left_delimiter: LPAR,
                    right_delimiter: RPAR
                }
            })
        ],
    );
    t(
        seq![
            Some(PreAst::LeftDelimiter(LPAR)),
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::RightDelimiter(RPAR))
        ],
        seq![
            None,
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None
        ],
        seq![
            None,
            None,
            Some(PreAst::Ast(AstData::Delimited {
                left_delimiter_idx: idx!(0),
                left_delimiter: LPAR,
                right_delimiter: RPAR
            }))
        ],
        seq![
            None,
            Some(Ast {
                parent: Some(idx!(2)),
                data: AstData::Literal(Literal::Int(1)),
            }),
            Some(Ast {
                parent: None,
                data: AstData::Delimited {
                    left_delimiter_idx: idx!(0),
                    left_delimiter: LPAR,
                    right_delimiter: RPAR
                }
            })
        ],
    );
    t(
        seq![
            Some(PreAst::LeftDelimiter(LPAR)),
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::Separator(Separator::Comma)),
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::RightDelimiter(RPAR))
        ],
        seq![
            None,
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None,
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None
        ],
        seq![
            None,
            None,
            None,
            None,
            Some(PreAst::Ast(AstData::Delimited {
                left_delimiter_idx: idx!(0),
                left_delimiter: LPAR,
                right_delimiter: RPAR
            }))
        ],
        seq![
            None,
            Some(Ast {
                parent: Some(idx!(2)),
                data: AstData::Literal(Literal::Int(1)),
            }),
            Some(Ast {
                parent: Some(idx!(4)),
                data: AstData::SeparatedItem {
                    content: Some(idx!(1)),
                    separator: Separator::Comma
                }
            }),
            Some(Ast {
                parent: Some(idx!(4)),
                data: AstData::Literal(Literal::Int(1)),
            }),
            Some(Ast {
                parent: None,
                data: AstData::Delimited {
                    left_delimiter_idx: idx!(0),
                    left_delimiter: LPAR,
                    right_delimiter: RPAR
                }
            })
        ],
    );
    t(
        seq![
            Some(PreAst::LeftDelimiter(LPAR)),
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::Separator(Separator::Comma)),
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::Separator(Separator::Comma)),
            Some(PreAst::RightDelimiter(RPAR))
        ],
        seq![
            None,
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None,
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None,
            None
        ],
        seq![
            None,
            None,
            None,
            None,
            None,
            Some(PreAst::Ast(AstData::Delimited {
                left_delimiter_idx: idx!(0),
                left_delimiter: LPAR,
                right_delimiter: RPAR
            }))
        ],
        seq![
            None,
            Some(Ast {
                parent: Some(idx!(2)),
                data: AstData::Literal(Literal::Int(1)),
            }),
            Some(Ast {
                parent: Some(idx!(5)),
                data: AstData::SeparatedItem {
                    content: Some(idx!(1)),
                    separator: Separator::Comma
                }
            }),
            Some(Ast {
                parent: Some(idx!(4)),
                data: AstData::Literal(Literal::Int(1)),
            }),
            Some(Ast {
                parent: Some(idx!(5)),
                data: AstData::SeparatedItem {
                    content: Some(idx!(3)),
                    separator: Separator::Comma
                }
            }),
            Some(Ast {
                parent: None,
                data: AstData::Delimited {
                    left_delimiter_idx: idx!(0),
                    left_delimiter: LPAR,
                    right_delimiter: RPAR
                }
            })
        ],
    );
}

fn new_ast_by_delimited(
    nearest_left2: Option2<(Idx, DelimitedFragment)>,
    pre_ast: Option<PreAst>,
) -> Option<AstData> {
    let Some(PreAst::RightDelimiter(right_delimiter)) = pre_ast else {
        return None;
    };
    match nearest_left2.first() {
        Some((idx, fst)) => match fst {
            DelimitedFragment::LeftDelimiter(left_delimiter) => Some(AstData::Delimited {
                left_delimiter_idx: idx,
                left_delimiter,
                right_delimiter,
            }),
            DelimitedFragment::Ast(_) => match nearest_left2.second() {
                Some((idx, snd)) => match snd {
                    DelimitedFragment::LeftDelimiter(left_delimiter) => Some(AstData::Delimited {
                        left_delimiter_idx: idx,
                        left_delimiter,
                        right_delimiter,
                    }),
                    DelimitedFragment::Ast(_) | DelimitedFragment::Obstruction => None,
                },
                None => None,
            },
            DelimitedFragment::Obstruction => None,
        },
        None => None,
    }
}

fn reduce_pre_asts_by_delimited_item(
    pre_asts: Seq<Option<PreAst>>,
    allocated_asts: Seq<Option<Ast>>,
) -> (Seq<Option<PreAst>>, Seq<Option<Ast>>) {
    let pre_asts_nearest_left2 = pre_asts.nearest_left2();
    let new_asts = new_ast_by_separated_item.apply(pre_asts_nearest_left2, pre_asts);
    let (pre_asts, new_parents) =
        (|idx, pre_ast, new_ast, new_ast_nearest_right| -> (Option<PreAst>, Option<Idx>) {
            if let Some(new_ast) = new_ast {
                return (Some(PreAst::Ast(new_ast)), None);
            }
            let Some(pre_ast) = pre_ast else {
                return (None, None);
            };
            let Some((
                idx2,
                AstData::SeparatedItem {
                    content: Some(content),
                    separator,
                },
            )) = new_ast_nearest_right
            else {
                return (Some(pre_ast), None);
            };
            if content == idx {
                (None, Some(idx2))
            } else {
                (Some(pre_ast), None)
            }
        })
        .apply_enumerated(pre_asts, new_asts, new_asts.nearest_right())
        .decouple();
    let allocated_asts =
        (|allocated_ast: Option<Ast>, new_ast, new_parent: Option<_>| match new_ast {
            Some(new_ast) => {
                debug_assert!(allocated_ast.is_none());
                debug_assert!(new_parent.is_none());
                Some(Ast {
                    parent: None,
                    data: new_ast,
                })
            }
            None => match new_parent {
                Some(new_parent) => {
                    let Some(Ast { parent: None, data }) = allocated_ast else {
                        unreachable!()
                    };
                    Some(Ast {
                        parent: Some(new_parent),
                        data,
                    })
                }
                None => allocated_ast,
            },
        })
        .apply(allocated_asts, new_asts, new_parents);
    (pre_asts, allocated_asts)
}

#[test]
fn reduce_pre_asts_by_delimited_item_works() {
    #[track_caller]
    fn t(
        pre_asts: Seq<Option<PreAst>>,
        allocated_asts: Seq<Option<Ast>>,
        pre_asts1_expected: Seq<Option<PreAst>>,
        allocated_asts1_expected: Seq<Option<Ast>>,
    ) {
        let (pre_asts1, allocated_asts1) =
            reduce_pre_asts_by_delimited_item(pre_asts, allocated_asts);
        assert_eq!(pre_asts1, pre_asts1_expected);
        assert_eq!(allocated_asts1, allocated_asts1_expected);
    }

    t(seq![], seq![], seq![], seq![]);
    t(
        seq![Some(PreAst::Ast(AstData::Literal(Literal::Int(1))))],
        seq![Some(Ast {
            parent: None,
            data: AstData::Literal(Literal::Int(1))
        })],
        seq![Some(PreAst::Ast(AstData::Literal(Literal::Int(1))))],
        seq![Some(Ast {
            parent: None,
            data: AstData::Literal(Literal::Int(1))
        })],
    );
    t(
        seq![Some(PreAst::Separator(Separator::Comma))],
        seq![None],
        seq![Some(PreAst::Ast(AstData::SeparatedItem {
            content: None,
            separator: Separator::Comma,
        }))],
        seq![Some(Ast {
            parent: None,
            data: AstData::SeparatedItem {
                content: None,
                separator: Separator::Comma
            }
        })],
    );
    t(
        seq![
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::Separator(Separator::Comma))
        ],
        seq![
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None
        ],
        seq![
            None,
            Some(PreAst::Ast(AstData::SeparatedItem {
                content: Some(idx!(0)),
                separator: Separator::Comma
            }))
        ],
        seq![
            Some(Ast {
                parent: Some(idx!(1)),
                data: AstData::Literal(Literal::Int(1)),
            }),
            Some(Ast {
                parent: None,
                data: AstData::SeparatedItem {
                    content: Some(idx!(0)),
                    separator: Separator::Comma
                }
            })
        ],
    );
}

fn new_ast_by_separated_item(
    nearest_left2: Option2<(Idx, PreAst)>,
    pre_ast: Option<PreAst>,
) -> Option<AstData> {
    let Some(PreAst::Separator(separator)) = pre_ast else {
        return None;
    };
    match nearest_left2.first() {
        Some((idx, pre_ast)) => match pre_ast {
            PreAst::Keyword(_) | PreAst::LeftDelimiter(_) | PreAst::Separator(_) => {
                Some(AstData::SeparatedItem {
                    content: None,
                    separator,
                })
            }
            PreAst::Opr(_) | PreAst::RightDelimiter(_) => return None,
            PreAst::Ast(AstData::SeparatedItem {
                content,
                separator: separator1,
            }) => match (separator, separator1) {
                (Separator::Semicolon, Separator::Comma) => Some(AstData::SeparatedItem {
                    content: Some(idx),
                    separator,
                }),
                (Separator::Comma, _) | (Separator::Semicolon, Separator::Semicolon) => {
                    Some(AstData::SeparatedItem {
                        content: None,
                        separator,
                    })
                }
            },

            PreAst::Ast(_) => match nearest_left2.second() {
                Some((_, snd)) => match snd {
                    PreAst::Keyword(_) if separator == Separator::Semicolon => None,
                    PreAst::Keyword(_) | PreAst::LeftDelimiter(_) | PreAst::Separator(_) => {
                        Some(AstData::SeparatedItem {
                            content: Some(idx),
                            separator,
                        })
                    }
                    PreAst::Ast(
                        AstData::SeparatedItem { .. }
                        | AstData::LetInit { .. }
                        | AstData::Return { .. }
                        | AstData::Assert { .. }
                        | AstData::Defn { .. },
                    ) => Some(AstData::SeparatedItem {
                        content: Some(idx),
                        separator,
                    }),
                    PreAst::Opr(_) | PreAst::RightDelimiter(_) | PreAst::Ast(_) => None,
                },
                None => Some(AstData::SeparatedItem {
                    content: Some(idx),
                    separator,
                }),
            },
        },
        None => Some(AstData::SeparatedItem {
            content: None,
            separator,
        }),
    }
}

#[test]
fn new_ast_by_delimited_item_works() {
    fn t(
        pre_asts: Seq<Option<PreAst>>,
        allocated_asts: Seq<Option<Ast>>,
        new_asts_expected: Seq<Option<AstData>>,
    ) {
        let pre_asts_nearest_left2 = pre_asts.nearest_left2();
        let new_asts = new_ast_by_separated_item.apply(pre_asts_nearest_left2, pre_asts);
        assert_eq!(new_asts, new_asts_expected);
    }

    t(seq![], seq![], seq![]);
    t(
        seq![Some(PreAst::Separator(Separator::Comma))],
        seq![None],
        seq![Some(AstData::SeparatedItem {
            content: None,
            separator: Separator::Comma
        })],
    );
    t(
        seq![
            Some(PreAst::Separator(Separator::Comma)),
            Some(PreAst::Separator(Separator::Comma))
        ],
        seq![None, None],
        seq![
            Some(AstData::SeparatedItem {
                content: None,
                separator: Separator::Comma
            }),
            Some(AstData::SeparatedItem {
                content: None,
                separator: Separator::Comma
            })
        ],
    );
    t(
        seq![
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::Separator(Separator::Comma))
        ],
        seq![
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None
        ],
        seq![
            None,
            Some(AstData::SeparatedItem {
                content: Some(idx!(0)),
                separator: Separator::Comma
            })
        ],
    );
    t(
        seq![
            Some(PreAst::Opr(Opr::Prefix(PrefixOpr::Minus))),
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::Separator(Separator::Comma))
        ],
        seq![
            None,
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None
        ],
        seq![None, None, None,],
    );
    t(
        seq![
            Some(PreAst::Keyword(Keyword::LET)),
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            Some(PreAst::Separator(Separator::Comma))
        ],
        seq![
            None,
            Some(Ast {
                parent: None,
                data: AstData::Literal(Literal::Int(1)),
            }),
            None
        ],
        seq![
            None,
            None,
            Some(AstData::SeparatedItem {
                content: Some(idx!(1)),
                separator: Separator::Comma
            }),
        ],
    );
}

#[test]
fn reduce_n_times_for_delimited_works1() {
    t(
        "()",
        1,
        expect![[r#"
            [
                #0 `(`: `(`,
                #1 `)`: "()" ✓,
            ]
        "#]],
    );
    t(
        "(,)",
        1,
        expect![[r#"
            [
                #0 `(`: `(`,
                #1 `,`: ", ",
                #2 `)`: "(, )" ✓,
            ]
        "#]],
    );
    t(
        "(,,)",
        1,
        expect![[r#"
            [
                #0 `(`: `(`,
                #1 `,`: ", ",
                #2 `,`: ", ",
                #3 `)`: "(, , )" ✓,
            ]
        "#]],
    );
    t(
        "(1)",
        1,
        expect![[r#"
            [
                #0 `(`: `(`,
                #1 `1`: "1",
                #2 `)`: "(1)" ✓,
            ]
        "#]],
    );
    t(
        "(1,)",
        1,
        expect![[r#"
            [
                #0 `(`: `(`,
                #1 `1`: "1",
                #2 `,`: "1, ",
                #3 `)`: "(1, )" ✓,
            ]
        "#]],
    );
    t(
        "(1,,)",
        1,
        expect![[r#"
            [
                #0 `(`: `(`,
                #1 `1`: "1",
                #2 `,`: "1, ",
                #3 `,`: ", ",
                #4 `)`: "(1, , )" ✓,
            ]
        "#]],
    );
    t(
        "(1,1)",
        1,
        expect![[r#"
            [
                #0 `(`: `(`,
                #1 `1`: "1",
                #2 `,`: "1, ",
                #3 `1`: "1",
                #4 `)`: "(1, 1)" ✓,
            ]
        "#]],
    );
    t(
        "((1,1),1)",
        1,
        expect![[r#"
            [
                #0 `(`: `(`,
                #1 `(`: `(`,
                #2 `1`: "1",
                #3 `,`: "1, ",
                #4 `1`: "1",
                #5 `)`: "(1, 1)" ✓,
                #6 `,`: `,`,
                #7 `1`: "1" ✓,
                #8 `)`: `)`,
            ]
        "#]],
    );
}

#[test]
fn reduce_n_times_for_delimited_works2() {
    t(
        "{}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `}`: "{}" ✓,
            ]
        "#]],
    );
    t(
        "{,}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `,`: ", ",
                #2 `}`: "{ ,  }" ✓,
            ]
        "#]],
    );
    t(
        "{,,}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `,`: ", ",
                #2 `,`: ", ",
                #3 `}`: "{ , ,  }" ✓,
            ]
        "#]],
    );
    t(
        "{1}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `1`: "1",
                #2 `}`: "{ 1 }" ✓,
            ]
        "#]],
    );
    t(
        "{1,}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `1`: "1",
                #2 `,`: "1, ",
                #3 `}`: "{ 1,  }" ✓,
            ]
        "#]],
    );
    t(
        "{1,,}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `1`: "1",
                #2 `,`: "1, ",
                #3 `,`: ", ",
                #4 `}`: "{ 1, ,  }" ✓,
            ]
        "#]],
    );
    t(
        "{1,1}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `1`: "1",
                #2 `,`: "1, ",
                #3 `1`: "1",
                #4 `}`: "{ 1, 1 }" ✓,
            ]
        "#]],
    );
    t(
        "{{1,1},1}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `{`: `{`,
                #2 `1`: "1",
                #3 `,`: "1, ",
                #4 `1`: "1",
                #5 `}`: "{ 1, 1 }" ✓,
                #6 `,`: `,`,
                #7 `1`: "1" ✓,
                #8 `}`: `}`,
            ]
        "#]],
    );
}

#[test]
fn reduce_n_times_for_delimited_works3() {
    t(
        "{}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `}`: "{}" ✓,
            ]
        "#]],
    );
    t(
        "{;}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `;`: "; ",
                #2 `}`: "{ ;  }" ✓,
            ]
        "#]],
    );
    t(
        "{;;}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `;`: "; ",
                #2 `;`: "; ",
                #3 `}`: "{ ; ;  }" ✓,
            ]
        "#]],
    );
    t(
        "{1}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `1`: "1",
                #2 `}`: "{ 1 }" ✓,
            ]
        "#]],
    );
    t(
        "{1;}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `1`: "1",
                #2 `;`: "1; ",
                #3 `}`: "{ 1;  }" ✓,
            ]
        "#]],
    );
    t(
        "{1;;}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `1`: "1",
                #2 `;`: "1; ",
                #3 `;`: "; ",
                #4 `}`: "{ 1; ;  }" ✓,
            ]
        "#]],
    );
    t(
        "{1;1}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `1`: "1",
                #2 `;`: "1; ",
                #3 `1`: "1",
                #4 `}`: "{ 1; 1 }" ✓,
            ]
        "#]],
    );
    t(
        "{{1;1};1}",
        1,
        expect![[r#"
            [
                #0 `{`: `{`,
                #1 `{`: `{`,
                #2 `1`: "1",
                #3 `;`: "1; ",
                #4 `1`: "1",
                #5 `}`: "{ 1; 1 }" ✓,
                #6 `;`: `;`,
                #7 `1`: "1" ✓,
                #8 `}`: `}`,
            ]
        "#]],
    );
}

pub fn count() {}

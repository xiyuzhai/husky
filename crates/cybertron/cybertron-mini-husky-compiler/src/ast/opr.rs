use any::AnySeq;
use cybertron::debug::set_debug;
use indexmap::IndexMap;
use token::opr::{PrefixOpr, SuffixOpr};

use super::*;

pub(super) fn reduce_by_opr(
    pre_asts: Seq<Option<PreAst>>,
    allocated_asts: Seq<Option<Ast>>,
) -> (Seq<Option<PreAst>>, Seq<Option<Ast>>) {
    let pre_asts_nearest_left2 = pre_asts.nearest_left2();
    let pre_asts_nearest_right2 = pre_asts.nearest_right2();
    let new_opr_asts = new_opr_ast.apply(pre_asts_nearest_left2, pre_asts, pre_asts_nearest_right2);
    let (pre_asts_reduced, new_parents) = reduce_pre_asts_by_opr(pre_asts, new_opr_asts);
    let pre_asts = update_pre_asts_by_new_asts(pre_asts_reduced, new_opr_asts);
    let allocated_asts =
        allocate_asts_and_update_parents(allocated_asts, new_opr_asts, new_parents);
    (pre_asts, allocated_asts)
}

#[test]
fn reduce_asts_by_binary_opr_works1() {
    let pre_asts = seq![
        Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
        Some(PreAst::Opr(Opr::Binary(BinaryOpr::Add))),
        Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
    ];
    let allocated_asts = seq![
        Some(Ast {
            parent: None,
            data: AstData::Literal(Literal::Int(1))
        }),
        None,
        Some(Ast {
            parent: None,
            data: AstData::Literal(Literal::Int(1))
        }),
    ];
    let (pre_asts1, allocated_asts1) = reduce_by_opr(pre_asts, allocated_asts);
    assert_eq!(
        pre_asts1,
        seq![
            None,
            Some(PreAst::Ast(AstData::Binary {
                lopd: idx!(0),
                opr: BinaryOpr::Add,
                ropd: idx!(2),
                lopd_ident: None
            })),
            None
        ]
    );
    assert_eq!(
        allocated_asts1,
        seq![
            Some(Ast {
                parent: Some(idx!(1)),
                data: AstData::Literal(Literal::Int(1))
            }),
            Some(Ast {
                parent: None,
                data: AstData::Binary {
                    lopd: idx!(0),
                    lopd_ident: None,
                    opr: BinaryOpr::Add,
                    ropd: idx!(2)
                }
            }),
            Some(Ast {
                parent: Some(idx!(1)),
                data: AstData::Literal(Literal::Int(1))
            }),
        ]
    );
}

#[test]
fn reduce_asts_by_prefix_opr_works1() {
    let pre_asts = seq![
        Some(PreAst::Opr(Opr::Prefix(PrefixOpr::Minus))),
        Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
    ];
    let allocated_asts = seq![
        None,
        Some(Ast {
            parent: None,
            data: AstData::Literal(Literal::Int(1))
        }),
    ];
    let (pre_asts1, allocated_asts1) = reduce_by_opr(pre_asts, allocated_asts);
    assert_eq!(
        pre_asts1,
        seq![
            Some(PreAst::Ast(AstData::Prefix {
                opr: PrefixOpr::Minus,
                opd: idx!(1),
            })),
            None
        ]
    );
    assert_eq!(
        allocated_asts1,
        seq![
            Some(Ast {
                parent: None,
                data: AstData::Prefix {
                    opr: PrefixOpr::Minus,
                    opd: idx!(1),
                }
            }),
            Some(Ast {
                parent: Some(idx!(0)),
                data: AstData::Literal(Literal::Int(1))
            }),
        ]
    );
}

#[test]
fn reduce_asts_by_suffix_opr_works1() {
    let pre_asts = seq![
        Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
        Some(PreAst::Opr(Opr::Suffix(SuffixOpr::Decr))),
    ];
    let allocated_asts = seq![
        Some(Ast {
            parent: None,
            data: AstData::Literal(Literal::Int(1))
        }),
        None,
    ];
    let (pre_asts1, allocated_asts1) = reduce_by_opr(pre_asts, allocated_asts);
    assert_eq!(
        pre_asts1,
        seq![
            None,
            Some(PreAst::Ast(AstData::Suffix {
                opr: SuffixOpr::Decr,
                opd: idx!(0),
            })),
        ]
    );
    assert_eq!(
        allocated_asts1,
        seq![
            Some(Ast {
                parent: Some(idx!(1)),
                data: AstData::Literal(Literal::Int(1))
            }),
            Some(Ast {
                parent: None,
                data: AstData::Suffix {
                    opr: SuffixOpr::Decr,
                    opd: idx!(0),
                }
            }),
        ]
    );
}

#[test]
fn reduce_asts_by_opr_works_as_expected() {
    fn t(input: &str, expect: Expect) {
        let tokens = tokenize(input);
        let pre_asts = calc_pre_ast_initial_seq(tokens);
        let mut seqs: IndexMap<String, AnySeq> = Default::default();
        let allocated_asts: Seq<Option<Ast>> = tokens.map(|token| token.into());
        seqs.insert("pre_asts".into(), pre_asts.into());
        seqs.insert("allocated_asts".into(), allocated_asts.into());
        let (pre_asts1, allocated_asts1) = reduce_by_opr(pre_asts, allocated_asts);
        seqs.insert("pre_asts1".into(), pre_asts1.into());
        seqs.insert("allocated_asts1".into(), allocated_asts1.into());
        let (pre_asts2, allocated_asts2) = reduce_by_opr(pre_asts1, allocated_asts1);
        seqs.insert("pre_asts2".into(), pre_asts2.into());
        seqs.insert("allocated_asts2".into(), allocated_asts2.into());
        let (pre_asts3, allocated_asts3) = reduce_by_opr(pre_asts2, allocated_asts2);
        seqs.insert("pre_asts3".into(), pre_asts3.into());
        seqs.insert("allocated_asts3".into(), allocated_asts3.into());
        expect.assert_debug_eq(&seqs)
    }
    t(
        "hello",
        expect![[r#"
            {
                "pre_asts": [Some(Ident(`hello`))],
                "allocated_asts": [Some(Ast { parent: None, data: Ident(`hello`) })],
                "pre_asts1": [Some(Ident(`hello`))],
                "allocated_asts1": [Some(Ast { parent: None, data: Ident(`hello`) })],
                "pre_asts2": [Some(Ident(`hello`))],
                "allocated_asts2": [Some(Ast { parent: None, data: Ident(`hello`) })],
                "pre_asts3": [Some(Ident(`hello`))],
                "allocated_asts3": [Some(Ast { parent: None, data: Ident(`hello`) })],
            }
        "#]],
    );
    t(
        "1",
        expect![[r#"
            {
                "pre_asts": [Some(Literal(`1`))],
                "allocated_asts": [Some(Ast { parent: None, data: Literal(`1`) })],
                "pre_asts1": [Some(Literal(`1`))],
                "allocated_asts1": [Some(Ast { parent: None, data: Literal(`1`) })],
                "pre_asts2": [Some(Literal(`1`))],
                "allocated_asts2": [Some(Ast { parent: None, data: Literal(`1`) })],
                "pre_asts3": [Some(Literal(`1`))],
                "allocated_asts3": [Some(Ast { parent: None, data: Literal(`1`) })],
            }
        "#]],
    );
    t(
        "1+1",
        expect![[r#"
            {
                "pre_asts": [Some(Literal(`1`)), Some(`+(add)`), Some(Literal(`1`))],
                "allocated_asts": [
                    Some(Ast { parent: None, data: Literal(`1`) }),
                    None,
                    Some(Ast { parent: None, data: Literal(`1`) }),
                ],
                "pre_asts1": [
                    None,
                    Some(Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 }),
                    None,
                ],
                "allocated_asts1": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 } }),
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                ],
                "pre_asts2": [
                    None,
                    Some(Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 }),
                    None,
                ],
                "allocated_asts2": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 } }),
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                ],
                "pre_asts3": [
                    None,
                    Some(Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 }),
                    None,
                ],
                "allocated_asts3": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 } }),
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                ],
            }
        "#]],
    );
    t(
        "1+1+1",
        expect![[r#"
            {
                "pre_asts": [
                    Some(Literal(`1`)),
                    Some(`+(add)`),
                    Some(Literal(`1`)),
                    Some(`+(add)`),
                    Some(Literal(`1`)),
                ],
                "allocated_asts": [
                    Some(Ast { parent: None, data: Literal(`1`) }),
                    None,
                    Some(Ast { parent: None, data: Literal(`1`) }),
                    None,
                    Some(Ast { parent: None, data: Literal(`1`) }),
                ],
                "pre_asts1": [
                    None,
                    Some(Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 }),
                    None,
                    Some(`+(add)`),
                    Some(Literal(`1`)),
                ],
                "allocated_asts1": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 } }),
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    None,
                    Some(Ast { parent: None, data: Literal(`1`) }),
                ],
                "pre_asts2": [
                    None,
                    None,
                    None,
                    Some(Binary { lopd: #1, lopd_ident: None, opr: `+(add)`, ropd: #4 }),
                    None,
                ],
                "allocated_asts2": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: Some(#3), data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 } }),
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #1, lopd_ident: None, opr: `+(add)`, ropd: #4 } }),
                    Some(Ast { parent: Some(#3), data: Literal(`1`) }),
                ],
                "pre_asts3": [
                    None,
                    None,
                    None,
                    Some(Binary { lopd: #1, lopd_ident: None, opr: `+(add)`, ropd: #4 }),
                    None,
                ],
                "allocated_asts3": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: Some(#3), data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 } }),
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #1, lopd_ident: None, opr: `+(add)`, ropd: #4 } }),
                    Some(Ast { parent: Some(#3), data: Literal(`1`) }),
                ],
            }
        "#]],
    );
    set_debug();
    t(
        "1+1*1",
        expect![[r#"
            {
                "pre_asts": [
                    Some(Literal(`1`)),
                    Some(`+(add)`),
                    Some(Literal(`1`)),
                    Some(`*`),
                    Some(Literal(`1`)),
                ],
                "allocated_asts": [
                    Some(Ast { parent: None, data: Literal(`1`) }),
                    None,
                    Some(Ast { parent: None, data: Literal(`1`) }),
                    None,
                    Some(Ast { parent: None, data: Literal(`1`) }),
                ],
                "pre_asts1": [
                    Some(Literal(`1`)),
                    Some(`+(add)`),
                    None,
                    Some(Binary { lopd: #2, lopd_ident: None, opr: `*`, ropd: #4 }),
                    None,
                ],
                "allocated_asts1": [
                    Some(Ast { parent: None, data: Literal(`1`) }),
                    None,
                    Some(Ast { parent: Some(#3), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #2, lopd_ident: None, opr: `*`, ropd: #4 } }),
                    Some(Ast { parent: Some(#3), data: Literal(`1`) }),
                ],
                "pre_asts2": [
                    None,
                    Some(Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #3 }),
                    None,
                    None,
                    None,
                ],
                "allocated_asts2": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #3 } }),
                    Some(Ast { parent: Some(#3), data: Literal(`1`) }),
                    Some(Ast { parent: Some(#1), data: Binary { lopd: #2, lopd_ident: None, opr: `*`, ropd: #4 } }),
                    Some(Ast { parent: Some(#3), data: Literal(`1`) }),
                ],
                "pre_asts3": [
                    None,
                    Some(Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #3 }),
                    None,
                    None,
                    None,
                ],
                "allocated_asts3": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #3 } }),
                    Some(Ast { parent: Some(#3), data: Literal(`1`) }),
                    Some(Ast { parent: Some(#1), data: Binary { lopd: #2, lopd_ident: None, opr: `*`, ropd: #4 } }),
                    Some(Ast { parent: Some(#3), data: Literal(`1`) }),
                ],
            }
        "#]],
    );
    t(
        "-1",
        expect![[r#"
            {
                "pre_asts": [Some(`-(minus)`), Some(Literal(`1`))],
                "allocated_asts": [None, Some(Ast { parent: None, data: Literal(`1`) })],
                "pre_asts1": [Some(Prefix { opr: `-(minus)`, opd: #1 }), None],
                "allocated_asts1": [
                    Some(Ast { parent: None, data: Prefix { opr: `-(minus)`, opd: #1 } }),
                    Some(Ast { parent: Some(#0), data: Literal(`1`) }),
                ],
                "pre_asts2": [Some(Prefix { opr: `-(minus)`, opd: #1 }), None],
                "allocated_asts2": [
                    Some(Ast { parent: None, data: Prefix { opr: `-(minus)`, opd: #1 } }),
                    Some(Ast { parent: Some(#0), data: Literal(`1`) }),
                ],
                "pre_asts3": [Some(Prefix { opr: `-(minus)`, opd: #1 }), None],
                "allocated_asts3": [
                    Some(Ast { parent: None, data: Prefix { opr: `-(minus)`, opd: #1 } }),
                    Some(Ast { parent: Some(#0), data: Literal(`1`) }),
                ],
            }
        "#]],
    );
    t(
        "1+-1",
        expect![[r#"
            {
                "pre_asts": [Some(Literal(`1`)), Some(`+(add)`), Some(`-(minus)`), Some(Literal(`1`))],
                "allocated_asts": [
                    Some(Ast { parent: None, data: Literal(`1`) }),
                    None,
                    None,
                    Some(Ast { parent: None, data: Literal(`1`) }),
                ],
                "pre_asts1": [
                    Some(Literal(`1`)),
                    Some(`+(add)`),
                    Some(Prefix { opr: `-(minus)`, opd: #3 }),
                    None,
                ],
                "allocated_asts1": [
                    Some(Ast { parent: None, data: Literal(`1`) }),
                    None,
                    Some(Ast { parent: None, data: Prefix { opr: `-(minus)`, opd: #3 } }),
                    Some(Ast { parent: Some(#2), data: Literal(`1`) }),
                ],
                "pre_asts2": [
                    None,
                    Some(Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 }),
                    None,
                    None,
                ],
                "allocated_asts2": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 } }),
                    Some(Ast { parent: Some(#1), data: Prefix { opr: `-(minus)`, opd: #3 } }),
                    Some(Ast { parent: Some(#2), data: Literal(`1`) }),
                ],
                "pre_asts3": [
                    None,
                    Some(Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 }),
                    None,
                    None,
                ],
                "allocated_asts3": [
                    Some(Ast { parent: Some(#1), data: Literal(`1`) }),
                    Some(Ast { parent: None, data: Binary { lopd: #0, lopd_ident: None, opr: `+(add)`, ropd: #2 } }),
                    Some(Ast { parent: Some(#1), data: Prefix { opr: `-(minus)`, opd: #3 } }),
                    Some(Ast { parent: Some(#2), data: Literal(`1`) }),
                ],
            }
        "#]],
    );
}

/// a finite function
pub(crate) fn new_opr_ast(
    nearest_left2: Option2<(Idx, PreAst)>,
    current: Option<PreAst>,
    nearest_right2: Option2<(Idx, PreAst)>,
) -> Option<AstData> {
    let Some(PreAst::Opr(opr)) = current else {
        return None;
    };
    match opr {
        Opr::Prefix(opr) => {
            let Some((opd, PreAst::Ast(_))) = nearest_right2.first() else {
                return None;
            };
            if let Some((_, ast)) = nearest_right2.second() {
                match ast {
                    PreAst::Keyword(_) => (),
                    PreAst::Opr(right_opr) => match right_opr {
                        Opr::Prefix(_) => (),
                        Opr::Binary(right_opr) => {
                            // every binary opr in our small language is left associative, so `<` instead of `<=`
                            if right_opr.precedence() > opr.precedence() {
                                return None;
                            }
                        }
                        Opr::Suffix(right_opr) => {
                            if right_opr.precedence() > opr.precedence() {
                                return None;
                            }
                        }
                    },
                    PreAst::Ast(_) => (),
                    // function call or index takes higher precedence
                    PreAst::LeftDelimiter(_) => return None,
                    PreAst::RightDelimiter(_) => (),
                    PreAst::Separator(_) => (),
                }
            };
            Some(AstData::Prefix { opr, opd })
        }
        Opr::Binary(opr) => {
            let Some((lopd, PreAst::Ast(lopd_ast))) = nearest_left2.first() else {
                return None;
            };
            let lopd_ident = match lopd_ast {
                AstData::Ident(ident) => Some(ident),
                _ => None,
            };
            let Some((ropd, PreAst::Ast(_))) = nearest_right2.first() else {
                return None;
            };
            if let Some((_, ast)) = nearest_left2.second() {
                match ast {
                    PreAst::Keyword(kw) => (),
                    PreAst::Opr(left_opr) => match left_opr {
                        Opr::Prefix(left_opr) => {
                            if left_opr.precedence() >= opr.precedence() {
                                return None;
                            }
                        }
                        Opr::Binary(left_opr) => {
                            /// every binary opr in our small language is left associative, so `>=` instead of `>`
                            if left_opr.precedence() >= opr.precedence() {
                                return None;
                            }
                        }
                        Opr::Suffix(_) => (), // actually this will be a syntax error
                    },
                    PreAst::Ast(
                        AstData::SeparatedItem { .. }
                        | AstData::LetInit { .. }
                        | AstData::Return { .. }
                        | AstData::Assert { .. }
                        | AstData::Defn { .. },
                    ) => (),
                    PreAst::Ast(_) => {
                        if opr != BinaryOpr::LightArrow {
                            return None;
                        }
                    }
                    PreAst::LeftDelimiter(_) => (),
                    PreAst::RightDelimiter(_) => return None,
                    PreAst::Separator(_) => (),
                }
            };
            if let Some((_, ast)) = nearest_right2.second() {
                match ast {
                    PreAst::Keyword(kw) => match kw {
                        Keyword::ELSE => return None,
                        _ => (),
                    },
                    PreAst::Opr(right_opr) => match right_opr {
                        Opr::Prefix(_) => (), // actually this will be a syntax error
                        Opr::Binary(right_opr) => {
                            /// every binary opr in our small language is left associative, so `<` instead of `<=`
                            if right_opr.precedence() > opr.precedence() {
                                return None;
                            }
                        }
                        Opr::Suffix(right_opr) => {
                            if right_opr.precedence() >= opr.precedence() {
                                return None;
                            }
                        }
                    },
                    // function call or index takes higher precedence
                    PreAst::LeftDelimiter(_) => return None,
                    PreAst::RightDelimiter(_) => (),
                    PreAst::Ast(_) => (),
                    PreAst::Separator(_) => (),
                }
            };
            Some(AstData::Binary {
                lopd,
                opr,
                ropd,
                lopd_ident,
            })
        }
        Opr::Suffix(opr) => {
            let Some((opd, PreAst::Ast(_))) = nearest_left2.first() else {
                return None;
            };
            if let Some((_, ast)) = nearest_left2.second() {
                match ast {
                    PreAst::Keyword(_) => (),
                    PreAst::Opr(right_opr) => match right_opr {
                        Opr::Prefix(right_opr) => {
                            if right_opr.precedence() > opr.precedence() {
                                return None;
                            }
                        }
                        Opr::Binary(right_opr) => {
                            /// every binary opr in our small language is left associative, so `<` instead of `<=`
                            if right_opr.precedence() > opr.precedence() {
                                return None;
                            }
                        }
                        Opr::Suffix(_) => (),
                    },
                    PreAst::LeftDelimiter(_) => (),
                    PreAst::RightDelimiter(_) => return None,
                    PreAst::Ast(
                        AstData::SeparatedItem { .. }
                        | AstData::LetInit { .. }
                        | AstData::Return { .. }
                        | AstData::Assert { .. }
                        | AstData::Defn { .. },
                    ) => (),
                    PreAst::Ast(_) => return None,
                    PreAst::Separator(_) => (),
                }
            };
            Some(AstData::Suffix { opr, opd })
        }
    }
}

/// returns sequence of remaining PreAsts and new parent idxs
pub(crate) fn reduce_pre_asts_by_opr(
    pre_asts: Seq<Option<PreAst>>,
    new_asts: Seq<Option<AstData>>,
) -> (Seq<Option<PreAst>>, Seq<Option<Idx>>) {
    let new_asts_nearest_left = new_asts.nearest_left();
    let pre_asts = reduce_pre_ast_by_new_ast.apply(pre_asts, new_asts);
    let (pre_asts, new_parents) = reduce_pre_ast_by_opr_left
        .apply_enumerated(new_asts_nearest_left, pre_asts)
        .decouple();
    let new_asts_nearest_right = new_asts.nearest_right();
    reduce_pre_ast_by_opr_right
        .apply_enumerated(new_asts_nearest_right, pre_asts, new_parents)
        .decouple()
}

fn reduce_pre_ast_by_new_ast(pre_ast: Option<PreAst>, new_ast: Option<AstData>) -> Option<PreAst> {
    if new_ast.is_some() {
        None
    } else {
        pre_ast
    }
}

fn reduce_pre_ast_by_opr_left(
    idx: Idx,
    new_ast_nearest_left: Option<(Idx, AstData)>,
    pre_ast: Option<PreAst>,
) -> (Option<PreAst>, Option<Idx>) {
    let Some(pre_ast) = pre_ast else {
        return (None, None);
    };
    let Some((new_ast_idx, new_ast_data)) = new_ast_nearest_left else {
        return (Some(pre_ast), None);
    };
    match new_ast_data {
        AstData::Binary { ropd: opd, .. } | AstData::Prefix { opd, .. } if opd == idx => {
            (None, Some(new_ast_idx))
        }
        _ => (Some(pre_ast), None),
    }
}

fn reduce_pre_ast_by_opr_right(
    idx: Idx,
    new_ast_nearest_right: Option<(Idx, AstData)>,
    pre_ast: Option<PreAst>,
    new_parent: Option<Idx>,
) -> (Option<PreAst>, Option<Idx>) {
    let Some(pre_ast) = pre_ast else {
        return (None, new_parent);
    };
    if let Some(new_parent) = new_parent {
        return (None, Some(new_parent));
    }
    let Some((new_ast_idx, new_ast_data)) = new_ast_nearest_right else {
        return (Some(pre_ast), None);
    };
    match new_ast_data {
        AstData::Binary { lopd: opd, .. } | AstData::Suffix { opd, .. } if opd == idx => {
            (None, Some(new_ast_idx))
        }
        _ => (Some(pre_ast), None),
    }
}

#[test]
fn reduce_pre_ast_by_opr_right_works() {
    assert_eq!(
        reduce_pre_ast_by_opr_right(
            idx!(0),
            Some((
                idx!(1),
                AstData::Binary {
                    lopd: idx!(0),
                    opr: BinaryOpr::Add,
                    ropd: idx!(2),
                    lopd_ident: None
                }
            )),
            Some(PreAst::Ast(AstData::Literal(Literal::Int(1)))),
            None,
        ),
        (None, Some(idx!(1)))
    );
}

#[test]
fn reduce_n_times_for_opr_works1() {
    t(
        "1",
        0,
        expect![[r#"
            [
                #0 `1`: "1" ✓,
            ]
        "#]],
    );
    t(
        "1+1",
        1,
        expect![[r#"
            [
                #0 `1`: "1",
                #1 `+`: "1 + 1" ✓,
                #2 `1`: "1",
            ]
        "#]],
    );
    t(
        "1+2*3",
        1,
        expect![[r#"
            [
                #0 `1`: "1" ✓,
                #1 `+`: `+`,
                #2 `2`: "2",
                #3 `*`: "2 * 3" ✓,
                #4 `3`: "3",
            ]
        "#]],
    );
    t(
        "1+2*3",
        2,
        expect![[r#"
            [
                #0 `1`: "1",
                #1 `+`: "1 + 2 * 3" ✓,
                #2 `2`: "2",
                #3 `*`: "2 * 3",
                #4 `3`: "3",
            ]
        "#]],
    );
}

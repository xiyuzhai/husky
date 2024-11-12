//! call is a generalized version of normal function call
//!
//! it includes all kinds of delimiters
use token::{
    delimiter::{Delimiter, LCURL, LPAR, RPAR},
    keyword::StmtKeyword,
};

use super::*;

pub(super) fn reduce_by_call(
    pre_asts: Seq<Option<PreAst>>,
    allocated_asts: Seq<Option<Ast>>,
) -> (Seq<Option<PreAst>>, Seq<Option<Ast>>) {
    let pre_asts_nearest_left2 = pre_asts.nearest_left2();
    let pre_asts_nearest_right = pre_asts.nearest_right();
    let new_call_asts =
        new_call_ast.apply_enumerated(pre_asts_nearest_left2, pre_asts_nearest_right);
    let (pre_asts, new_parents) = reduce_pre_asts_by_call(pre_asts, new_call_asts);
    let allocated_asts =
        allocate_asts_and_update_parents(allocated_asts, new_call_asts, new_parents);
    let pre_asts = update_pre_asts_by_new_asts(pre_asts, new_call_asts);
    (pre_asts, allocated_asts)
}

/// a call expr like `f(1)` or `a[2]` is placed over the token `(` or `[`, the left delimiter
///
/// idx is the index of `(`
fn new_call_ast(
    idx: Idx,
    pre_ast_nearest_left2: Option2<(Idx, PreAst)>,
    pre_ast_nearest_right: Option<(Idx, PreAst)>,
) -> Option<AstData> {
    let (caller, PreAst::Ast(caller_ast)) = pre_ast_nearest_left2.first()? else {
        return None;
    };
    let caller_ident = match caller_ast {
        AstData::SeparatedItem { .. }
        | AstData::LetInit { .. }
        | AstData::Return { .. }
        | AstData::Assert { .. }
        | AstData::Defn { .. } => return None,
        AstData::Ident(ident) => Some(ident),
        _ => None,
    };
    let (
        delimited_arguments,
        PreAst::Ast(AstData::Delimited {
            left_delimiter_idx,
            left_delimiter,
            right_delimiter,
        }),
    ) = pre_ast_nearest_right?
    else {
        return None;
    };
    if let Some((_, snd)) = pre_ast_nearest_left2.second() {
        match snd {
            PreAst::Keyword(kw) => match kw {
                Keyword::Defn(kw) => match kw {
                    DefnKeyword::Struct | DefnKeyword::Enum => return None,
                    DefnKeyword::Fn => match left_delimiter.delimiter() {
                        Delimiter::Parenthesis | Delimiter::Box => return None,
                        Delimiter::Curly => (),
                    },
                },
                Keyword::Stmt(kw) => match kw {
                    StmtKeyword::Let => (),
                    StmtKeyword::Return => (),
                    StmtKeyword::Assert => (),
                    StmtKeyword::If => match left_delimiter.delimiter() {
                        Delimiter::Parenthesis | Delimiter::Box => (),
                        Delimiter::Curly => return None,
                    },
                    StmtKeyword::Else => return None,
                },
            },
            PreAst::Opr(opr) => match opr {
                Opr::Prefix(_) | Opr::Binary(_) => match left_delimiter.delimiter() {
                    Delimiter::Parenthesis | Delimiter::Box => (),
                    Delimiter::Curly => return None,
                },
                Opr::Suffix(_) => return None,
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
            PreAst::Ast(snd_ast) => {
                if let AstData::Ident(_) = snd_ast
                    && left_delimiter == LCURL
                {
                    match caller_ast {
                        AstData::Binary {
                            opr: BinaryOpr::LightArrow,
                            ..
                        }
                        | AstData::Delimited {
                            left_delimiter: LPAR,
                            right_delimiter: RPAR,
                            ..
                        } => (),
                        _ => return None,
                    }
                } else {
                    return None;
                }
            }
            PreAst::Separator(_) => (),
        }
    }
    if left_delimiter_idx != idx {
        return None;
    }
    Some(AstData::Call {
        caller,
        caller_ident,
        delimited_arguments,
        left_delimiter,
        right_delimiter,
    })
}

fn reduce_pre_asts_by_call(
    pre_asts: Seq<Option<PreAst>>,
    new_asts: Seq<Option<AstData>>,
) -> (Seq<Option<PreAst>>, Seq<Option<Idx>>) {
    let new_asts_nearest_left = new_asts.nearest_left();
    let new_asts_nearest_right = new_asts.nearest_right();
    reduce_pre_ast_by_call
        .apply_enumerated(new_asts_nearest_left, new_asts_nearest_right, pre_asts)
        .decouple()
}

fn reduce_pre_ast_by_call(
    idx: Idx,
    new_ast_nearest_left: Option<(Idx, AstData)>,
    new_ast_nearest_right: Option<(Idx, AstData)>,
    pre_ast: Option<PreAst>,
) -> (Option<PreAst>, Option<Idx>) {
    if let Some((
        idx1,
        AstData::Call {
            delimited_arguments,
            ..
        },
    )) = new_ast_nearest_left
        && delimited_arguments == idx
    {
        (None, Some(idx1))
    } else if let Some((idx1, AstData::Call { caller, .. })) = new_ast_nearest_right
        && caller == idx
    {
        (None, Some(idx1))
    } else {
        (pre_ast, None)
    }
}

#[test]
fn reduce_n_times_for_call_works1() {
    t(
        "f()",
        2,
        expect![[r#"
            [
                #0 `f`: "f",
                #1 `(`: "f()" ✓,
                #2 `)`: "()",
            ]
        "#]],
    );
    t(
        "f()()",
        2,
        expect![[r#"
            [
                #0 `f`: "f",
                #1 `(`: "f()",
                #2 `)`: "()",
                #3 `(`: "f()()" ✓,
                #4 `)`: "()",
            ]
        "#]],
    );
    t(
        "f()+1",
        2,
        expect![[r#"
            [
                #0 `f`: "f",
                #1 `(`: "f()",
                #2 `)`: "()",
                #3 `+`: "f() + 1" ✓,
                #4 `1`: "1",
            ]
        "#]],
    );
    t(
        "A {}",
        2,
        expect![[r#"
            [
                #0 `A`: "A",
                #1 `{`: "A {}" ✓,
                #2 `}`: "{}",
            ]
        "#]],
    );
}

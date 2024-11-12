use ident::Ident;

use super::*;
use crate::{
    token::{delimiter::*, *},
    *,
};

pub fn show_asts(tokens: Seq<Token>, asts: Seq<Option<Ast>>) -> Vec<AstOut> {
    let tokens = tokens.data();
    let asts = asts.data();
    let len = tokens.len();
    debug_assert_eq!(len, asts.len());
    let mut outs: Vec<AstOut> = (0..len)
        .into_iter()
        .map(|i| AstOut {
            idx: idx!(i),
            token: tokens[i],
            is_root: match asts[i] {
                Some(ast) => ast.parent.is_none(),
                None => false,
            },
            ast: "".into(),
        })
        .collect();
    for i in 0..len {
        calc_ast_repr(tokens, asts, idx!(i), &mut outs)
    }
    outs
}

pub struct AstOut {
    idx: Idx,
    token: Token,
    is_root: bool,
    ast: String,
}

impl std::fmt::Debug for AstOut {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.is_root {
            true => {
                if self.ast.is_empty() {
                    f.write_fmt(format_args!(
                        "{:?} `{}`: `{}` ✓",
                        self.idx,
                        self.token.repr_short(),
                        self.token.repr_short()
                    ))
                } else {
                    f.write_fmt(format_args!(
                        "{:?} `{}`: \"{}\" ✓",
                        self.idx,
                        self.token.repr_short(),
                        self.ast
                    ))
                }
            }
            false => {
                if self.ast.is_empty() {
                    f.write_fmt(format_args!(
                        "{:?} `{}`: `{}`",
                        self.idx,
                        self.token.repr_short(),
                        self.token.repr_short()
                    ))
                } else {
                    f.write_fmt(format_args!(
                        "{:?} `{}`: \"{}\"",
                        self.idx,
                        self.token.repr_short(),
                        self.ast
                    ))
                }
            }
        }
    }
}

fn calc_ast_repr(tokens: &[Token], asts: &[Option<Ast>], idx: Idx, outs: &mut Vec<AstOut>) {
    let i = idx.index();
    let Some(ast) = asts[i] else { return };
    if outs[i].ast.len() > 0 {
        return;
    }
    let repr = match ast.data {
        AstData::Literal(lit) => lit.repr(),
        AstData::Ident(ident) => ident.repr().to_string(),
        AstData::Prefix { opr, opd } => {
            calc_ast_repr(tokens, asts, opd, outs);
            format!("{}{}", opr.repr_short(), outs[opd.index()].ast)
        }
        AstData::Binary {
            lopd,
            opr,
            ropd,
            lopd_ident,
        } => {
            calc_ast_repr(tokens, asts, lopd, outs);
            calc_ast_repr(tokens, asts, ropd, outs);
            format!(
                "{} {} {}",
                outs[lopd.index()].ast,
                opr.repr_short(),
                outs[ropd.index()].ast
            )
        }
        AstData::Suffix { opd, opr } => {
            calc_ast_repr(tokens, asts, opd, outs);
            format!("{}{}", outs[opd.index()].ast, opr.repr())
        }
        AstData::Delimited {
            left_delimiter_idx,
            left_delimiter,
            right_delimiter,
        } => {
            let mut result = String::new();
            let number_of_items = asts
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(i, ast)| (ast?.parent == Some(idx)).then_some((i, ast?)))
                .count();
            if number_of_items > 0 {
                result += left_delimiter.repr2();
                for (jj, (j, ast)) in asts
                    .iter()
                    .copied()
                    .enumerate()
                    .filter_map(|(i, ast)| Some((i, ast?)))
                    .enumerate()
                {
                    if ast.parent == Some(idx) {
                        calc_ast_repr(tokens, asts, idx!(j), outs);
                        result += &outs[j].ast;
                    }
                }
                result += right_delimiter.repr2();
            } else {
                result += left_delimiter.repr();
                result += right_delimiter.repr();
            }
            result
        }
        AstData::SeparatedItem { content, separator } => {
            let mut result = String::new();
            if let Some(content) = content {
                calc_ast_repr(tokens, asts, content, outs);
                result += &outs[content.index()].ast;
            }
            result += separator.repr2();
            result
        }
        AstData::Call {
            caller,
            left_delimiter,
            delimited_arguments,
            ..
        } => {
            calc_ast_repr(tokens, asts, caller, outs);
            calc_ast_repr(tokens, asts, delimited_arguments, outs);
            format!(
                "{}{}{}",
                outs[caller.index()].ast,
                match left_delimiter.delimiter() {
                    Delimiter::Parenthesis | Delimiter::Box => "",
                    Delimiter::Curly => " ",
                },
                outs[delimited_arguments.index()].ast
            )
        }
        AstData::Defn {
            keyword,
            ident_idx,
            ident,
            content,
        } => {
            calc_ast_repr(tokens, asts, content, outs);
            format!(
                "{} {}{}{}",
                keyword.repr(),
                ident.repr(),
                match keyword {
                    DefnKeyword::Struct | DefnKeyword::Enum => " ",
                    DefnKeyword::Fn => "",
                },
                outs[content.index()].ast
            )
        }
        AstData::LetInit { expr, .. } => {
            calc_ast_repr(tokens, asts, expr, outs);
            format!("let {}", outs[expr.index()].ast,)
        }
        AstData::Return { result } => {
            calc_ast_repr(tokens, asts, result, outs);
            format!("return {}", outs[result.index()].ast,)
        }
        AstData::Assert { condition } => {
            calc_ast_repr(tokens, asts, condition, outs);
            format!("assert {}", outs[condition.index()].ast,)
        }
        AstData::If { condition, body } => {
            calc_ast_repr(tokens, asts, condition, outs);
            calc_ast_repr(tokens, asts, body, outs);
            format!(
                "if {} {}",
                outs[condition.index()].ast,
                outs[body.index()].ast
            )
        }
        AstData::Else { if_stmt, body } => {
            calc_ast_repr(tokens, asts, if_stmt, outs);
            calc_ast_repr(tokens, asts, body, outs);
            format!(
                "{} else {}",
                outs[if_stmt.index()].ast,
                outs[body.index()].ast
            )
        }
    };
    outs[i].ast = repr
}

#[test]
fn show_asts_works() {
    expect![[r#"
        [
            #0 `hello`: "hello" ✓,
        ]
    "#]]
    .assert_debug_eq(&show_asts(
        seq![Token::Ident(Ident::new("hello"))],
        seq![Some(Ast {
            parent: None,
            data: AstData::Ident(Ident::new("hello"))
        })],
    ));
    expect![[r#"
        [
            #0 `+`: "+hello" ✓,
            #1 `hello`: "hello",
        ]
    "#]]
    .assert_debug_eq(&show_asts(
        seq![Token::Opr(Opr::PLUS), Token::Ident(Ident::new("hello"))],
        seq![
            Some(Ast {
                parent: None,
                data: AstData::Prefix {
                    opr: PrefixOpr::Plus,
                    opd: idx!(1)
                }
            }),
            Some(Ast {
                parent: Some(idx!(0)),
                data: AstData::Ident(Ident::new("hello"))
            })
        ],
    ));
    expect![[r#"
        [
            #0 `1`: "1",
            #1 `+`: "1 + 1" ✓,
            #2 `1`: "1",
        ]
    "#]]
    .assert_debug_eq(&show_asts(
        seq![
            Token::Literal(Literal::Int(1)),
            Token::Opr(Opr::ADD),
            Token::Literal(Literal::Int(1))
        ],
        seq![
            Some(Ast {
                parent: Some(idx!(1)),
                data: AstData::Literal(Literal::Int(1))
            }),
            Some(Ast {
                parent: None,
                data: AstData::Binary {
                    lopd: idx!(0),
                    opr: BinaryOpr::Add,
                    ropd: idx!(2),
                    lopd_ident: None
                }
            }),
            Some(Ast {
                parent: Some(idx!(1)),
                data: AstData::Literal(Literal::Int(1))
            })
        ],
    ));
    expect![[r#"
        [
            #0 `(`: `(`,
            #1 `1`: "1",
            #2 `,`: "1, ",
            #3 `1`: "1",
            #4 `)`: "(1, 1)" ✓,
        ]
    "#]]
    .assert_debug_eq(&show_asts(
        seq![
            Token::LeftDelimiter(LPAR),
            Token::Literal(Literal::Int(1)),
            Token::Separator(Separator::Comma),
            Token::Literal(Literal::Int(1)),
            Token::RightDelimiter(RPAR),
        ],
        seq![
            None,
            Some(Ast {
                parent: Some(idx!(2)),
                data: AstData::Literal(Literal::Int(1))
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
                data: AstData::Literal(Literal::Int(1))
            }),
            Some(Ast {
                parent: None,
                data: AstData::Delimited {
                    left_delimiter_idx: idx!(0),
                    left_delimiter: LPAR,
                    right_delimiter: RPAR,
                }
            })
        ],
    ));
}

pub fn show_asts_mapped_values<T>(
    tokens: Seq<Token>,
    asts: Seq<Option<Ast>>,
    mapped: Seq<Option<T>>,
) -> Vec<AstOutMappedValue>
where
    T: std::fmt::Debug + Send + Sync + Copy + 'static,
{
    let outs = show_asts(tokens, asts);
    outs.into_iter()
        .zip(mapped.data())
        .enumerate()
        .map(|(i, (ast_out, mapped))| AstOutMappedValue {
            ast_out,
            mapped_value: match mapped {
                Some(mapped) => Some(format!("{:?}", mapped)),
                None => None,
            },
        })
        .collect()
}

pub struct AstOutMappedValue {
    ast_out: AstOut,
    mapped_value: Option<String>,
}

impl std::fmt::Debug for AstOutMappedValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.mapped_value {
            Some(ref value) => f.write_fmt(format_args!("{:?} → {}", self.ast_out, value)),
            None => f.write_fmt(format_args!("{:?}", self.ast_out)),
        }
    }
}

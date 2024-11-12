use crate::*;
use delimiter::Delimiter;
use ident::Ident;
use scope::Scope;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    LetStmt {
        pattern: Idx,
        initial_value: Option<Idx>,
    },
    LetStmtInner {
        pattern: Idx,
        initial_value: Idx,
    },
    LetStmtIdent,
    LetStmtTypedVariables {
        variables: Idx,
        ty: Idx,
    },
    StructDefn(Ident),
    EnumDefn(Ident),
    FnDefn(Ident),
    FnDefnCallForm {
        fn_ident: Ident,
        scope: Scope,
    },
    FnParameters {
        fn_ident: Ident,
        has_return_ty: bool,
        scope: Scope,
    },
    FnParametersAndReturnType {
        fn_ident: Ident,
        parameters: Idx,
        scope: Scope,
        return_ty: Idx,
    },
    FnBody(Ident),
    StructFields(Ident),
    FnParameter {
        fn_ident: Ident,
        rank: Rank,
        ty: Idx,
        fn_ident_idx: Idx,
        scope: Scope,
    },
    FnParameterIdent {
        scope: Scope,
    },
    FnParameterSeparated {
        fn_ident: Ident,
        rank: Rank,
        scope: Scope,
    },
    FnParameterType {
        fn_ident: Ident,
        rank: Rank,
    },
    FnOutputType {
        fn_ident: Ident,
    },
    StructField {
        ty_ident: Ident,
        field_ident: Ident,
        ty_idx: Idx,
    },
    StructFieldType {
        ty_ident: Ident,
        field_ident: Ident,
    },
    TypeArgument,
    TypeArguments,
    StructFieldSeparated(Ident),
    LetStmtVariablesType,
    LetStmtVariables,
}

impl Ast {
    fn role(self) -> Option<Role> {
        match self.data {
            AstData::LetInit {
                expr,
                pattern,
                initial_value,
            } => Some(Role::LetStmt {
                pattern,
                initial_value,
            }),
            AstData::Defn {
                keyword,
                ident_idx,
                ident,
                content,
            } => Some(match keyword {
                DefnKeyword::Struct => Role::StructDefn(ident),
                DefnKeyword::Enum => Role::EnumDefn(ident),
                DefnKeyword::Fn => Role::FnDefn(ident),
            }),
            _ => None,
        }
    }
}

pub fn calc_roles(
    asts: Seq<Option<Ast>>,
    scopes: Seq<Option<Scope>>,
    n: usize,
) -> Seq<Option<Role>> {
    let mut roles: Seq<Option<Role>> = asts.map(|ast| ast?.role());
    let ranks = calc_ranks(asts);
    for _ in 0..n {
        let parent_roles = parent_queries(asts, roles);
        roles = calc_roles_step(asts, parent_roles, roles, ranks, scopes);
    }
    roles
}

fn calc_roles_step(
    asts: Seq<Option<Ast>>,
    parent_roles: Seq<Option<Role>>,
    roles: Seq<Option<Role>>,
    ranks: Seq<Option<Rank>>,
    scopes: Seq<Option<Scope>>,
) -> Seq<Option<Role>> {
    calc_role_step.apply_enumerated(asts, parent_roles, roles, ranks, scopes)
}

fn calc_role_step(
    idx: Idx,
    ast: Option<Ast>,
    parent_role: Option<Role>,
    role: Option<Role>,
    rank: Option<Rank>,
    scope: Option<Scope>,
) -> Option<Role> {
    if let Some(role) = role {
        return Some(role);
    }
    let ast = ast?;
    if let Some(role) = ast.role() {
        return Some(role);
    }
    match parent_role? {
        Role::LetStmt {
            pattern,
            initial_value,
        } => match ast.data {
            AstData::Ident(ident) if idx == pattern => Some(Role::LetStmtIdent),
            AstData::Binary {
                lopd,
                opr: BinaryOpr::Assign,
                ropd,
                lopd_ident,
            } if lopd == pattern => Some(Role::LetStmtInner {
                pattern,
                initial_value: ropd,
            }),
            _ => None,
        },
        Role::LetStmtInner {
            pattern,
            initial_value,
        } => {
            if idx == pattern {
                match ast.data {
                    AstData::Ident(ident) => Some(Role::LetStmtIdent),
                    AstData::Binary {
                        lopd,
                        lopd_ident,
                        opr,
                        ropd,
                    } => Some(Role::LetStmtTypedVariables {
                        variables: lopd,
                        ty: ropd,
                    }),
                    _ => todo!(),
                }
            } else {
                None
            }
        }
        Role::LetStmtIdent => todo!(),
        Role::FnParameterIdent { scope } => todo!(),
        Role::StructDefn(ident) => match ast.data {
            AstData::Literal(_) => todo!(),
            AstData::Ident(_) => None,
            AstData::Prefix { opr, opd } => todo!(),
            AstData::Binary {
                lopd,
                opr,
                ropd,
                lopd_ident,
            } => todo!(),
            AstData::Suffix { opd, opr } => todo!(),
            AstData::Delimited {
                left_delimiter_idx,
                left_delimiter,
                right_delimiter,
            } => Some(Role::StructFields(ident)),
            AstData::SeparatedItem { content, separator } => todo!(),
            AstData::Call { .. } => todo!(),
            AstData::LetInit {
                expr,
                pattern,
                initial_value,
            } => todo!(),
            AstData::Return { result } => todo!(),
            AstData::Assert { condition } => todo!(),
            AstData::If { condition, body } => todo!(),
            AstData::Else { if_stmt, body } => todo!(),
            AstData::Defn {
                keyword,
                ident_idx,
                ident,
                content,
            } => todo!(),
        },
        Role::EnumDefn(_) => None, // ad hoc
        Role::FnDefn(fn_ident) => match ast.data {
            AstData::Literal(_) => todo!(),
            AstData::Ident(_) => None,
            AstData::Prefix { opr, opd } => todo!(),
            AstData::Binary {
                lopd,
                opr,
                ropd,
                lopd_ident,
            } => todo!(),
            AstData::Suffix { opd, opr } => todo!(),
            AstData::Delimited {
                left_delimiter_idx,
                left_delimiter,
                right_delimiter,
            } => todo!(),
            AstData::SeparatedItem { content, separator } => todo!(),
            AstData::Call {
                delimited_arguments,
                ..
            } => Some(Role::FnDefnCallForm {
                fn_ident,
                scope: match scope {
                    Some(scope) => scope.append(delimited_arguments),
                    None => Scope::new(delimited_arguments),
                },
            }),
            AstData::LetInit {
                expr,
                pattern,
                initial_value,
            } => todo!(),
            AstData::Return { result } => todo!(),
            AstData::Assert { condition } => todo!(),
            AstData::If { condition, body } => todo!(),
            AstData::Else { if_stmt, body } => todo!(),
            AstData::Defn {
                keyword,
                ident_idx,
                ident,
                content,
            } => todo!(),
        },
        Role::FnDefnCallForm { fn_ident, scope } => match ast.data {
            AstData::Literal(_) => todo!(),
            AstData::Ident(_) => todo!(),
            AstData::Prefix { opr, opd } => todo!(),
            AstData::Binary {
                lopd,
                opr,
                ropd,
                lopd_ident,
            } => {
                if opr == BinaryOpr::LightArrow {
                    Some(Role::FnParametersAndReturnType {
                        fn_ident,
                        parameters: lopd,
                        return_ty: ropd,
                        scope,
                    })
                } else {
                    unreachable!()
                }
            }
            AstData::Suffix { opd, opr } => todo!(),
            AstData::Delimited {
                left_delimiter_idx,
                left_delimiter,
                right_delimiter,
            } => match left_delimiter.delimiter() {
                Delimiter::Parenthesis => Some(Role::FnParameters {
                    fn_ident,
                    has_return_ty: false,
                    scope,
                }),
                Delimiter::Box => todo!(),
                Delimiter::Curly => Some(Role::FnBody(fn_ident)),
            },
            AstData::SeparatedItem { content, separator } => todo!(),
            AstData::Call { .. } => todo!(),
            AstData::LetInit {
                expr,
                pattern,
                initial_value,
            } => todo!(),
            AstData::Return { result } => todo!(),
            AstData::Assert { condition } => todo!(),
            AstData::If { condition, body } => todo!(),
            AstData::Else { if_stmt, body } => todo!(),
            AstData::Defn {
                keyword,
                ident_idx,
                ident,
                content,
            } => todo!(),
        },
        Role::FnParameters {
            fn_ident, scope, ..
        } => match ast.data {
            AstData::Binary {
                lopd,
                opr,
                ropd,
                lopd_ident,
            } => {
                if opr == BinaryOpr::TypeIs {
                    Some(Role::FnParameter {
                        fn_ident,
                        fn_ident_idx: lopd,
                        rank: rank.unwrap(),
                        ty: ropd,
                        scope,
                    })
                } else {
                    unreachable!()
                }
            }
            AstData::SeparatedItem { .. } => Some(Role::FnParameterSeparated {
                fn_ident,
                rank: rank.unwrap(),
                scope,
            }),
            _ => unreachable!(),
        },
        Role::FnBody(_) => None,
        Role::StructFields(ty_ident) => match ast.data {
            AstData::Binary {
                lopd,
                opr,
                ropd,
                lopd_ident,
            } => {
                assert_eq!(opr, BinaryOpr::TypeIs);
                Some(Role::StructField {
                    ty_ident,
                    field_ident: lopd_ident.unwrap(),
                    ty_idx: ropd,
                })
            }
            AstData::SeparatedItem { content, separator } => {
                Some(Role::StructFieldSeparated(ty_ident))
            }
            _ => None,
        },
        Role::FnParameter {
            fn_ident,
            fn_ident_idx,
            rank,
            ty,
            scope,
            ..
        } => {
            if idx == ty {
                Some(Role::FnParameterType { fn_ident, rank })
            } else if idx == fn_ident_idx {
                Some(Role::FnParameterIdent { scope })
            } else {
                None
            }
        }
        Role::FnParameterSeparated {
            fn_ident,
            rank,
            scope,
        } => match ast.data {
            AstData::Binary {
                lopd,
                opr,
                ropd,
                lopd_ident,
            } => {
                if opr == BinaryOpr::TypeIs {
                    Some(Role::FnParameter {
                        fn_ident,
                        fn_ident_idx: lopd,
                        rank,
                        ty: ropd,
                        scope,
                    })
                } else {
                    unreachable!()
                }
            }
            _ => unreachable!(),
        },
        Role::StructField {
            ty_ident,
            field_ident,
            ty_idx,
        } => {
            if idx == ty_idx {
                Some(Role::StructFieldType {
                    ty_ident,
                    field_ident,
                })
            } else {
                None
            }
        }
        Role::StructFieldSeparated(ty_ident) => match ast.data {
            AstData::Binary {
                lopd,
                opr,
                ropd,
                lopd_ident,
            } => {
                assert_eq!(opr, BinaryOpr::TypeIs);
                Some(Role::StructField {
                    ty_ident,
                    field_ident: lopd_ident.unwrap(),
                    ty_idx: ropd,
                })
            }
            _ => unreachable!(),
        },
        Role::FnParameterType { .. } | Role::StructFieldType { .. } | Role::TypeArgument => {
            match ast.data {
                AstData::Delimited {
                    left_delimiter_idx,
                    left_delimiter,
                    right_delimiter,
                } => Some(Role::TypeArguments),
                _ => None,
            }
        }
        Role::TypeArguments => match ast.data {
            AstData::Ident(_) => Some(Role::TypeArgument),
            AstData::Delimited {
                left_delimiter_idx,
                left_delimiter,
                right_delimiter,
            } => todo!(),
            AstData::SeparatedItem { content, separator } => todo!(),
            AstData::Call {
                caller,
                caller_ident,
                left_delimiter,
                right_delimiter,
                delimited_arguments,
            } => todo!(),
            _ => None,
        },
        Role::FnParametersAndReturnType {
            fn_ident,
            parameters,
            return_ty,
            scope,
        } => {
            if idx == parameters {
                Some(Role::FnParameters {
                    fn_ident,
                    has_return_ty: true,
                    scope,
                })
            } else if idx == return_ty {
                Some(Role::FnOutputType { fn_ident })
            } else {
                unreachable!()
            }
        }
        Role::FnOutputType { fn_ident } => todo!(),
        Role::LetStmtTypedVariables { variables, ty } => {
            if idx == variables {
                Some(Role::LetStmtVariables)
            } else if idx == ty {
                Some(Role::LetStmtVariablesType)
            } else {
                unreachable!()
            }
        }
        Role::LetStmtVariablesType => todo!(),
        Role::LetStmtVariables => todo!(),
    }
}

#[cfg(test)]
fn t(input: &str, expect: Expect) {
    use scope::infer_scopes;

    let (tokens, pre_asts, asts) =
        calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
    let scopes = infer_scopes(asts, 10);
    let roles = calc_roles(asts, scopes, 10);
    expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, roles))
}

#[test]
fn calc_roles_works() {
    t(
        "",
        expect![[r#"
        []
    "#]],
    );
    t(
        "struct A {}",
        expect![[r#"
            [
                #0 `struct`: "struct A {}" ✓ → StructDefn(`A`),
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `}`: "{}" → StructFields(`A`),
            ]
        "#]],
    );
    t(
        "struct A { x: i32 }",
        expect![[r#"
            [
                #0 `struct`: "struct A { x : i32 }" ✓ → StructDefn(`A`),
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `x`: "x",
                #4 `:`: "x : i32" → StructField { ty_ident: `A`, field_ident: `x`, ty_idx: #5 },
                #5 `i32`: "i32" → StructFieldType { ty_ident: `A`, field_ident: `x` },
                #6 `}`: "{ x : i32 }" → StructFields(`A`),
            ]
        "#]],
    );
    t(
        "struct A { x: i32, y: Vec[i32] }",
        expect![[r#"
            [
                #0 `struct`: "struct A { x : i32, y : Vec[i32] }" ✓ → StructDefn(`A`),
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `x`: "x",
                #4 `:`: "x : i32" → StructField { ty_ident: `A`, field_ident: `x`, ty_idx: #5 },
                #5 `i32`: "i32" → StructFieldType { ty_ident: `A`, field_ident: `x` },
                #6 `,`: "x : i32, " → StructFieldSeparated(`A`),
                #7 `y`: "y",
                #8 `:`: "y : Vec[i32]" → StructField { ty_ident: `A`, field_ident: `y`, ty_idx: #10 },
                #9 `Vec`: "Vec",
                #10 `[`: "Vec[i32]" → StructFieldType { ty_ident: `A`, field_ident: `y` },
                #11 `i32`: "i32" → TypeArgument,
                #12 `]`: "[i32]" → TypeArguments,
                #13 `}`: "{ x : i32, y : Vec[i32] }" → StructFields(`A`),
            ]
        "#]],
    );
    t(
        "fn f(x: i32) {}",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : i32) {}" ✓ → FnDefn(`f`),
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x" → FnParameterIdent { scope: `::8` },
                #4 `:`: "x : i32" → FnParameter { fn_ident: `f`, rank: Rank(0), ty: #5, fn_ident_idx: #3, scope: `::8` },
                #5 `i32`: "i32" → FnParameterType { fn_ident: `f`, rank: Rank(0) },
                #6 `)`: "(x : i32)" → FnParameters { fn_ident: `f`, has_return_ty: false, scope: `::8` },
                #7 `{`: "(x : i32) {}" → FnDefnCallForm { fn_ident: `f`, scope: `::8` },
                #8 `}`: "{}" → FnBody(`f`),
            ]
        "#]],
    );
    t(
        "fn f(x: i32) -> i32 { return 1; }",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : i32) -> i32 { return 1;  }" ✓ → FnDefn(`f`),
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x" → FnParameterIdent { scope: `::13` },
                #4 `:`: "x : i32" → FnParameter { fn_ident: `f`, rank: Rank(0), ty: #5, fn_ident_idx: #3, scope: `::13` },
                #5 `i32`: "i32" → FnParameterType { fn_ident: `f`, rank: Rank(0) },
                #6 `)`: "(x : i32)" → FnParameters { fn_ident: `f`, has_return_ty: true, scope: `::13` },
                #7 `->`: "(x : i32) -> i32" → FnParametersAndReturnType { fn_ident: `f`, parameters: #6, scope: `::13`, return_ty: #8 },
                #8 `i32`: "i32" → FnOutputType { fn_ident: `f` },
                #9 `{`: "(x : i32) -> i32 { return 1;  }" → FnDefnCallForm { fn_ident: `f`, scope: `::13` },
                #10 `return`: "return 1",
                #11 `1`: "1",
                #12 `;`: "return 1; ",
                #13 `}`: "{ return 1;  }" → FnBody(`f`),
            ]
        "#]],
    );
}

#[test]
fn populate_roles_n_times_works1() {
    t(
        "",
        expect![[r#"
        []
    "#]],
    );
}

#[test]
fn populate_roles_n_times_for_struct_works() {
    t(
        "struct A {}",
        expect![[r#"
            [
                #0 `struct`: "struct A {}" ✓ → StructDefn(`A`),
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `}`: "{}" → StructFields(`A`),
            ]
        "#]],
    );
    t(
        "struct A { a: i32 }",
        expect![[r#"
            [
                #0 `struct`: "struct A { a : i32 }" ✓ → StructDefn(`A`),
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `a`: "a",
                #4 `:`: "a : i32" → StructField { ty_ident: `A`, field_ident: `a`, ty_idx: #5 },
                #5 `i32`: "i32" → StructFieldType { ty_ident: `A`, field_ident: `a` },
                #6 `}`: "{ a : i32 }" → StructFields(`A`),
            ]
        "#]],
    );
}

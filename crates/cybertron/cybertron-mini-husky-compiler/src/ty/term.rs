use delimiter::{LBOX, RBOX};

use super::*;

pub fn calc_ty_terms(
    asts: Seq<Option<Ast>>,
    roles: Seq<Option<Role>>,
    n: usize,
) -> Seq<Option<Type>> {
    let mut ty_terms: Seq<Option<Type>> = asts.map(|_| None);
    for _ in 0..n {
        ty_terms = calc_ty_terms_step(asts, roles, ty_terms);
    }
    ty_terms
}

fn calc_ty_terms_step(
    asts: Seq<Option<Ast>>,
    roles: Seq<Option<Role>>,
    ty_terms: Seq<Option<Type>>,
) -> Seq<Option<Type>> {
    let argument_ty_terms = find_argument_ty_terms(asts, roles, ty_terms);
    calc_ty_term_step.apply(asts, roles, argument_ty_terms)
}

fn find_argument_ty_terms(
    asts: Seq<Option<Ast>>,
    roles: Seq<Option<Role>>,
    ty_terms: Seq<Option<Type>>,
) -> Seq<Option<Type>> {
    ty_terms
        .first_filtered_by_attention(
            delimited_arguments_idx.apply(asts, roles),
            asts,
            |delimited_arguments_idx, ast| {
                let Some(ast) = ast else { return false };
                let Some(delimited_arguments_idx) = delimited_arguments_idx else {
                    return false;
                };
                ast.parent == Some(delimited_arguments_idx)
            },
        )
        .map(Option::flatten)
}

fn delimited_arguments_idx(ast: Option<Ast>, role: Option<Role>) -> Option<Idx> {
    if !is_ty_role(role?) {
        return None;
    };
    match ast?.data {
        AstData::Call {
            caller,
            caller_ident,
            left_delimiter,
            right_delimiter,
            delimited_arguments,
        } => Some(delimited_arguments),
        _ => None,
    }
}

fn calc_ty_term_step(
    ast: Option<Ast>,
    role: Option<Role>,
    argument_ty_term: Option<Type>,
) -> Option<Type> {
    if !is_ty_role(role?) {
        return None;
    };
    match ast?.data {
        AstData::Ident(ident) => Some(Type::new_ident(ident)),
        AstData::Call {
            caller_ident: Some(caller_ident),
            left_delimiter: LBOX,
            right_delimiter: RBOX,
            delimited_arguments,
            ..
        } => match caller_ident.repr() {
            "Option" => Some(argument_ty_term?.in_option()),
            "Vec" => Some(argument_ty_term?.in_vec()),
            _ => None,
        },
        AstData::Delimited {
            left_delimiter: LBOX,
            right_delimiter: RBOX,
            ..
        } => argument_ty_term,
        _ => None,
    }
}

fn is_ty_role(role: Role) -> bool {
    match role {
        Role::FnParameterType { .. }
        | Role::FnOutputType { .. }
        | Role::StructFieldType { .. }
        | Role::LetStmtVariablesType
        | Role::TypeArgument => true,
        _ => false,
    }
}

#[cfg(test)]
fn t(input: &str, expect: Expect) {
    use scope::infer_scopes;

    let (tokens, pre_asts, asts) =
        calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
    let scopes = infer_scopes(asts, 10);
    let roles = calc_roles(asts, scopes, 10);
    let ty_terms = calc_ty_terms(asts, roles, 10);
    expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, ty_terms));
}

#[test]
fn calc_ty_terms_works() {
    t(
        "",
        expect![[r#"
        []
    "#]],
    );
    t(
        "fn f(x: i32) {}",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : i32) {}" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x",
                #4 `:`: "x : i32",
                #5 `i32`: "i32" → `i32`,
                #6 `)`: "(x : i32)",
                #7 `{`: "(x : i32) {}",
                #8 `}`: "{}",
            ]
        "#]],
    );
    t(
        "struct A { x: i32 }",
        expect![[r#"
            [
                #0 `struct`: "struct A { x : i32 }" ✓,
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `x`: "x",
                #4 `:`: "x : i32",
                #5 `i32`: "i32" → `i32`,
                #6 `}`: "{ x : i32 }",
            ]
        "#]],
    );
    t(
        "struct A { x: Option[i32] }",
        expect![[r#"
            [
                #0 `struct`: "struct A { x : Option[i32] }" ✓,
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `x`: "x",
                #4 `:`: "x : Option[i32]",
                #5 `Option`: "Option",
                #6 `[`: "Option[i32]" → `Option[i32]`,
                #7 `i32`: "i32" → `i32`,
                #8 `]`: "[i32]",
                #9 `}`: "{ x : Option[i32] }",
            ]
        "#]],
    );
}

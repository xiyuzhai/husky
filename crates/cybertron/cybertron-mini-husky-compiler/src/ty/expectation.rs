use super::*;
use signature::{TypeSignature, TypeSignatureKey};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TypeExpectation {
    pub ty: Type,
    pub source: TypeExpectationSource,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TypeExpectationSource {
    CallArgument { caller_ident: Ident, rank: Rank },
}

pub fn calc_ty_expectations(
    asts: Seq<Option<Ast>>,
    ranks: Seq<Option<Rank>>,
    ty_signatures: Seq<Option<TypeSignature>>,
) -> Seq<Option<TypeExpectation>> {
    let parent_asts = asts.index(asts.map(|ast| ast?.parent)).map(Option::flatten);
    let grandparent_asts = asts
        .index(parent_asts.map(|parent_ast| parent_ast?.parent))
        .map(Option::flatten);
    let ty_expectation_sources = calc_ty_expectation_source.apply(grandparent_asts, ranks);
    let retrieved_ty_signatures = ty_signatures
        .first_filtered_by_attention(
            ty_expectation_sources,
            ty_signatures,
            |ty_expection_source, ty_signature| {
                let Some(type_expectation_source) = ty_expection_source else {
                    return false;
                };
                let Some(type_signature) = ty_signature else {
                    return false;
                };
                match (type_expectation_source, type_signature.key()) {
                    (
                        TypeExpectationSource::CallArgument {
                            caller_ident,
                            rank: rank0,
                        },
                        TypeSignatureKey::FnParameter {
                            fn_ident,
                            rank: rank1,
                        },
                    ) if caller_ident == fn_ident && rank0 == rank1 => true,
                    _ => false,
                }
            },
        )
        .map(Option::flatten);
    (|ty_expectation_source: Option<TypeExpectationSource>,
      retrieved_ty_signature: Option<TypeSignature>| {
        Some(TypeExpectation {
            ty: retrieved_ty_signature?.ty(),
            source: ty_expectation_source?,
        })
    })
    .apply(ty_expectation_sources, retrieved_ty_signatures)
}

fn calc_ty_expectation_source(
    grandparent_ast: Option<Ast>,
    rank: Option<Rank>,
) -> Option<TypeExpectationSource> {
    let grandparent_ast = grandparent_ast?;
    let rank = rank?;
    match grandparent_ast.data {
        AstData::Call {
            caller,
            caller_ident: Some(caller_ident),
            left_delimiter,
            right_delimiter,
            delimited_arguments,
        } => Some(TypeExpectationSource::CallArgument { caller_ident, rank }),
        _ => None,
    }
}

#[cfg(test)]
fn t(input: &str, expect: Expect) {
    use scope::infer_scopes;
    use signature::calc_ty_signatures;
    use term::calc_ty_terms;

    let (tokens, pre_asts, asts) =
        calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
    let scopes = infer_scopes(asts, 10);
    let roles = calc_roles(asts, scopes, 10);
    let ranks = calc_ranks(asts);
    let ty_terms = calc_ty_terms(asts, roles, 10);
    let ty_signatures = calc_ty_signatures(asts, roles, ty_terms);
    let ty_expectations = calc_ty_expectations(asts, ranks, ty_signatures);
    expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, ty_expectations));
}

#[test]
fn calc_ty_expection_works() {
    t(
        "",
        expect![[r#"
        []
    "#]],
    );
    t(
        "fn f() {}",
        expect![[r#"
        [
            #0 `fn`: "fn f() {}" ✓,
            #1 `f`: "f",
            #2 `(`: `(`,
            #3 `)`: "()",
            #4 `{`: "() {}",
            #5 `}`: "{}",
        ]
    "#]],
    );
    t(
        "fn f() { let x = 1; }",
        expect![[r#"
            [
                #0 `fn`: "fn f() { let x = 1;  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() { let x = 1;  }",
                #5 `let`: "let x = 1",
                #6 `x`: "x",
                #7 `=`: "x = 1",
                #8 `1`: "1",
                #9 `;`: "let x = 1; ",
                #10 `}`: "{ let x = 1;  }",
            ]
        "#]],
    );
    t(
        "fn g(x: Int) {} fn f() { let x = 1; g(x) }",
        expect![[r#"
            [
                #0 `fn`: "fn g(x : Int) {}" ✓,
                #1 `g`: "g",
                #2 `(`: `(`,
                #3 `x`: "x",
                #4 `:`: "x : Int",
                #5 `Int`: "Int",
                #6 `)`: "(x : Int)",
                #7 `{`: "(x : Int) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn f() { let x = 1; g(x) }" ✓,
                #10 `f`: "f",
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { let x = 1; g(x) }",
                #14 `let`: "let x = 1",
                #15 `x`: "x",
                #16 `=`: "x = 1",
                #17 `1`: "1",
                #18 `;`: "let x = 1; ",
                #19 `g`: "g",
                #20 `(`: "g(x)",
                #21 `x`: "x" → TypeExpectation { ty: `Int`, source: CallArgument { caller_ident: `g`, rank: Rank(0) } },
                #22 `)`: "(x)",
                #23 `}`: "{ let x = 1; g(x) }",
            ]
        "#]],
    );
}

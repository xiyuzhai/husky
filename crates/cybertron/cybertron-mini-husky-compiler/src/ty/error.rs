use super::*;
use expectation::TypeExpectation;
use inference::TypeInference;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TypeError {
    TypeMismatch { expected: Type, actual: Type },
}

pub fn calc_ty_errors(
    ty_inferences: Seq<Option<TypeInference>>,
    ty_expectations: Seq<Option<TypeExpectation>>,
) -> Seq<Option<TypeError>> {
    calc_ty_error.apply(ty_inferences, ty_expectations)
}

fn calc_ty_error(
    ty_inference: Option<TypeInference>,
    ty_expectation: Option<TypeExpectation>,
) -> Option<TypeError> {
    let ty_inference = ty_inference?;
    let ty_expectation = ty_expectation?;
    if ty_inference.ty == ty_expectation.ty {
        None
    } else {
        Some(TypeError::TypeMismatch {
            expected: ty_expectation.ty,
            actual: ty_inference.ty,
        })
    }
}

#[cfg(test)]
fn t(input: &str, expect: Expect) {
    use expectation::calc_ty_expectations;
    use inference::calc_ty_inferences;
    use resolution::calc_symbol_resolutions;
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
    let symbol_resolutions = calc_symbol_resolutions(asts, 10);
    let ty_inferences =
        calc_ty_inferences(asts, symbol_resolutions, roles, ty_terms, ty_signatures, 10);
    let ty_errors = calc_ty_errors(ty_inferences, ty_expectations);
    expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, ty_errors));
}

#[test]
fn calc_ty_errors_works() {
    t(
        "",
        expect![[r#"
        []
    "#]],
    );
    t(
        "fn f(x: Float) {} fn g() { f(1) } ",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : Float) {}" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x",
                #4 `:`: "x : Float",
                #5 `Float`: "Float",
                #6 `)`: "(x : Float)",
                #7 `{`: "(x : Float) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn g() { f(1) }" ✓,
                #10 `g`: "g",
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { f(1) }",
                #14 `f`: "f",
                #15 `(`: "f(1)",
                #16 `1`: "1" → TypeMismatch { expected: `Float`, actual: `Int` },
                #17 `)`: "(1)",
                #18 `}`: "{ f(1) }",
            ]
        "#]],
    );
    t(
        "fn f(x: Float) {} fn g() { let x = 1; f(x) } ",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : Float) {}" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x",
                #4 `:`: "x : Float",
                #5 `Float`: "Float",
                #6 `)`: "(x : Float)",
                #7 `{`: "(x : Float) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn g() { let x = 1; f(x) }" ✓,
                #10 `g`: "g",
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { let x = 1; f(x) }",
                #14 `let`: "let x = 1",
                #15 `x`: "x",
                #16 `=`: "x = 1",
                #17 `1`: "1",
                #18 `;`: "let x = 1; ",
                #19 `f`: "f",
                #20 `(`: "f(x)",
                #21 `x`: "x" → TypeMismatch { expected: `Float`, actual: `Int` },
                #22 `)`: "(x)",
                #23 `}`: "{ let x = 1; f(x) }",
            ]
        "#]],
    );
    t(
        "fn f(a: Float) {} fn g() { let x = 1; f(x) } ",
        expect![[r#"
            [
                #0 `fn`: "fn f(a : Float) {}" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `a`: "a",
                #4 `:`: "a : Float",
                #5 `Float`: "Float",
                #6 `)`: "(a : Float)",
                #7 `{`: "(a : Float) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn g() { let x = 1; f(x) }" ✓,
                #10 `g`: "g",
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { let x = 1; f(x) }",
                #14 `let`: "let x = 1",
                #15 `x`: "x",
                #16 `=`: "x = 1",
                #17 `1`: "1",
                #18 `;`: "let x = 1; ",
                #19 `f`: "f",
                #20 `(`: "f(x)",
                #21 `x`: "x" → TypeMismatch { expected: `Float`, actual: `Int` },
                #22 `)`: "(x)",
                #23 `}`: "{ let x = 1; f(x) }",
            ]
        "#]],
    );
}

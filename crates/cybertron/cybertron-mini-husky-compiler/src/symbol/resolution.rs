use super::defn::calc_symbol_defns;
use super::*;
use ast::calc_asts_from_input_together_with_tokens_and_pre_asts;
use cybertron::prelude::*;
use scope::infer_scopes;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolResolution {
    Ok(Symbol),
    Err(SymbolResolutionError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolResolutionError {
    NotResolved,
    NotYetDeclared(Symbol),
}

pub fn calc_symbol_resolutions(asts: Seq<Option<Ast>>, n: usize) -> Seq<Option<SymbolResolution>> {
    let scopes = infer_scopes(asts, n);
    let symbol_defns = calc_symbol_defns(asts, scopes, n);
    let idents = asts.map(|ast| match ast?.data {
        AstData::Ident(ident) => Some(ident),
        _ => None,
    });
    let symbols = symbol_defns
        .map(|symbol_defn| Some(symbol_defn?.symbol))
        .first_filtered_by_attention(
            (|ident, scope| (ident, scope)).apply(idents, scopes),
            symbol_defns,
            |(ident, scope), symbol_defn| {
                let Some(ident) = ident else { return false };
                let Some(symbol_defn) = symbol_defn else {
                    return false;
                };
                if let Some(symbol_defn_scope) = symbol_defn.scope {
                    if !symbol_defn_scope.contains(scope.unwrap()) {
                        return false;
                    }
                }
                symbol_defn.symbol.ident == ident
            },
        )
        .map(|s| s.flatten());
    finalize.apply_enumerated(idents, symbols)
}

fn finalize(idx: Idx, ident: Option<Ident>, symbol: Option<Symbol>) -> Option<SymbolResolution> {
    let _ = ident?;
    let Some(symbol) = symbol else {
        return Some(SymbolResolution::Err(SymbolResolutionError::NotResolved));
    };
    match symbol.data {
        SymbolData::Item { .. } => (),
        SymbolData::Variable => {
            if idx < symbol.source {
                return Some(SymbolResolution::Err(
                    SymbolResolutionError::NotYetDeclared(symbol),
                ));
            }
        }
    }
    Some(SymbolResolution::Ok(symbol))
}

#[test]
fn calc_symbol_resoluion_works() {
    fn t(input: &str, expect: Expect) {
        let (tokens, pre_asts, asts) =
            calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
        let symbol_resolutions = calc_symbol_resolutions(asts, 10);
        expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, symbol_resolutions))
    }
    t(
        "1",
        expect![[r#"
            [
                #0 `1`: "1" ✓,
            ]
        "#]],
    );
    t(
        "fn f() {} fn g() { f() }",
        expect![[r#"
            [
                #0 `fn`: "fn f() {}" ✓,
                #1 `f`: "f" → Ok(Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }),
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() {}",
                #5 `}`: "{}",
                #6 `fn`: "fn g() { f() }" ✓,
                #7 `g`: "g" → Ok(Symbol { ident: `g`, source: #6, data: Item { kind: Fn } }),
                #8 `(`: `(`,
                #9 `)`: "()",
                #10 `{`: "() { f() }",
                #11 `f`: "f" → Ok(Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }),
                #12 `(`: "f()",
                #13 `)`: "()",
                #14 `}`: "{ f() }",
            ]
        "#]],
    );
    t(
        r#"
fn f() {
    {
        let x = 1;
    }
    let y = x;
    g()
}"#,
        expect![[r#"
            [
                #0 `fn`: `fn`,
                #1 `f`: "f" ✓ → Err(NotResolved),
                #2 `(`: `(`,
                #3 `)`: "()" ✓,
                #4 `{`: `{`,
                #5 `{`: `{`,
                #6 `let`: "let x = 1",
                #7 `x`: "x" → Ok(Symbol { ident: `x`, source: #7, data: Variable }),
                #8 `=`: "x = 1",
                #9 `1`: "1",
                #10 `;`: "let x = 1; ",
                #11 `}`: "{ let x = 1;  }" ✓,
                #12 `let`: "let y = x" ✓,
                #13 `y`: "y" → Ok(Symbol { ident: `y`, source: #13, data: Variable }),
                #14 `=`: "y = x",
                #15 `x`: "x" → Err(NotResolved),
                #16 `;`: `;`,
                #17 `g`: "g" → Err(NotResolved),
                #18 `(`: "g()" ✓,
                #19 `)`: "()",
                #20 `}`: `}`,
            ]
        "#]],
    );
    t(
        r#"
fn f() {}

fn g() {
    let x = 1;
    let y = x;
    f()
}"#,
        expect![[r#"
            [
                #0 `fn`: "fn f() {}" ✓,
                #1 `f`: "f" → Ok(Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }),
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() {}",
                #5 `}`: "{}",
                #6 `fn`: "fn g() { let x = 1; let y = x; f() }" ✓,
                #7 `g`: "g" → Ok(Symbol { ident: `g`, source: #6, data: Item { kind: Fn } }),
                #8 `(`: `(`,
                #9 `)`: "()",
                #10 `{`: "() { let x = 1; let y = x; f() }",
                #11 `let`: "let x = 1",
                #12 `x`: "x" → Ok(Symbol { ident: `x`, source: #12, data: Variable }),
                #13 `=`: "x = 1",
                #14 `1`: "1",
                #15 `;`: "let x = 1; ",
                #16 `let`: "let y = x",
                #17 `y`: "y" → Ok(Symbol { ident: `y`, source: #17, data: Variable }),
                #18 `=`: "y = x",
                #19 `x`: "x" → Ok(Symbol { ident: `x`, source: #12, data: Variable }),
                #20 `;`: "let y = x; ",
                #21 `f`: "f" → Ok(Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }),
                #22 `(`: "f()",
                #23 `)`: "()",
                #24 `}`: "{ let x = 1; let y = x; f() }",
            ]
        "#]],
    );
    t(
        "fn f(x: Float) {} fn g() { let x = 1; f(x) } ",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : Float) {}" ✓,
                #1 `f`: "f" → Ok(Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }),
                #2 `(`: `(`,
                #3 `x`: "x" → Err(NotResolved),
                #4 `:`: "x : Float",
                #5 `Float`: "Float" → Err(NotResolved),
                #6 `)`: "(x : Float)",
                #7 `{`: "(x : Float) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn g() { let x = 1; f(x) }" ✓,
                #10 `g`: "g" → Ok(Symbol { ident: `g`, source: #9, data: Item { kind: Fn } }),
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { let x = 1; f(x) }",
                #14 `let`: "let x = 1",
                #15 `x`: "x" → Ok(Symbol { ident: `x`, source: #15, data: Variable }),
                #16 `=`: "x = 1",
                #17 `1`: "1",
                #18 `;`: "let x = 1; ",
                #19 `f`: "f" → Ok(Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }),
                #20 `(`: "f(x)",
                #21 `x`: "x" → Ok(Symbol { ident: `x`, source: #15, data: Variable }),
                #22 `)`: "(x)",
                #23 `}`: "{ let x = 1; f(x) }",
            ]
        "#]],
    );
}

#[test]
fn calc_symbol_resoluion_works1() {
    fn t(input: &str, expect: Expect) {
        let (tokens, pre_asts, asts) =
            calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
        let symbol_resolutions = calc_symbol_resolutions(asts, 10);
        expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, symbol_resolutions))
    }
    t(
        "fn f(x: Float) {} fn g() { let x = 1; f(x) } ",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : Float) {}" ✓,
                #1 `f`: "f" → Ok(Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }),
                #2 `(`: `(`,
                #3 `x`: "x" → Err(NotResolved),
                #4 `:`: "x : Float",
                #5 `Float`: "Float" → Err(NotResolved),
                #6 `)`: "(x : Float)",
                #7 `{`: "(x : Float) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn g() { let x = 1; f(x) }" ✓,
                #10 `g`: "g" → Ok(Symbol { ident: `g`, source: #9, data: Item { kind: Fn } }),
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { let x = 1; f(x) }",
                #14 `let`: "let x = 1",
                #15 `x`: "x" → Ok(Symbol { ident: `x`, source: #15, data: Variable }),
                #16 `=`: "x = 1",
                #17 `1`: "1",
                #18 `;`: "let x = 1; ",
                #19 `f`: "f" → Ok(Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }),
                #20 `(`: "f(x)",
                #21 `x`: "x" → Ok(Symbol { ident: `x`, source: #15, data: Variable }),
                #22 `)`: "(x)",
                #23 `}`: "{ let x = 1; f(x) }",
            ]
        "#]],
    );
}

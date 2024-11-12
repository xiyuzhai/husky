use super::*;
use ast::{calc_asts_from_input_together_with_tokens_and_pre_asts, helpers::parent_queries};
use cybertron::prelude::*;
use scope::{infer_scopes, Scope};
use token::opr::{BinaryOpr, Opr};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SymbolDefn {
    pub symbol: Symbol,
    pub scope: Option<Scope>,
}

pub fn calc_symbol_defns(
    asts: Seq<Option<Ast>>,
    scopes: Seq<Option<Scope>>,
    n: usize,
) -> Seq<Option<SymbolDefn>> {
    let roles = calc_roles(asts, scopes, n);
    calc_symbol_defn.apply_enumerated(asts, roles, scopes)
}

fn calc_symbol_defn(
    idx: Idx,
    ast: Option<Ast>,
    role: Option<Role>,
    scope: Option<Scope>,
) -> Option<SymbolDefn> {
    match ast?.data {
        AstData::Ident(ident) => match role? {
            Role::LetStmt { .. } => unreachable!(),
            Role::LetStmtVariables | Role::LetStmtIdent => Some(SymbolDefn {
                symbol: Symbol {
                    ident,
                    source: idx,
                    data: SymbolData::Variable,
                },
                scope,
            }),
            Role::FnParameterIdent { scope } => Some(SymbolDefn {
                symbol: Symbol {
                    ident,
                    source: idx,
                    data: SymbolData::Variable,
                },
                scope: Some(scope),
            }),
            _ => None,
        },
        AstData::Defn {
            keyword,
            ident_idx,
            ident,
            content,
        } => Some(SymbolDefn {
            symbol: Symbol {
                ident,
                source: idx,
                data: SymbolData::Item {
                    kind: keyword.into(),
                },
            },
            scope,
        }),
        _ => None,
    }
}

#[test]
fn calc_symbol_defns_works() {
    fn t(input: &str, expect: Expect) {
        let (tokens, pre_asts, asts) =
            calc_asts_from_input_together_with_tokens_and_pre_asts(input, 10);
        let scopes = infer_scopes(asts, 10);
        let symbol_defns = calc_symbol_defns(asts, scopes, 10);
        expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, symbol_defns))
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
        "struct A {}",
        expect![[r#"
            [
                #0 `struct`: "struct A {}" ✓ → SymbolDefn { symbol: Symbol { ident: `A`, source: #0, data: Item { kind: Struct } }, scope: Some(`::`) },
                #1 `A`: "A",
                #2 `{`: `{`,
                #3 `}`: "{}",
            ]
        "#]],
    );
    t(
        "enum B {}",
        expect![[r#"
            [
                #0 `enum`: "enum B {}" ✓ → SymbolDefn { symbol: Symbol { ident: `B`, source: #0, data: Item { kind: Enum } }, scope: Some(`::`) },
                #1 `B`: "B",
                #2 `{`: `{`,
                #3 `}`: "{}",
            ]
        "#]],
    );
    t(
        "fn f() {}",
        expect![[r#"
            [
                #0 `fn`: "fn f() {}" ✓ → SymbolDefn { symbol: Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }, scope: Some(`::`) },
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() {}",
                #5 `}`: "{}",
            ]
        "#]],
    );
    t(
        "fn f() { let x = 1 }",
        expect![[r#"
            [
                #0 `fn`: "fn f() { let x = 1 }" ✓ → SymbolDefn { symbol: Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }, scope: Some(`::`) },
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() { let x = 1 }",
                #5 `let`: "let x = 1",
                #6 `x`: "x" → SymbolDefn { symbol: Symbol { ident: `x`, source: #6, data: Variable }, scope: Some(`::9`) },
                #7 `=`: "x = 1",
                #8 `1`: "1",
                #9 `}`: "{ let x = 1 }",
            ]
        "#]],
    );
    t(
        "fn f() { let x = 1; }",
        expect![[r#"
            [
                #0 `fn`: "fn f() { let x = 1;  }" ✓ → SymbolDefn { symbol: Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }, scope: Some(`::`) },
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() { let x = 1;  }",
                #5 `let`: "let x = 1",
                #6 `x`: "x" → SymbolDefn { symbol: Symbol { ident: `x`, source: #6, data: Variable }, scope: Some(`::10`) },
                #7 `=`: "x = 1",
                #8 `1`: "1",
                #9 `;`: "let x = 1; ",
                #10 `}`: "{ let x = 1;  }",
            ]
        "#]],
    );
    t(
        "fn f() { let x: Int = 1; }",
        expect![[r#"
            [
                #0 `fn`: "fn f() { let x : Int = 1;  }" ✓ → SymbolDefn { symbol: Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }, scope: Some(`::`) },
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() { let x : Int = 1;  }",
                #5 `let`: "let x : Int = 1",
                #6 `x`: "x" → SymbolDefn { symbol: Symbol { ident: `x`, source: #6, data: Variable }, scope: Some(`::12`) },
                #7 `:`: "x : Int",
                #8 `Int`: "Int",
                #9 `=`: "x : Int = 1",
                #10 `1`: "1",
                #11 `;`: "let x : Int = 1; ",
                #12 `}`: "{ let x : Int = 1;  }",
            ]
        "#]],
    );
    t(
        "fn f(x: Float) {} fn g() { let x = 1; f(x) } ",
        expect![[r#"
            [
                #0 `fn`: "fn f(x : Float) {}" ✓ → SymbolDefn { symbol: Symbol { ident: `f`, source: #0, data: Item { kind: Fn } }, scope: Some(`::`) },
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `x`: "x" → SymbolDefn { symbol: Symbol { ident: `x`, source: #3, data: Variable }, scope: Some(`::8`) },
                #4 `:`: "x : Float",
                #5 `Float`: "Float",
                #6 `)`: "(x : Float)",
                #7 `{`: "(x : Float) {}",
                #8 `}`: "{}",
                #9 `fn`: "fn g() { let x = 1; f(x) }" ✓ → SymbolDefn { symbol: Symbol { ident: `g`, source: #9, data: Item { kind: Fn } }, scope: Some(`::`) },
                #10 `g`: "g",
                #11 `(`: `(`,
                #12 `)`: "()",
                #13 `{`: "() { let x = 1; f(x) }",
                #14 `let`: "let x = 1",
                #15 `x`: "x" → SymbolDefn { symbol: Symbol { ident: `x`, source: #15, data: Variable }, scope: Some(`::23`) },
                #16 `=`: "x = 1",
                #17 `1`: "1",
                #18 `;`: "let x = 1; ",
                #19 `f`: "f",
                #20 `(`: "f(x)",
                #21 `x`: "x",
                #22 `)`: "(x)",
                #23 `}`: "{ let x = 1; f(x) }",
            ]
        "#]],
    );
}

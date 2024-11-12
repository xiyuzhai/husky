use super::*;
use super::{
    call::reduce_by_call, defn::reduce_by_defn, delimited::reduce_by_delimited, opr::reduce_by_opr,
    show::show_asts, stmt::reduce_by_stmt, utils::update_pre_asts_by_new_asts,
};
use cybertron::{
    debug::{is_debug, set_debug},
    prelude::*,
    seq::any::AnySeq,
};
use indexmap::IndexMap;

pub fn reduce(
    pre_asts: Seq<Option<PreAst>>,
    allocated_asts: Seq<Option<Ast>>,
) -> (Seq<Option<PreAst>>, Seq<Option<Ast>>) {
    let (pre_asts, allocated_asts) = reduce_by_opr(pre_asts, allocated_asts);
    let (pre_asts, allocated_asts) = reduce_by_delimited(pre_asts, allocated_asts);
    let (pre_asts, allocated_asts) = reduce_by_call(pre_asts, allocated_asts);
    let (pre_asts, allocated_asts) = reduce_by_stmt(pre_asts, allocated_asts);
    let (pre_asts, allocated_asts) = reduce_by_defn(pre_asts, allocated_asts);
    (pre_asts, allocated_asts)
}

pub fn reduce_n_times(
    mut pre_asts: Seq<Option<PreAst>>,
    mut allocated_asts: Seq<Option<Ast>>,
    n: usize,
) -> (Seq<Option<PreAst>>, Seq<Option<Ast>>) {
    for _ in 0..n {
        let (pre_asts1, allocated_asts1) = reduce(pre_asts, allocated_asts);
        pre_asts = pre_asts1;
        allocated_asts = allocated_asts1;
    }
    (pre_asts, allocated_asts)
}

#[cfg(test)]
pub(super) fn t(input: &str, n: usize, expect: Expect) {
    let tokens = tokenize(input);
    let pre_asts = calc_pre_ast_initial_seq(tokens);
    let allocated_asts: Seq<Option<Ast>> = tokens.map(|token| token.into());
    let (pre_asts, asts) = reduce_n_times(pre_asts, allocated_asts, n);
    expect.assert_debug_eq(&show_asts(tokens, asts));
}

#[test]
fn reduce_n_times_works() {
    t(
        "",
        1,
        expect![[r#"
        []
    "#]],
    );
    t(
        "fn f() { 1; (2); }",
        10,
        expect![[r#"
            [
                #0 `fn`: "fn f() { 1; (2);  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() { 1; (2);  }",
                #5 `1`: "1",
                #6 `;`: "1; ",
                #7 `(`: `(`,
                #8 `2`: "2",
                #9 `)`: "(2)",
                #10 `;`: "(2); ",
                #11 `}`: "{ 1; (2);  }",
            ]
        "#]],
    );
    t(
        "fn f() { 1; g(2); }",
        10,
        expect![[r#"
            [
                #0 `fn`: "fn f() { 1; g(2);  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() { 1; g(2);  }",
                #5 `1`: "1",
                #6 `;`: "1; ",
                #7 `g`: "g",
                #8 `(`: "g(2)",
                #9 `2`: "2",
                #10 `)`: "(2)",
                #11 `;`: "g(2); ",
                #12 `}`: "{ 1; g(2);  }",
            ]
        "#]],
    );
    t(
        "fn f() { 1; let x = g(2); }",
        10,
        expect![[r#"
            [
                #0 `fn`: "fn f() { 1; let x = g(2);  }" ✓,
                #1 `f`: "f",
                #2 `(`: `(`,
                #3 `)`: "()",
                #4 `{`: "() { 1; let x = g(2);  }",
                #5 `1`: "1",
                #6 `;`: "1; ",
                #7 `let`: "let x = g(2)",
                #8 `x`: "x",
                #9 `=`: "x = g(2)",
                #10 `g`: "g",
                #11 `(`: "g(2)",
                #12 `2`: "2",
                #13 `)`: "(2)",
                #14 `;`: "let x = g(2); ",
                #15 `}`: "{ 1; let x = g(2);  }",
            ]
        "#]],
    );
}

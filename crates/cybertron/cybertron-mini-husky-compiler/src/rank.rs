use crate::{
    show::{show_asts, show_asts_mapped_values},
    *,
};

#[derive(Debug, Default, PartialEq, Eq, Clone, Copy)]
pub struct Rank(u8);

impl Rank {
    fn next(self) -> Self {
        Self(self.0 + 1)
    }
}

pub fn calc_ranks(asts: Seq<Option<Ast>>) -> Seq<Option<Rank>> {
    let counts = asts.count_past_by_attention(asts, |ast, ast1| {
        let Some(ast) = ast else { return false };
        let Some(ast1) = ast1 else { return false };
        ast.parent == ast1.parent
    });
    (|c: usize, ast| {
        ast?;
        Some(Rank(c.try_into().unwrap()))
    })
    .apply(counts, asts)
}

pub fn calc_ranks1(asts: Seq<Option<Ast>>, n: usize) -> Seq<Option<Rank>> {
    let mut ranks: Seq<Option<Rank>> = asts.map(|_| None);
    for _ in 0..n {
        ranks = calc_sibling_indicies_step(asts, ranks);
    }
    ranks
}

fn calc_sibling_indicies_step(
    asts: Seq<Option<Ast>>,
    ranks: Seq<Option<Rank>>,
) -> Seq<Option<Rank>> {
    let previous_ranks = ranks.nearest_left_filtered_by_attention(asts, asts, |ast, ast1| {
        let Some(ast) = ast else { return false };
        let Some(ast1) = ast1 else { return false };
        ast.parent == ast1.parent
    });
    let ranks = (|ast, rank, previous_rank: Option<Option<Rank>>| {
        let _ = ast?;
        if let Some(rank) = rank {
            return Some(rank);
        }
        let Some(previous_rank) = previous_rank else {
            return Some(Default::default());
        };
        Some(previous_rank?.next())
    })
    .apply(asts, ranks, previous_ranks);
    ranks
}

#[test]
fn calc_ranks_works() {
    fn t(input: &str, n: usize, expect: Expect) {
        let (tokens, pre_asts, asts) =
            calc_asts_from_input_together_with_tokens_and_pre_asts(input, n);
        let ranks = calc_ranks(asts);
        expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, ranks));
    }
    t(
        "1",
        10,
        expect![[r#"
            [
                #0 `1`: "1" ✓ → Rank(0),
            ]
        "#]],
    );
    t(
        "1+1",
        10,
        expect![[r#"
            [
                #0 `1`: "1" → Rank(0),
                #1 `+`: "1 + 1" ✓ → Rank(0),
                #2 `1`: "1" → Rank(1),
            ]
        "#]],
    );
    t(
        "1+1*2",
        10,
        expect![[r#"
            [
                #0 `1`: "1" → Rank(0),
                #1 `+`: "1 + 1 * 2" ✓ → Rank(0),
                #2 `1`: "1" → Rank(0),
                #3 `*`: "1 * 2" → Rank(1),
                #4 `2`: "2" → Rank(1),
            ]
        "#]],
    );
    t(
        "fn f() {}",
        10,
        expect![[r#"
        [
            #0 `fn`: "fn f() {}" ✓ → Rank(0),
            #1 `f`: "f" → Rank(0),
            #2 `(`: `(`,
            #3 `)`: "()" → Rank(0),
            #4 `{`: "() {}" → Rank(1),
            #5 `}`: "{}" → Rank(1),
        ]
    "#]],
    );
    t(
        "fn f() { let x = 1; let y = g(x, 1, 2); }",
        10,
        expect![[r#"
            [
                #0 `fn`: "fn f() { let x = 1; let y = g(x, 1, 2);  }" ✓ → Rank(0),
                #1 `f`: "f" → Rank(0),
                #2 `(`: `(`,
                #3 `)`: "()" → Rank(0),
                #4 `{`: "() { let x = 1; let y = g(x, 1, 2);  }" → Rank(1),
                #5 `let`: "let x = 1" → Rank(0),
                #6 `x`: "x" → Rank(0),
                #7 `=`: "x = 1" → Rank(0),
                #8 `1`: "1" → Rank(1),
                #9 `;`: "let x = 1; " → Rank(0),
                #10 `let`: "let y = g(x, 1, 2)" → Rank(0),
                #11 `y`: "y" → Rank(0),
                #12 `=`: "y = g(x, 1, 2)" → Rank(0),
                #13 `g`: "g" → Rank(0),
                #14 `(`: "g(x, 1, 2)" → Rank(1),
                #15 `x`: "x" → Rank(0),
                #16 `,`: "x, " → Rank(0),
                #17 `1`: "1" → Rank(0),
                #18 `,`: "1, " → Rank(1),
                #19 `2`: "2" → Rank(2),
                #20 `)`: "(x, 1, 2)" → Rank(1),
                #21 `;`: "let y = g(x, 1, 2); " → Rank(1),
                #22 `}`: "{ let x = 1; let y = g(x, 1, 2);  }" → Rank(1),
            ]
        "#]],
    );
}

#[test]
fn calc_ranks1_works() {
    fn t(input: &str, n: usize, expect: Expect) {
        let (tokens, pre_asts, asts) =
            calc_asts_from_input_together_with_tokens_and_pre_asts(input, n);
        let ranks = calc_ranks1(asts, 10);
        assert_eq!(ranks, calc_ranks(asts), "input = {:?}", input);
        expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, ranks));
    }
    t(
        "1",
        10,
        expect![[r#"
            [
                #0 `1`: "1" ✓ → Rank(0),
            ]
        "#]],
    );
    t(
        "1+1",
        10,
        expect![[r#"
            [
                #0 `1`: "1" → Rank(0),
                #1 `+`: "1 + 1" ✓ → Rank(0),
                #2 `1`: "1" → Rank(1),
            ]
        "#]],
    );
    t(
        "1+1*2",
        10,
        expect![[r#"
            [
                #0 `1`: "1" → Rank(0),
                #1 `+`: "1 + 1 * 2" ✓ → Rank(0),
                #2 `1`: "1" → Rank(0),
                #3 `*`: "1 * 2" → Rank(1),
                #4 `2`: "2" → Rank(1),
            ]
        "#]],
    );
    t(
        "g(x, 1, 2)",
        10,
        expect![[r#"
            [
                #0 `g`: "g" → Rank(0),
                #1 `(`: "g(x, 1, 2)" ✓ → Rank(0),
                #2 `x`: "x" → Rank(0),
                #3 `,`: "x, " → Rank(0),
                #4 `1`: "1" → Rank(0),
                #5 `,`: "1, " → Rank(1),
                #6 `2`: "2" → Rank(2),
                #7 `)`: "(x, 1, 2)" → Rank(1),
            ]
        "#]],
    );
    t(
        "g(x, 1, 2, 3)",
        10,
        expect![[r#"
            [
                #0 `g`: "g" → Rank(0),
                #1 `(`: "g(x, 1, 2, 3)" ✓ → Rank(0),
                #2 `x`: "x" → Rank(0),
                #3 `,`: "x, " → Rank(0),
                #4 `1`: "1" → Rank(0),
                #5 `,`: "1, " → Rank(1),
                #6 `2`: "2" → Rank(0),
                #7 `,`: "2, " → Rank(2),
                #8 `3`: "3" → Rank(3),
                #9 `)`: "(x, 1, 2, 3)" → Rank(1),
            ]
        "#]],
    );
    t(
        "fn f() {}",
        10,
        expect![[r#"
            [
                #0 `fn`: "fn f() {}" ✓ → Rank(0),
                #1 `f`: "f" → Rank(0),
                #2 `(`: `(`,
                #3 `)`: "()" → Rank(0),
                #4 `{`: "() {}" → Rank(1),
                #5 `}`: "{}" → Rank(1),
            ]
        "#]],
    );
    t(
        "fn f() { let x = 1; let y = g(x, 1, 2); }",
        10,
        expect![[r#"
            [
                #0 `fn`: "fn f() { let x = 1; let y = g(x, 1, 2);  }" ✓ → Rank(0),
                #1 `f`: "f" → Rank(0),
                #2 `(`: `(`,
                #3 `)`: "()" → Rank(0),
                #4 `{`: "() { let x = 1; let y = g(x, 1, 2);  }" → Rank(1),
                #5 `let`: "let x = 1" → Rank(0),
                #6 `x`: "x" → Rank(0),
                #7 `=`: "x = 1" → Rank(0),
                #8 `1`: "1" → Rank(1),
                #9 `;`: "let x = 1; " → Rank(0),
                #10 `let`: "let y = g(x, 1, 2)" → Rank(0),
                #11 `y`: "y" → Rank(0),
                #12 `=`: "y = g(x, 1, 2)" → Rank(0),
                #13 `g`: "g" → Rank(0),
                #14 `(`: "g(x, 1, 2)" → Rank(1),
                #15 `x`: "x" → Rank(0),
                #16 `,`: "x, " → Rank(0),
                #17 `1`: "1" → Rank(0),
                #18 `,`: "1, " → Rank(1),
                #19 `2`: "2" → Rank(2),
                #20 `)`: "(x, 1, 2)" → Rank(1),
                #21 `;`: "let y = g(x, 1, 2); " → Rank(1),
                #22 `}`: "{ let x = 1; let y = g(x, 1, 2);  }" → Rank(1),
            ]
        "#]],
    );
}

#[test]
fn calc_ranks2_works() {
    fn t(input: &str, n: usize, expect: Expect) {
        let (tokens, pre_asts, asts) =
            calc_asts_from_input_together_with_tokens_and_pre_asts(input, n);
        let ranks = calc_ranks1(asts, 10);
        assert_eq!(ranks, calc_ranks(asts), "input = {:?}", input);
        expect.assert_debug_eq(&show_asts_mapped_values(tokens, asts, ranks));
    }
    t(
        "fn f() {}",
        10,
        expect![[r#"
            [
                #0 `fn`: "fn f() {}" ✓ → Rank(0),
                #1 `f`: "f" → Rank(0),
                #2 `(`: `(`,
                #3 `)`: "()" → Rank(0),
                #4 `{`: "() {}" → Rank(1),
                #5 `}`: "{}" → Rank(1),
            ]
        "#]],
    );
}

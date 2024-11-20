use super::*;
use helpers::tracker::VdLeanTranspilationTracker;
use latex_prelude::{helper::tracker::LxPageInput, mode::LxMode};
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expected_display_tree: &Expect, expected_fmt: &Expect) {
    let db = &DB::default();
    let file_path = LxFilePath::new(db, PathBuf::from(file!()));
    let tracker = VdLeanTranspilationTracker::new(LxPageInput { file_path, content }, &[], &[], db);
    expected_display_tree.assert_eq(&tracker.show_display_tree(db));
    expected_fmt.assert_eq(&tracker.show_fmt(db));
}

#[test]
fn basic_visored_clause_to_lean_works() {
    t(
        "Let $x\\in\\mathbb{N}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect!["variable (x : ℕ)"],
    );
    t(
        "Let $x\\in\\mathbb{Z}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect!["variable (x : ℤ)"],
    );
    t(
        "Let $x\\in\\mathbb{Q}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect!["variable (x : ℚ)"],
    );
    t(
        "Let $x\\in\\mathbb{R}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect!["variable (x : ℝ)"],
    );
    t(
        "Let $x\\in\\mathbb{C}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect!["variable (x : ℂ)"],
    );
    t(
        "Let $x\\in\\mathbb{R}$. Then $x=x$.",
        &expect![[r#"
            └─ group: `paragraph`
              ├─ group: `sentence`
              │ └─ variable: `x`
              └─ group: `sentence`
                └─ def: `h`
                  ├─ application
                  │ ├─ variable: `x`
                  │ └─ variable: `x`
                  └─ sorry
        "#]],
        &expect![[r#"
            variable (x : ℝ)

            def h : x = x := sorry"#]],
    );
    t(
        "Let $x\\in\\mathbb{N}$. Then $2x\\ge x$.",
        &expect![[r#"
            └─ group: `paragraph`
              ├─ group: `sentence`
              │ └─ variable: `x`
              └─ group: `sentence`
                └─ def: `h`
                  ├─ application
                  │ ├─ application
                  │ │ ├─ literal: `2`
                  │ │ └─ variable: `x`
                  │ └─ variable: `x`
                  └─ sorry
        "#]],
        &expect![[r#"
            variable (x : ℕ)

            def h : 2 * x ≥ x := sorry"#]],
    );
    t(
        "Let $x\\in\\mathbb{R}$. Then ${(x-1)}^2 \\ge 0$. Then $x^2-2x+1 \\ge 0$. Then $x^2 + 1\\ge 2x$.",
        &expect![[r#"
            └─ group: `paragraph`
              ├─ group: `sentence`
              │ └─ variable: `x`
              ├─ group: `sentence`
              │ └─ def: `h`
              │   ├─ application
              │   │ ├─ application
              │   │ │ ├─ application
              │   │ │ │ ├─ variable: `x`
              │   │ │ │ └─ literal: `1`
              │   │ │ └─ literal: `2`
              │   │ └─ literal: `0`
              │   └─ sorry
              ├─ group: `sentence`
              │ └─ def: `h1`
              │   ├─ application
              │   │ ├─ application
              │   │ │ ├─ application
              │   │ │ │ ├─ application
              │   │ │ │ │ ├─ variable: `x`
              │   │ │ │ │ └─ literal: `2`
              │   │ │ │ └─ application
              │   │ │ │   ├─ literal: `2`
              │   │ │ │   └─ variable: `x`
              │   │ │ └─ literal: `1`
              │   │ └─ literal: `0`
              │   └─ sorry
              └─ group: `sentence`
                └─ def: `h2`
                  ├─ application
                  │ ├─ application
                  │ │ ├─ application
                  │ │ │ ├─ variable: `x`
                  │ │ │ └─ literal: `2`
                  │ │ └─ literal: `1`
                  │ └─ application
                  │   ├─ literal: `2`
                  │   └─ variable: `x`
                  └─ sorry
        "#]],
        &expect![[r#"
            variable (x : ℝ)

            def h : (x - 1) ^ 2 ≥ 0 := sorry

            def h1 : x ^ 2 - 2 * x + 1 ≥ 0 := sorry

            def h2 : x ^ 2 + 1 ≥ 2 * x := sorry"#]],
    );
}

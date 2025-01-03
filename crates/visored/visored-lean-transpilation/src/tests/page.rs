use super::*;
use crate::{
    helpers::tracker::VdLeanTranspilationTracker, scheme::sparse::VdLeanTranspilationSparseScheme,
};
use eterned::db::EternerDb;
use latex_prelude::{helper::tracker::LxPageInput, mode::LxMode};
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;
use visored_mir_expr::elaborator::VdMirTrivialElaborator;
use visored_syn_expr::vibe::VdSynExprVibe;

fn t(models: &VdModels, content: &str, expected_display_tree: &Expect, expected_fmt: &Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let db = &EternerDb::default();
    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()), db);
    let tracker = VdLeanTranspilationTracker::new(
        LxPageInput {
            specs_dir: dev_paths.specs_dir(),
            file_path,
            content,
        },
        &[],
        &[],
        models,
        VdSynExprVibe::ROOT_CNL,
        db,
        &VdLeanTranspilationSparseScheme,
        |_| VdMirTrivialElaborator::default(),
    );
    expected_display_tree.assert_eq(&tracker.show_display_tree(db));
    expected_fmt.assert_eq(&tracker.show_fmt(db));
}

#[test]
fn basic_visored_clause_to_lean_works() {
    let models = &VdModels::new();
    t(
        models,
        "Let $x\\in\\mathbb{N}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect![[r#"
            -- Let $x\in\mathbb{N}$.

            variable (x : ℕ)"#]],
    );
    t(
        models,
        "Let $x\\in\\mathbb{Z}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect![[r#"
            -- Let $x\in\mathbb{Z}$.

            variable (x : ℤ)"#]],
    );
    t(
        models,
        "Let $x\\in\\mathbb{Q}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect![[r#"
            -- Let $x\in\mathbb{Q}$.

            variable (x : ℚ)"#]],
    );
    t(
        models,
        "Let $x\\in\\mathbb{R}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect![[r#"
            -- Let $x\in\mathbb{R}$.

            variable (x : ℝ)"#]],
    );
    t(
        models,
        "Let $x\\in\\mathbb{C}$.",
        &expect![[r#"
            └─ group: `paragraph`
              └─ group: `sentence`
                └─ variable: `x`
        "#]],
        &expect![[r#"
            -- Let $x\in\mathbb{C}$.

            variable (x : ℂ)"#]],
    );
    t(
        models,
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
                  └─ tactics
                    └─ tactic: `Obvious`
        "#]],
        &expect![[r#"
            -- Let $x\in\mathbb{R}$.

            variable (x : ℝ)

            -- Then $x=x$.

            def h : x = x := by
              obvious"#]],
    );
    t(
        models,
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
                  └─ tactics
                    └─ tactic: `Obvious`
        "#]],
        &expect![[r#"
            -- Let $x\in\mathbb{N}$.

            variable (x : ℕ)

            -- Then $2x\ge x$.

            def h : 2 * x ≥ x := by
              obvious"#]],
    );
    t(
        models,
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
              │   └─ tactics
              │     └─ tactic: `Obvious`
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
              │   └─ tactics
              │     └─ tactic: `Obvious`
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
                  └─ tactics
                    └─ tactic: `Obvious`
        "#]],
        &expect![[r#"
            -- Let $x\in\mathbb{R}$.

            variable (x : ℝ)

            -- Then ${(x-1)}^2 \ge 0$.

            def h : (x - 1) ^ 2 ≥ 0 := by
              obvious

            -- Then $x^2-2x+1 \ge 0$.

            def h1 : x ^ 2 - 2 * x + 1 ≥ 0 := by
              obvious

            -- Then $x^2 + 1\ge 2x$.

            def h2 : x ^ 2 + 1 ≥ 2 * x := by
              obvious"#]],
    );
}

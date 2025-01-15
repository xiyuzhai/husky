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
        |_| VdMirTrivialElaborator::new(()),
        &VdLeanTranspilationSparseScheme,
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
            └─ variable: `x`
        "#]],
        &expect!["variable (x : ℕ)"],
    );
    t(
        models,
        "Let $x\\in\\mathbb{Z}$.",
        &expect![[r#"
            └─ variable: `x`
        "#]],
        &expect!["variable (x : ℤ)"],
    );
    t(
        models,
        "Let $x\\in\\mathbb{Q}$.",
        &expect![[r#"
            └─ variable: `x`
        "#]],
        &expect!["variable (x : ℚ)"],
    );
    t(
        models,
        "Let $x\\in\\mathbb{R}$.",
        &expect![[r#"
            └─ variable: `x`
        "#]],
        &expect!["variable (x : ℝ)"],
    );
    t(
        models,
        "Let $x\\in\\mathbb{C}$.",
        &expect![[r#"
            └─ variable: `x`
        "#]],
        &expect!["variable (x : ℂ)"],
    );
    t(
        models,
        "Let $x\\in\\mathbb{R}$. Then $x=x$.",
        &expect![[r#"
            ├─ variable: `x`
            └─ def: `h`
              ├─ application
              │ ├─ variable: `x`
              │ └─ variable: `x`
              └─ tactics
                └─ tactic: `Have { ident: LnIdent(Coword("h1")), ty: Some(4), construction: 1 }`
        "#]],
        &expect![[r#"
            variable (x : ℝ)

            def h : x = x := by
              have h1 : x = x := by obvious"#]],
    );
    t(
        models,
        "Let $x\\in\\mathbb{N}$. Then $2x\\ge x$.",
        &expect![[r#"
            ├─ variable: `x`
            └─ def: `h`
              ├─ application
              │ ├─ application
              │ │ ├─ literal: `2`
              │ │ └─ variable: `x`
              │ └─ variable: `x`
              └─ tactics
                └─ tactic: `Have { ident: LnIdent(Coword("h1")), ty: Some(6), construction: 1 }`
        "#]],
        &expect![[r#"
            variable (x : ℕ)

            def h : 2 * x ≥ x := by
              have h1 : 2 * x ≥ x := by obvious"#]],
    );
    t(
        models,
        "Let $x\\in\\mathbb{R}$. Then ${(x-1)}^2 \\ge 0$. Then $x^2-2x+1 \\ge 0$. Then $x^2 + 1\\ge 2x$.",
        &expect![[r#"
            ├─ variable: `x`
            ├─ def: `h`
            │ ├─ application
            │ │ ├─ application
            │ │ │ ├─ application
            │ │ │ │ ├─ variable: `x`
            │ │ │ │ └─ literal: `1`
            │ │ │ └─ literal: `2`
            │ │ └─ literal: `0`
            │ └─ tactics
            │   └─ tactic: `Have { ident: LnIdent(Coword("h1")), ty: Some(10), construction: 1 }`
            ├─ def: `h2`
            │ ├─ application
            │ │ ├─ application
            │ │ │ ├─ application
            │ │ │ │ ├─ application
            │ │ │ │ │ ├─ variable: `x`
            │ │ │ │ │ └─ literal: `2`
            │ │ │ │ └─ application
            │ │ │ │   ├─ literal: `2`
            │ │ │ │   └─ variable: `x`
            │ │ │ └─ literal: `1`
            │ │ └─ literal: `0`
            │ └─ tactics
            │   └─ tactic: `Have { ident: LnIdent(Coword("h3")), ty: Some(34), construction: 20 }`
            └─ def: `h4`
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
                └─ tactic: `Have { ident: LnIdent(Coword("h5")), ty: Some(60), construction: 49 }`
        "#]],
        &expect![[r#"
            variable (x : ℝ)

            def h : (x - (1 : ℝ)) ^ 2 ≥ (0 : ℝ) := by
              have h1 : (x - (1 : ℝ)) ^ 2 ≥ (0 : ℝ) := by obvious

            def h2 : x ^ 2 - (2 : ℝ) * x + (1 : ℝ) ≥ (0 : ℝ) := by
              have h3 : x ^ 2 - (2 : ℝ) * x + (1 : ℝ) ≥ (0 : ℝ) := by obvious

            def h4 : x ^ 2 + (1 : ℝ) ≥ (2 : ℝ) * x := by
              have h5 : x ^ 2 + (1 : ℝ) ≥ (2 : ℝ) * x := by obvious"#]],
    );
}

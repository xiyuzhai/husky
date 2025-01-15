use super::*;
use crate::{
    helpers::tracker::VdLeanTranspilationTracker, scheme::sparse::VdLeanTranspilationSparseScheme,
};
use eterned::db::EternerDb;
use latex_prelude::{helper::tracker::LxFormulaInput, mode::LxMode};
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;
use visored_mir_expr::elaborator::VdMirTrivialElaborator;
use visored_syn_expr::vibe::VdSynExprVibe;

fn t(models: &VdModels, content: &str, expected_display_tree: &Expect, expected_fmt: &Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let db = &EternerDb::default();
    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()), db);
    let tracker = VdLeanTranspilationTracker::new::<VdMirTrivialElaborator>(
        LxFormulaInput {
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
    );
    expected_display_tree.assert_eq(&tracker.show_display_tree(db));
    expected_fmt.assert_eq(&tracker.show_fmt(db));
}

#[test]
fn basic_visored_expr_to_lean_works() {
    let models = &VdModels::new();
    t(
        models,
        "1",
        &expect![[r#"
            literal: `1`
        "#]],
        &expect!["1"],
    );
    t(
        models,
        "-1",
        &expect![[r#"
            application
            └─ literal: `1`
        "#]],
        &expect!["-(1 : ℤ)"],
    );
    t(
        models,
        "1 + 1",
        &expect![[r#"
            application
            ├─ literal: `1`
            └─ literal: `1`
        "#]],
        &expect!["1 + 1"],
    );
    t(
        models,
        "1 < 2",
        &expect![[r#"
            application
            ├─ literal: `1`
            └─ literal: `2`
        "#]],
        &expect!["1 < 2"],
    );
    t(
        models,
        "1\\in\\mathbb{N}",
        &expect![[r#"
            application
            ├─ literal: `1`
            └─ item path: `ℕ`
        "#]],
        &expect!["in_set"],
    );
    t(
        models,
        "\\frac{1}{2}",
        &expect![[r#"
            application
            ├─ literal: `1`
            └─ literal: `2`
        "#]],
        &expect!["(1 : ℚ) / (2 : ℚ)"],
    );
    t(
        models,
        "\\sqrt{2}",
        &expect![[r#"
            application
            ├─ item path: `√`
            └─ literal: `2`
        "#]],
        &expect!["√ (2 : ℝ)"],
    );
}

#[test]
fn item_path_to_lean_works() {
    let models = &VdModels::new();
    t(
        models,
        "\\mathbb{N}",
        &expect![[r#"
            item path: `ℕ`
        "#]],
        &expect!["ℕ"],
    );
}

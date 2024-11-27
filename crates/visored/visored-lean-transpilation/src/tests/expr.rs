use super::*;
use crate::helpers::tracker::VdLeanTranspilationTracker;
use latex_prelude::{helper::tracker::LxFormulaInput, mode::LxMode};
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expected_display_tree: &Expect, expected_fmt: &Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()));
    let tracker = VdLeanTranspilationTracker::new(
        LxFormulaInput {
            specs_dir: dev_paths.specs_dir(),
            file_path,
            content,
        },
        &[],
        &[],
    );
    expected_display_tree.assert_eq(&tracker.show_display_tree());
    expected_fmt.assert_eq(&tracker.show_fmt());
}

#[test]
fn basic_visored_expr_to_lean_works() {
    t(
        "1",
        &expect![[r#"
            literal: `1`
        "#]],
        &expect!["1"],
    );
    t(
        "-1",
        &expect![[r#"
            application
            └─ literal: `1`
        "#]],
        &expect!["-1"],
    );
    t(
        "1 + 1",
        &expect![[r#"
            application
            ├─ literal: `1`
            └─ literal: `1`
        "#]],
        &expect!["1 + 1"],
    );
    t(
        "1 < 2",
        &expect![[r#"
            application
            ├─ literal: `1`
            └─ literal: `2`
        "#]],
        &expect!["1 < 2"],
    );
    t(
        "1\\in\\mathbb{N}",
        &expect![[r#"
            application
            ├─ literal: `1`
            └─ item path: `ℕ`
        "#]],
        &expect!["sorry"],
    );
    t(
        "\\frac{1}{2}",
        &expect![[r#"
            application
            ├─ literal: `1`
            └─ literal: `2`
        "#]],
        &expect!["1 / 2"],
    );
    t(
        "\\sqrt{2}",
        &expect![[r#"
            application
            ├─ item path: `√`
            └─ literal: `2`
        "#]],
        &expect!["√ 2"],
    );
}

#[test]
fn item_path_to_lean_works() {
    t(
        "\\mathbb{N}",
        &expect![[r#"
            item path: `ℕ`
        "#]],
        &expect!["ℕ"],
    );
}

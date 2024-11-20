use super::*;
use helpers::tracker::VdLeanTranspilationTracker;
use latex_prelude::{helper::tracker::LxFormulaInput, mode::LxMode};
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expected_display_tree: &Expect, expected_fmt: &Expect) {
    let db = &DB::default();
    let file_path = LxFilePath::new(db, PathBuf::from(file!()));
    let tracker =
        VdLeanTranspilationTracker::new(LxFormulaInput { file_path, content }, &[], &[], db);
    expected_display_tree.assert_eq(&tracker.show_display_tree(db));
    expected_fmt.assert_eq(&tracker.show_fmt(db));
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
            sorry
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

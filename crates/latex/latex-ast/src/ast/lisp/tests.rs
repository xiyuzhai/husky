use super::*;
use ast::helpers::tracker::LxAstTracker;
use expect_test::Expect;
use latex_prelude::helper::tracker::LxLispInput;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expected: Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let file_path = LxFilePath::new(PathBuf::from(file!()));
    let dev_paths = HuskyLangDevPaths::new();
    let tracker = LxAstTracker::new(LxLispInput {
        specs_dir: dev_paths.specs_dir(),
        file_path,
        content,
    });
    let show = tracker.show();
    expected.assert_eq(&show);
}

#[test]
fn parse_literal_lisp_latex_input_into_asts_works() {
    t(
        "0",
        expect![[r#"
            └─ "0" literal
        "#]],
    );
    t(
        "0.0",
        expect![[r#"
            └─ "0.0" literal
        "#]],
    );
    t(
        "\"hilbert nullstellensatz\"",
        expect![[r#"
            └─ "\"hilbert nullstellensatz\"" literal
        "#]],
    );
    t(
        "\"\\\"\"",
        expect![[r#"
            └─ "\"\\\"\"" literal
        "#]],
    );
    t(
        "\"\\\\\"",
        expect![[r#"
            └─ "\"\\\\\"" literal
        "#]],
    );
}

#[test]
fn parse_ident_lisp_latex_input_into_asts_works() {
    t(
        "x",
        expect![[r#"
            └─ "x" ident
        "#]],
    );
    t(
        "x_1",
        expect![[r#"
            └─ "x_1" ident
        "#]],
    );
    t(
        "apply",
        expect![[r#"
            └─ "apply" ident
        "#]],
    );
    t(
        "apply_to_all",
        expect![[r#"
            └─ "apply_to_all" ident
        "#]],
    );
}

#[test]
fn parse_xlabel_lisp_latex_input_into_asts_works() {
    t(
        "'1",
        expect![[r#"
            └─ "'1" xlabel
        "#]],
    );
    t(
        "'x",
        expect![[r#"
            └─ "'x" xlabel
        "#]],
    );
    t(
        "'eq:1",
        expect![[r#"
            └─ "'eq:1" xlabel
        "#]],
    );
}
#[test]
fn parse_parenthesized_lisp_latex_input_into_asts_works() {
    t(
        "(x)",
        expect![[r#"
            └─ "(x)" parenthesized
              └─ "x" ident
        "#]],
    );
    t(
        "f (g x) y",
        expect![[r#"
            ├─ "f" ident
            ├─ "(g x)" parenthesized
            │ ├─ "g" ident
            │ └─ "x" ident
            └─ "y" ident
        "#]],
    );
}

#[test]
fn parse_basic_lisp_latex_input_into_asts_works() {
    t(
        "x",
        expect![[r#"
            └─ "x" ident
        "#]],
    );
    t(
        "f x y",
        expect![[r#"
            ├─ "f" ident
            ├─ "x" ident
            └─ "y" ident
        "#]],
    );
}

#[test]
fn parse_boxed_lisp_latex_input_into_asts_works() {
    t(
        "[x]",
        expect![[r#"
            └─ "[x]" boxed list
              └─ item
                └─ "x" ident
        "#]],
    );
    t(
        "[x, y]",
        expect![[r#"
            └─ "[x, y]" boxed list
              ├─ item
              │ └─ "x" ident
              └─ item
                └─ "y" ident
        "#]],
    );
}

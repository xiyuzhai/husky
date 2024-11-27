use super::*;
use ast::helpers::tracker::LxAstTracker;
use expect_test::Expect;
use latex_prelude::helper::tracker::LxFormulaInput;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expected: Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()));
    let tracker = LxAstTracker::new(LxFormulaInput {
        specs_dir: dev_paths.specs_dir(),
        file_path,
        content,
    });
    let show = tracker.show();
    expected.assert_eq(&show);
}

#[test]
fn parse_basic_math_latex_input_into_asts_works() {
    t(
        "x",
        expect![[r#"
            └─ "x" plain letter
        "#]],
    );
    t(
        "1",
        expect![[r#"
            └─ "1" digit
        "#]],
    );
    t(
        "-x",
        expect![[r#"
            ├─ "-" punctuation
            └─ "x" plain letter
        "#]],
    );
    t(
        "x+1",
        expect![[r#"
            ├─ "x" plain letter
            ├─ "+" punctuation
            └─ "1" digit
        "#]],
    );
    t(
        "1<2",
        expect![[r#"
            ├─ "1" digit
            ├─ "<" punctuation
            └─ "2" digit
        "#]],
    );
    t(
        "1>2",
        expect![[r#"
            ├─ "1" digit
            ├─ ">" punctuation
            └─ "2" digit
        "#]],
    );
    t(
        "x^2",
        expect![[r#"
            └─ "x^2" attach
              ├─ "x" plain letter
              └─ "2" digit
        "#]],
    );
    t(
        "x_2",
        expect![[r#"
            └─ "x_2" attach
              ├─ "x" plain letter
              └─ "2" digit
        "#]],
    );
    t(
        "x^{i+2}",
        expect![[r#"
            └─ "x^{i+2}" attach
              ├─ "x" plain letter
              └─ "{i+2}" delimited
                ├─ "i" plain letter
                ├─ "+" punctuation
                └─ "2" digit
        "#]],
    );
}

#[test]
fn parse_math_extended_letter_command_latex_input_into_asts_works() {
    t(
        "\\alpha",
        expect![[r#"
            └─ "\\alpha" complete command
        "#]],
    );
    t(
        "\\beta",
        expect![[r#"
            └─ "\\beta" complete command
        "#]],
    );
    t(
        "\\gamma",
        expect![[r#"
            └─ "\\gamma" complete command
        "#]],
    );
    t(
        "\\pi",
        expect![[r#"
            └─ "\\pi" complete command
        "#]],
    );
    t(
        "\\alpha+\\beta",
        expect![[r#"
            ├─ "\\alpha" complete command
            ├─ "+" punctuation
            └─ "\\beta" complete command
        "#]],
    );
}

#[test]
fn parse_math_command_with_arguments_latex_input_into_asts_works() {
    t(
        "\\sqrt{}",
        expect![[r#"
            └─ "\\sqrt{}" complete command
              └─ 
        "#]],
    );
    t(
        "\\sqrt{1}",
        expect![[r#"
            └─ "\\sqrt{1}" complete command
              └─ 1
                └─ "1" digit
        "#]],
    );
    t(
        "\\sqrt{1+x}",
        expect![[r#"
            └─ "\\sqrt{1+x}" complete command
              └─ 1+x
                ├─ "1" digit
                ├─ "+" punctuation
                └─ "x" plain letter
        "#]],
    );
    t(
        "\\sqrt{1+x^2}+1",
        expect![[r#"
            ├─ "\\sqrt{1+x^2}" complete command
            │ └─ 1+x^2
            │   ├─ "1" digit
            │   ├─ "+" punctuation
            │   └─ "x^2" attach
            │     ├─ "x" plain letter
            │     └─ "2" digit
            ├─ "+" punctuation
            └─ "1" digit
        "#]],
    );
}

#[test]
fn parse_attach_works() {
    t(
        "x^2",
        expect![[r#"
            └─ "x^2" attach
              ├─ "x" plain letter
              └─ "2" digit
        "#]],
    );
    t(
        "(x)^2",
        expect![[r#"
            ├─ "(" punctuation
            ├─ "x" plain letter
            └─ ")^2" attach
              ├─ ")" punctuation
              └─ "2" digit
        "#]],
    );
    t(
        "{(x)}^2",
        expect![[r#"
            └─ "{(x)}^2" attach
              ├─ "{(x)}" delimited
              │ ├─ "(" punctuation
              │ ├─ "x" plain letter
              │ └─ ")" punctuation
              └─ "2" digit
        "#]],
    );
}

#[test]
fn lx_parse_environment_works() {
    t(
        "\\begin{align}x\\end{align}",
        expect![[r#"
            └─ "\\begin{align}x\\end{align}" environment
              └─ "x" plain letter
        "#]],
    );
}

#[test]
fn parse_styled_letter_works() {
    t(
        "\\mathbf{X}",
        expect![[r#"
            └─ "\\mathbf{X}" styled letter
        "#]],
    );
}

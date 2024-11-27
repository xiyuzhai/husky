use super::*;
use ast::helpers::tracker::LxAstTracker;
use expect_test::Expect;
use latex_prelude::helper::tracker::LxPageInput;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expected: Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()));
    let tracker = LxAstTracker::new(LxPageInput {
        specs_dir: dev_paths.specs_dir(),
        file_path,
        content,
    });
    let show = tracker.show();
    expected.assert_eq(&show);
}

#[test]
fn parse_basic_rose_latex_input_into_asts_works() {
    t(
        "Hello, world!",
        expect![[r#"
            ├─ "Hello" word
            ├─ "," punctuation
            ├─ "world" word
            └─ "!" punctuation
        "#]],
    );
}

#[test]
fn parse_rose_with_math_latex_input_into_asts_works() {
    t(
        "Let $x = 1$.",
        expect![[r#"
            ├─ "Let" word
            ├─ "$x = 1$" math
            │ ├─ "x" plain letter
            │ ├─ "=" punctuation
            │ └─ "1" digit
            └─ "." punctuation
        "#]],
    );
}

#[test]
fn paragraph_latex_input_into_asts_works() {
    t(
        r#"Roses are red,
Violets are blue.

Code is my passion,
And testing is too!"#,
        expect![[r#"
            ├─ "Roses" word
            ├─ "are" word
            ├─ "red" word
            ├─ "," punctuation
            ├─ "Violets" word
            ├─ "are" word
            ├─ "blue" word
            ├─ "." punctuation
            ├─ "\n\n" new paragraph
            ├─ "Code" word
            ├─ "is" word
            ├─ "my" word
            ├─ "passion" word
            ├─ "," punctuation
            ├─ "And" word
            ├─ "testing" word
            ├─ "is" word
            ├─ "too" word
            └─ "!" punctuation
        "#]],
    );
}

#[test]
fn parse_rose_equation_environment_into_latex_asts_works() {
    t(
        r#"\begin{equation}x = 1\end{equation}"#,
        expect![[r#"
            └─ "\\begin{equation}x = 1\\end{equation}" environment
              ├─ "x" plain letter
              ├─ "=" punctuation
              └─ "1" digit
        "#]],
    );
    t(
        "$x-1$",
        expect![[r#"
            └─ "$x-1$" math
              ├─ "x" plain letter
              ├─ "-" punctuation
              └─ "1" digit
        "#]],
    );
    t(
        r#"\[x-1\]"#,
        expect![[r#"
            └─ "\\[x-1\\]" math
              ├─ "x" plain letter
              ├─ "-" punctuation
              └─ "1" digit
        "#]],
    );
    t(
        r#"$$x-1$$"#,
        expect![[r#"
            └─ "$$x-1$$" math
              ├─ "x" plain letter
              ├─ "-" punctuation
              └─ "1" digit
        "#]],
    );
}

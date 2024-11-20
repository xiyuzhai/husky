use super::*;
use ast::helpers::tracker::LxAstTracker;
use expect_test::{expect, Expect};
use latex_prelude::{helper::tracker::LxDocumentInput, mode::LxMode};
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expected: Expect) {
    let db = &DB::default();
    let file_path = LxFilePath::new(db, PathBuf::from(file!()));
    let tracker = LxAstTracker::new(LxDocumentInput { file_path, content }, db);
    let show = tracker.show(db);
    expected.assert_eq(&show);
}

#[test]
fn parse_use_packages_into_lx_root_asts_works() {
    t(
        "\\documentclass{article}",
        expect![[r#"
            └─ "\\documentclass{article}" complete command
              └─ article
        "#]],
    );
    t(
        "\\usepackage{amsmath}",
        expect![[r#"
            └─ "\\usepackage{amsmath}" complete command
              └─ amsmath
        "#]],
    );
    t(
        "\\usepackage[utf8]{inputenc}",
        expect![[r#"
            └─ "\\usepackage[utf8]{inputenc}" complete command
              └─ inputenc
        "#]],
    );
}

#[test]
fn parse_document_environment_works() {
    t(
        r#"\begin{document}\end{document}"#,
        expect![[r#"
            └─ "\\begin{document}\\end{document}" environment
        "#]],
    );
    t(
        r#"\begin{document}Hello\end{document}"#,
        expect![[r#"
            └─ "\\begin{document}Hello\\end{document}" environment
              └─ "Hello" word
        "#]],
    );
    t(
        r#"\begin{document}Let $x\in\mathbb{R}$.\end{document}"#,
        expect![[r#"
            └─ "\\begin{document}Let $x\\in\\mathbb{R}$.\\end{document}" environment
              ├─ "Let" word
              ├─ "$x\\in\\mathbb{R}$" math
              │ ├─ "x" plain letter
              │ ├─ "\\in" complete command
              │ └─ "\\mathbb{R}" styled letter
              └─ "." punctuation
        "#]],
    );
}

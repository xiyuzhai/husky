use super::*;
use crate::helpers::tracker::VdSemExprTracker;
use expect_test::{expect, Expect};
use latex_prelude::helper::tracker::LxDocumentBodyInput;
use latex_prelude::mode::LxMode;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expect: &Expect) {
    let db = &DB::default();
    let file_path = LxFilePath::new(db, PathBuf::from(file!()));
    let tracker = VdSemExprTracker::new(LxDocumentBodyInput { file_path, content }, &[], &[], db);
    expect.assert_eq(&tracker.show_display_tree(db));
}

#[test]
fn basic_body_to_vd_mir_works() {
    t(
        r#"Let $x\in\mathbb{R}$."#,
        &expect![[r#"
            └─ "Let $x\\in\\mathbb{R}$." division.stmts
              └─ "Let $x\\in\\mathbb{R}$." stmt.paragraph
                └─ "Let $x\\in\\mathbb{R}$." sentence.clauses
                  └─ "Let $x\\in\\mathbb{R}$" clause.let
                    └─ "x\\in\\mathbb{R}" expr.separated_list
                      ├─ "x" expr.letter
                      └─ "\\mathbb{R}" expr.letter
        "#]],
    );
    t(
        r#"\begin{example}\end{example}"#,
        &expect![[r#"
            └─ "\\begin{example}\\end{example}" division.stmts
              └─ "\\begin{example}\\end{example}" stmt.block
        "#]],
    );
    t(
        r#"\begin{example}Let $x\in\mathbb{R}$.\end{example}"#,
        &expect![[r#"
            └─ "\\begin{example}Let $x\\in\\mathbb{R}$.\\end{example}" division.stmts
              └─ "\\begin{example}Let $x\\in\\mathbb{R}$.\\end{example}" stmt.block
                └─ "Let $x\\in\\mathbb{R}$." stmt.paragraph
                  └─ "Let $x\\in\\mathbb{R}$." sentence.clauses
                    └─ "Let $x\\in\\mathbb{R}$" clause.let
                      └─ "x\\in\\mathbb{R}" expr.separated_list
                        ├─ "x" expr.letter
                        └─ "\\mathbb{R}" expr.letter
        "#]],
    );
}

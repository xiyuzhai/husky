use super::*;
use expect_test::{expect, Expect};
use helpers::tracker::VdSemExprTracker;
use latex_prelude::helper::tracker::LxPageInput;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

pub(crate) fn t(content: &str, expected: &Expect) {
    let db = &DB::default();
    let file_path = LxFilePath::new(db, PathBuf::from(file!()));
    let tracker = VdSemExprTracker::new(LxPageInput { file_path, content }, &[], &[], db);
    expected.assert_eq(&tracker.show_display_tree(db))
}

#[test]
pub(crate) fn basic_vd_sem_clause_works() {
    t(
        "Let $x=1$. Let $y=-2x$.",
        &expect![[r#"
            Let $x=1$. Let $y=-2x$.
            └─ "Let $x=1$. Let $y=-2x$." stmt.paragraph
              ├─ "Let $x=1$." sentence.clauses
              │ └─ "Let $x=1$" clause.let
              │   └─ "x=1" expr.separated_list
              │     ├─ "x" expr.letter
              │     └─ "1" expr.literal
              └─ "Let $y=-2x$." sentence.clauses
                └─ "Let $y=-2x$" clause.let
                  └─ "y=-2x" expr.separated_list
                    ├─ "y" expr.letter
                    └─ "-2x" expr.prefix
                      └─ "2x" expr.separated_list
                        ├─ "2" expr.literal
                        └─ "x" expr.letter
        "#]],
    );
    t(
        "Let $x\\in \\mathbb{N}$. Assume $x=1$.",
        &expect![[r#"
            Let $x\in \mathbb{N}$. Assume $x=1$.
            └─ "Let $x\\in \\mathbb{N}$. Assume $x=1$." stmt.paragraph
              ├─ "Let $x\\in \\mathbb{N}$." sentence.clauses
              │ └─ "Let $x\\in \\mathbb{N}$" clause.let
              │   └─ "x\\in \\mathbb{N}" expr.separated_list
              │     ├─ "x" expr.letter
              │     └─ "\\mathbb{N}" expr.letter
              └─ "Assume $x=1$." sentence.clauses
                └─ "Assume $x=1$" clause.assume
                  └─ "x=1" expr.separated_list
                    ├─ "x" expr.letter
                    └─ "1" expr.literal
        "#]],
    );
    // t(
    //     "Let $x=1$. Then $x=1$.",
    //     &expect![[r#"
    //         Let $x=1$. Then $x=1$.
    //         └─ "Let $x=1$. Then $x=1$." stmt.paragraph
    //           ├─ "Let $x=1$." sentence.clauses
    //           │ └─ "Let $x=1$" clause.let
    //           │   └─ "x=1" expr.separated_list
    //           │     ├─ "x" expr.letter
    //           │     └─ "1" expr.literal
    //           └─ "Then $x=1$." sentence.clauses
    //             └─ "Then $x=1$" clause.then
    //               └─ "x=1" expr.separated_list
    //                 ├─ "x" expr.letter
    //                 └─ "1" expr.literal
    //     "#]],
    // );
    // t(
    //     "Let $x=1$. Let $y\\in \\mathbb{N}$. Assume $y=2$. Then $x+y=3$.",
    //     &expect![[r#"
    //         Let $x=1$. Let $y\in \mathbb{N}$. Assume $y=2$. Then $x+y=3$.
    //         └─ "Let $x=1$. Let $y\\in \\mathbb{N}$. Assume $y=2$. Then $x+y=3$." stmt.paragraph
    //           ├─ "Let $x=1$." sentence.clauses
    //           │ └─ "Let $x=1$" clause.let
    //           │   └─ "x=1" expr.separated_list
    //           │     ├─ "x" expr.letter
    //           │     └─ "1" expr.literal
    //           ├─ "Let $y\\in \\mathbb{N}$." sentence.clauses
    //           │ └─ "Let $y\\in \\mathbb{N}$" clause.let
    //           │   └─ "y\\in \\mathbb{N}" expr.separated_list
    //           │     ├─ "y" expr.letter
    //           │     └─ "\\mathbb{N}" expr.letter
    //           ├─ "Assume $y=2$." sentence.clauses
    //           │ └─ "Assume $y=2$" clause.assume
    //           │   └─ "y=2" expr.separated_list
    //           │     ├─ "y" expr.letter
    //           │     └─ "2" expr.literal
    //           └─ "Then $x+y=3$." sentence.clauses
    //             └─ "Then $x+y=3$" clause.then
    //               └─ "x+y=3" expr.separated_list
    //                 ├─ "x+y" expr.separated_list
    //                 │ ├─ "x" expr.letter
    //                 │ └─ "y" expr.letter
    //                 └─ "3" expr.literal
    //     "#]],
    // );
}

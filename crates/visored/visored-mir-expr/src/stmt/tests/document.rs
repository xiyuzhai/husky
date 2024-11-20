use super::*;
use expect_test::{expect, Expect};
use helpers::tracker::VdMirExprTracker;
use latex_prelude::helper::tracker::LxDocumentInput;
use latex_prelude::mode::LxMode;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expect: &Expect) {
    let db = &DB::default();
    let file_path = LxFilePath::new(db, PathBuf::from(file!()));
    let tracker = VdMirExprTracker::new(LxDocumentInput { file_path, content }, &[], &[], db);
    expect.assert_eq(&tracker.show_display_tree(db));
}

#[test]
fn basic_document_to_vd_mir_works() {
    t(
        r#"\documentclass{article}
\usepackage{amsmath}
\begin{document}
Let $x\in\mathbb{R}$.
\end{document}"#,
        &expect![[r#"
            └─ block: Division(Stmts, VdModulePath(Id { value: 2 }))
              └─ block: Paragraph
                └─ block: Sentence
                  └─ let placeholder
        "#]],
    );
    t(
        r#"\documentclass{article}
\usepackage{amsmath}
\begin{document}
\section{Introduction}
Let $x\in\mathbb{R}$.
\end{document}"#,
        &expect![[r#"
            └─ block: Division(Section, VdModulePath(Id { value: 2 }))
              └─ block: Division(Stmts, VdModulePath(Id { value: 3 }))
                └─ block: Paragraph
                  └─ block: Sentence
                    └─ let placeholder
        "#]],
    );
    t(
        r#"\documentclass{article}
\usepackage{amsmath}
\begin{document}
\section{Introduction}
Let $x\in\mathbb{R}$.
\subsection{Hello}
Let $y\in\mathbb{R}$.
\subsection{World}
\subsection{This}
\subsubsection{Is}
\subsubsection{Bad}
\end{document}"#,
        &expect![[r#"
            └─ block: Division(Section, VdModulePath(Id { value: 2 }))
              ├─ block: Division(Stmts, VdModulePath(Id { value: 3 }))
              │ └─ block: Paragraph
              │   └─ block: Sentence
              │     └─ let placeholder
              ├─ block: Division(Subsection, VdModulePath(Id { value: 5 }))
              │ └─ block: Division(Stmts, VdModulePath(Id { value: 6 }))
              │   └─ block: Paragraph
              │     └─ block: Sentence
              │       └─ let placeholder
              ├─ block: Division(Subsection, VdModulePath(Id { value: 8 }))
              └─ block: Division(Subsection, VdModulePath(Id { value: 9 }))
                ├─ block: Division(Subsubsection, VdModulePath(Id { value: 10 }))
                └─ block: Division(Subsubsection, VdModulePath(Id { value: 11 }))
        "#]],
    );
}

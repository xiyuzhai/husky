use super::*;
use expect_test::{expect, Expect};
use helpers::tracker::VdMirExprTracker;
use latex_prelude::helper::tracker::LxDocumentInput;
use latex_prelude::mode::LxMode;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;

fn t(content: &str, expect: &Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()));
    let tracker = VdMirExprTracker::new(
        LxDocumentInput {
            specs_dir: dev_paths.specs_dir(),
            file_path,
            content,
        },
        &[],
        &[],
    );
    expect.assert_eq(&tracker.show_display_tree());
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
            └─ block: Division(Stmts, VdModulePath(`root.stmts1`))
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
            └─ block: Division(Section, VdModulePath(`root.section1`))
              └─ block: Division(Stmts, VdModulePath(`root.section1.stmts1`))
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
            └─ block: Division(Section, VdModulePath(`root.section1`))
              ├─ block: Division(Stmts, VdModulePath(`root.section1.stmts1`))
              │ └─ block: Paragraph
              │   └─ block: Sentence
              │     └─ let placeholder
              ├─ block: Division(Subsection, VdModulePath(`root.section1.subsection1`))
              │ └─ block: Division(Stmts, VdModulePath(`root.section1.subsection1.stmts1`))
              │   └─ block: Paragraph
              │     └─ block: Sentence
              │       └─ let placeholder
              ├─ block: Division(Subsection, VdModulePath(`root.section1.subsection2`))
              └─ block: Division(Subsection, VdModulePath(`root.section1.subsection3`))
                ├─ block: Division(Subsubsection, VdModulePath(`root.section1.subsection3.subsubsection1`))
                └─ block: Division(Subsubsection, VdModulePath(`root.section1.subsection3.subsubsection2`))
        "#]],
    );
}

use super::*;
use crate::elaborator::VdMirTrivialElaborator;
use eterned::db::EternerDb;
use expect_test::{expect, Expect};
use helpers::tracker::VdMirExprTracker;
use latex_prelude::helper::tracker::LxDocumentInput;
use latex_prelude::mode::LxMode;
use latex_vfs::path::LxFilePath;
use std::path::PathBuf;
use visored_syn_expr::vibe::VdSynExprVibe;

fn t(models: &VdModels, content: &str, expect: &Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let db = &EternerDb::default();
    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()), db);
    let tracker = VdMirExprTracker::new(
        LxDocumentInput {
            specs_dir: dev_paths.specs_dir().to_path_buf(),
            file_path,
            content,
        },
        &[],
        &[],
        models,
        VdSynExprVibe::ROOT_CNL,
        db,
        |_| VdMirTrivialElaborator::new(()),
    );
    expect.assert_eq(&tracker.show_display_tree(db));
}

#[test]
fn basic_document_to_vd_mir_works() {
    let models = &VdModels::new();
    t(
        models,
        r#"\documentclass{article}
\usepackage{amsmath}
\begin{document}
Let $x\in\mathbb{R}$.
\end{document}"#,
        &expect![[r#"
            └─ block: Division(Blocks, VdModulePath(`root.stmts1`))
              ├─ let placeholder
              └─ qed
        "#]],
    );
    t(
        models,
        r#"\documentclass{article}
\usepackage{amsmath}
\begin{document}
\section{Introduction}
Let $x\in\mathbb{R}$.
\end{document}"#,
        &expect![[r#"
            └─ block: Division(Section, VdModulePath(`root.section1`))
              └─ block: Division(Blocks, VdModulePath(`root.section1.stmts1`))
                ├─ let placeholder
                └─ qed
        "#]],
    );
    t(
        models,
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
              ├─ block: Division(Blocks, VdModulePath(`root.section1.stmts1`))
              │ ├─ let placeholder
              │ └─ qed
              ├─ block: Division(Subsection, VdModulePath(`root.section1.subsection1`))
              │ └─ block: Division(Blocks, VdModulePath(`root.section1.subsection1.stmts1`))
              │   ├─ let placeholder
              │   └─ qed
              ├─ block: Division(Subsection, VdModulePath(`root.section1.subsection2`))
              └─ block: Division(Subsection, VdModulePath(`root.section1.subsection3`))
                ├─ block: Division(Subsubsection, VdModulePath(`root.section1.subsection3.subsubsection1`))
                └─ block: Division(Subsubsection, VdModulePath(`root.section1.subsection3.subsubsection2`))
        "#]],
    );
}

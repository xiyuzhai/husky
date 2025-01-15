use super::*;
use crate::scheme::sparse::VdLeanTranspilationSparseScheme;
use visored_mir_expr::elaborator::VdMirTrivialElaborator;
use visored_syn_expr::vibe::VdSynExprVibe;

fn t(models: &VdModels, content: &str, expected_display_tree: &Expect, expected_fmt: &Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let db = &EternerDb::default();
    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()), db);
    let tracker = VdLeanTranspilationTracker::new::<VdMirTrivialElaborator>(
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
        &VdLeanTranspilationSparseScheme,
    );
    expected_display_tree.assert_eq(&tracker.show_display_tree(db));
    expected_fmt.assert_eq(&tracker.show_fmt(db));
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
            └─ group: `division`
              └─ variable: `x`
        "#]],
        &expect!["variable (x : ℝ)"],
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
            └─ group: `division`
              └─ group: `division`
                └─ variable: `x`
        "#]],
        &expect![[r#"
            namespace Section1
            variable (x : ℝ)
            end Section1
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
            └─ group: `division`
              ├─ group: `division`
              │ └─ variable: `x`
              ├─ group: `division`
              │ └─ group: `division`
              │   └─ variable: `y`
              ├─ group: `division`
              └─ group: `division`
                ├─ group: `division`
                └─ group: `division`
        "#]],
        &expect![[r#"
            namespace Section1
            variable (x : ℝ)

            namespace Subsection1
            variable (y : ℝ)
            end Subsection1

            namespace Subsection2
            end Subsection2

            namespace Subsection3
            namespace Subsubsection1
            end Subsubsection1

            namespace Subsubsection2
            end Subsubsection2
            end Subsection3
            end Section1
        "#]],
    );
}

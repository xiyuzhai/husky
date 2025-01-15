use visored_mir_expr::elaborator::VdMirTrivialElaborator;
use visored_syn_expr::vibe::VdSynExprVibe;

use super::*;
use crate::scheme::dense::VdLeanTranspilationDenseScheme;

fn t(models: &VdModels, content: &str, expected_display_tree: &Expect, expected_fmt: &Expect) {
    use husky_path_utils::HuskyLangDevPaths;

    let db = &EternerDb::default();
    let dev_paths = HuskyLangDevPaths::new();
    let file_path = LxFilePath::new(PathBuf::from(file!()), db);
    let tracker = VdLeanTranspilationTracker::new(
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
        &VdLeanTranspilationDenseScheme,
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
              └─ def: `h`
                ├─ item path: `ℝ`
                └─ tactics
                  └─ tactic: `Exact { term: 1 }`
        "#]],
        &expect![[r#"
            def h (x : ℝ) := by
              exact ()"#]],
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
                └─ def: `h`
                  ├─ item path: `ℝ`
                  └─ tactics
                    └─ tactic: `Exact { term: 1 }`
        "#]],
        &expect![[r#"
            namespace Section1
            def h (x : ℝ) := by
              exact ()
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
              │ └─ def: `h`
              │   ├─ item path: `ℝ`
              │   └─ tactics
              │     └─ tactic: `Exact { term: 1 }`
              ├─ group: `division`
              │ └─ group: `division`
              │   └─ def: `h`
              │     ├─ item path: `ℝ`
              │     └─ tactics
              │       └─ tactic: `Exact { term: 3 }`
              ├─ group: `division`
              └─ group: `division`
                ├─ group: `division`
                └─ group: `division`
        "#]],
        &expect![[r#"
            namespace Section1
            def h (x : ℝ) := by
              exact ()

            namespace Subsection1
            def h (y : ℝ) := by
              exact ()
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

#[test]
fn latex_shorts_to_lean_works() {
    use expect_test::expect_file;
    use husky_path_utils::HuskyLangDevPaths;
    use std::fs;

    let db = &EternerDb::default();
    let dev_paths = HuskyLangDevPaths::new();
    let projects_dir = dev_paths.projects_dir();
    let models = &VdModels::new();
    for file in fs::read_dir(projects_dir.join("ai-math-autoformalization/latex/shorts")).unwrap() {
        let file = file.unwrap();
        let file_path = file.path();
        if file_path.extension() != Some(&std::ffi::OsStr::new("tex")) {
            continue;
        }
        let content = &fs::read_to_string(&file_path).unwrap();
        let filestem = file_path.file_stem().unwrap().to_str().unwrap();
        let file_path = LxFilePath::new(file_path.clone(), db);
        let tracker = VdLeanTranspilationTracker::new(
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
            &VdLeanTranspilationDenseScheme,
        );
        expect_file![projects_dir.join(format!(
            "ai-math-autoformalization/lean/central-46/Central46/Shorts/{}.lean",
            filestem
        ))]
        .assert_eq(&format!(
            r#"import Mathlib
import Obvious
open Obvious

{}"#,
            tracker.show_fmt(db)
        ));
    }
}

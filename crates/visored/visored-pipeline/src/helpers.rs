use std::path::Path;

use crate::{
    instance::VdPipelineInstance,
    runner::{VdPipelineInstanceFile, VdPipelineRunner},
};
use relative_path::{RelativePathBuf, RelativeToError};

const LATEX_DOCUMENT_PREFIX: &'static str = r#"%!TEX TS-program = xelatex
\documentclass{article}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{fvextra}
\usepackage{tcolorbox}
\usepackage{listings}
\usepackage{amsthm}
\usepackage{fontspec}  % For Unicode support
\setmonofont{DejaVu Sans Mono}  % For monospace/code blocks
\usepackage{unicode-math}
% \setmathfont{XITS Math}  % Or another Unicode math font
\newtheorem{example}{Example}
\fvset{breaklines=true}



\begin{document}
\lstdefinelanguage{Lean4}{
    breaklines=true,
    basicstyle=\ttfamily\normalsize,
    keepspaces=true,
    morekeywords={
        def, theorem, lemma, example, have, show, calc, let, assume, by, exact,
        sorry, obvious, Type, Prop, where, with, extends, class, instance,
        structure, inductive, mutual, coinductive, variable, variables,
        universe, universes, deriving, abbrev, partial, terminating,
        namespace, import, open, export, private, protected, public,
        noncomputable, unsafe, macro, syntax, macro_rules, set_option,
        attribute, local, scoped, section, end, match, fun, if, then, else,
        return, do, for, in, while, break, continue, try, catch, throw,
        mut, pure, opaque
    },
    morekeywords=[2]{
        ℕ, ℝ, ∈, ≥, ≤, →, ∀, ∃, ⊢, ∧, ∨, ¬, ≠, ×, ⊗, ⊕, ∘, □, ◇, ∎,
        ⟨, ⟩, ⦃, ⦄, ▸, ≈, ∼, ≡, ⌊, ⌋, ⌈, ⌉
    },
    morecomment=[l]--,     % Line comments start with --
    morestring=[b]",       % Strings in double quotes
    sensitive=true,         % Case-sensitive
    keywordstyle=\color{blue}\bfseries,      % Regular keywords in blue and bold
    keywordstyle=[2]\color{purple}\bfseries, % Special symbols in purple and bold
    commentstyle=\color{green!50!black},     % Comments in dark green
    stringstyle=\color{red},                 % Strings in red
}

"#;

const LATEX_DOCUMENT_SUFFIX: &'static str = r#"\end{document}"#;

const LATEX_MATH_PREFIX: &'static str = r#"\begin{align*}"#;
const LATEX_MATH_SUFFIX: &'static str = r#"\end{align*}"#;

pub struct VdPipelineResultLatexFile {
    pub relative_path: RelativePathBuf,
    pub latex_content: String,
}

impl<'db> VdPipelineRunner<'db> {
    /// Returns pipeline results as LaTeX files.
    ///
    /// Returns pairs of `(relative_path, latex_content)` for each generated file.
    pub fn export_result_latex_files(
        &self,
        parent_dir: impl AsRef<Path>,
    ) -> Result<Vec<VdPipelineResultLatexFile>, RelativeToError> {
        let mut latex_files = Vec::new();
        let parent_dir = parent_dir.as_ref();
        for instance_file in self.instance_files() {
            use relative_path::PathExt;
            let relative_path = instance_file.path.relative_to(parent_dir)?;
            let latex_content = instance_file.result_latex_content(self);
            latex_files.push(VdPipelineResultLatexFile {
                relative_path,
                latex_content,
            });
        }
        Ok(latex_files)
    }
}

impl VdPipelineInstanceFile {
    pub fn result_latex_content(&self, runner: &VdPipelineRunner) -> String {
        let mut latex_content = LATEX_DOCUMENT_PREFIX.to_string();
        for (input, instance_idx_range) in &self.instances {
            for instance_idx in instance_idx_range {
                let instance = &runner[instance_idx];
                instance.write_result_latex_content(&mut latex_content);
            }
        }
        latex_content.push_str(LATEX_DOCUMENT_SUFFIX);
        latex_content
    }
}

impl VdPipelineInstance {
    pub fn write_result_latex_content(&self, latex_content: &mut String) {
        use std::fmt::Write;

        let tracker = self.tracker();
        write!(
            latex_content,
            r#"

\begin{{example}}
Problem:
\begin{{tcolorbox}}[colback=yellow!10, width=\linewidth]
{}
\end{{tcolorbox}}

Simplified proof:
\begin{{tcolorbox}}[colback=blue!10, width=\linewidth]
{}
\end{{tcolorbox}}
\end{{example}}

Elaborated proof:
\begin{{tcolorbox}}[colback=green!10, width=\linewidth]
{}
\end{{tcolorbox}}

Regularized proof:
\begin{{tcolorbox}}[colback=red!10, width=\linewidth]
{}
\end{{tcolorbox}}
"#,
            tracker.input.content,
            tracker.simplified_proof.1,
            tracker.elaborated_proof.1,
            tracker.regularized_proof.1,
        )
        .unwrap();
    }
}

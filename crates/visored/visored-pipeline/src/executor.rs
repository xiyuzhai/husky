mod transformations;

use crate::*;
use all_llms::transformation::AllLlmsStringTransformationRecord;
use all_llms::{model::AllLlmModel, AllLlmsClient};
use eterned::db::EternerDb;
use husky_io_utils::diff_write;
use input::VdPipelineInput;
use latex_prelude::helper::tracker::LxDocumentBodyInput;
use latex_vfs::path::LxFilePath;
use lean_helpers::hypothesis::HYPOTHESIS_HEADER;
use lean_helpers::obvious::OBVIOUS_HEADER;
use lean_mir_expr::helpers::ad_hoc_header::AD_HOC_HEADER;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use visored_baseq_elaborator::{
    elaborator::{VdBsqElaborator, VdBsqElaboratorInner},
    session::VdBsqSession,
};
use visored_lean_transpilation::{
    helpers::tracker::VdLeanTranspilationTracker, scheme::dense::VdLeanTranspilationDenseScheme,
};
use visored_mir_expr::elaborator::VdMirTrivialElaborator;
use visored_models::VdModels;
use visored_syn_expr::vibe::VdSynExprVibe;

pub struct VdPipelineExecutor<'a, 'db> {
    db: &'db EternerDb,
    // TODO: replace with preloaded specs???
    specs_dir: &'a Path,
    lean4_dir: &'a Path,
    input: &'a VdPipelineInput,
    config: &'a VdPipelineConfig,
    llm_client: AllLlmsClient<'db>,
    raw_proof: Option<String>,
    simplified_proof: Option<(Vec<AllLlmsStringTransformationRecord>, String)>,
    elaborated_proof: Option<(Vec<AllLlmsStringTransformationRecord>, String)>,
    regularized_proof: Option<(Vec<AllLlmsStringTransformationRecord>, String)>,
    lean4_code: Option<String>,
}

impl<'a, 'db> VdPipelineExecutor<'a, 'db> {
    pub fn new(
        db: &'db EternerDb,
        tokio_runtime: Arc<tokio::runtime::Runtime>,
        // TODO: replace with preloaded specs???
        specs_dir: &'a Path,
        lean4_dir: &'a Path,
        input: &'a VdPipelineInput,
        config: &'a VdPipelineConfig,
    ) -> Self {
        let base = input.file_path.parent().unwrap();
        let cache_dir = config.data.cache_dir.to_logical_path(base).join(format!(
            "{}/example-{}",
            input.file_path.file_stem().unwrap().to_str().unwrap(),
            input.index
        ));
        std::fs::create_dir_all(&cache_dir).unwrap();
        Self {
            db,
            specs_dir,
            lean4_dir,
            input,
            config,
            llm_client: AllLlmsClient::new(db, tokio_runtime, cache_dir).unwrap(),
            raw_proof: None,
            simplified_proof: None,
            elaborated_proof: None,
            regularized_proof: None,
            lean4_code: None,
        }
    }
}

impl<'a, 'db> VdPipelineExecutor<'a, 'db> {
    pub(crate) fn execute_all(&mut self) {
        self.query_raw_proof();
    }

    fn query_raw_proof(&mut self) {
        let prompt = format!(
            r#"Please provide the raw solution to the following problem. The solution should be a concise and complete mathematical proof written in LaTeX. If something is straightforward and trivial as seen by college level student, just say that it's trivial and don't ever try to say unnecessary things.

```latex
{}
```

Provide only the LaTeX code for the solution, without any surrounding text. Wrap the proof in \begin{{proof}} and \end{{proof}}. The solution should:
- Start from given information and progress logically forward to the conclusion
- Show each step's reasoning clearly
- Build upon previous steps in a natural progression
- Use appropriate mathematical notation and LaTeX environments
- Avoid unnecessary labels or references
- If the problem is trivially true, just finish the proof in one sentence by restating the conclusion. Keep the normal amount of details.
- Avoid unnecessary repetitions.
- Avoid introducing unnecessary variables.

Here are some examples that help you understand the task.

------- EXAMPLES -------
Problem: prove that $(x+y)^2 \ge 0$ for all real numbers $x$.

Solution:
```latex
\begin{{proof}}
We have $(x+y)^2 \ge 0$ because these are real numbers.
\end{{proof}}
```

Problem: prove that $x^2 \ge 0$ for all real numbers $x$.

Solution:
```latex
\begin{{proof}}
We have $x^2 \ge 0$ because these are real numbers.
\end{{proof}}
```

------- END OF EXAMPLES -------
"#,
            self.input.content
        );
        self.raw_proof = Some(extract_proof(
            &self
                .llm_client
                .generate_text(
                    self.config
                        .routing_resolved
                        .solver
                        .mathematical_reasoning
                        .model,
                    prompt,
                )
                .unwrap(),
        ));
        let input_and_raw_proof = format!(
            r#"```latex
\begin{{example}}
{}
\end{{example}}

\begin{{proof}}
{}
\end{{proof}}
```"#,
            self.input.content,
            self.raw_proof.as_ref().unwrap()
        );
        let (transformations, simplified_proof) = self
            .llm_client
            .apply_transformations_sequentially(
                &self.config.simplification_transformations(),
                input_and_raw_proof,
            )
            .unwrap();
        let simplified_proof = extract_proof(&simplified_proof);
        let input_and_simplified_proof = format!(
            r#"```latex
\begin{{example}}
{}
\end{{example}}

\begin{{proof}}
{}
\end{{proof}}
```"#,
            self.input.content, simplified_proof
        );
        self.simplified_proof = Some((transformations, simplified_proof));
        let (transformations, elaborated_proof) = self
            .llm_client
            .apply_transformations_sequentially(
                &self.config.elaboration_transformations(),
                input_and_simplified_proof,
            )
            .unwrap();
        let elaborated_proof = extract_proof(&elaborated_proof);
        let input_and_elaborated_proof = format!(
            r#"```latex
\begin{{example}}
{}
\end{{example}}

\begin{{proof}}
{}
\end{{proof}}
```"#,
            self.input.content, elaborated_proof
        );
        self.elaborated_proof = Some((transformations, elaborated_proof));
        let (transformations, regularized_proof) = self
            .llm_client
            .apply_transformations_sequentially(
                &self.config.regularization_transformations(),
                input_and_elaborated_proof,
            )
            .unwrap();
        let regularized_proof = extract_proof(&regularized_proof);
        self.regularized_proof = Some((transformations, regularized_proof.clone()));
        let file_path = LxFilePath::new(PathBuf::from(file!()), self.db);
        let tracker = VdLeanTranspilationTracker::new::<VdBsqElaborator>(
            LxDocumentBodyInput {
                specs_dir: self.specs_dir,
                file_path,
                content: &regularized_proof,
            },
            &[],
            &[],
            &VdModels {},
            VdSynExprVibe::ROOT_CNL,
            self.db,
            &VdLeanTranspilationDenseScheme,
        );
        self.lean4_code = Some(format!(
            r#"import Mathlib
{OBVIOUS_HEADER}
{AD_HOC_HEADER}
{HYPOTHESIS_HEADER}
{}
"#,
            tracker.show_fmt(self.db)
        ));
        let lean4_code_path = self
            .input
            .relative_path
            .to_logical_path(self.lean4_dir)
            .with_extension("")
            .join(format!("example-{}.lean", self.input.index + 1));
        if let Some(parent) = lean4_code_path.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        diff_write(&lean4_code_path, self.lean4_code.as_ref().unwrap(), true);
        // p!(lake_lean(&lean4_code_path));
        // todo!("compile lean4 code");
    }

    pub(crate) fn finish(
        self,
    ) -> (
        String,
        (Vec<AllLlmsStringTransformationRecord>, String),
        (Vec<AllLlmsStringTransformationRecord>, String),
        (Vec<AllLlmsStringTransformationRecord>, String),
        String,
    ) {
        (
            self.raw_proof.unwrap(),
            self.simplified_proof.unwrap(),
            self.elaborated_proof.unwrap(),
            self.regularized_proof.unwrap(),
            self.lean4_code.unwrap(),
        )
    }
}

const PROOF_BEGIN: &str = "\\begin{proof}";
const PROOF_END: &str = "\\end{proof}";

fn extract_proof(s: &str) -> String {
    assert!(s.contains(PROOF_BEGIN));
    assert!(s.contains(PROOF_END));
    let start = s.find(PROOF_BEGIN).unwrap();
    let end = s.find(PROOF_END).unwrap();
    let content = &s[start + PROOF_BEGIN.len()..end];
    content
        .trim()
        .replace("$$", "$")
        .replace("\\[", "$")
        .replace("\\]", "$")
}

#[test]
fn extract_proof_works() {
    #[track_caller]
    fn t(input: &str, expected: &str) {
        assert_eq!(extract_proof(input), expected);
    }
    t(
        r"
Here's the solution:

```latex
\begin{proof}
\begin{align*}
x^2 + 2x + 1 = 0
\end{align*}
\end{proof}
```
",
        r"\begin{align*}
x^2 + 2x + 1 = 0
\end{align*}",
    );
}

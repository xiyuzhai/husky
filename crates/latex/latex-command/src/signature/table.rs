use super::*;
use crate::path::{
    menu::{command_path_menu, LxCommandPathMenu},
    LxCommandName,
};
use latex_prelude::mode::LxMode;
use parameter::{LxCommandParameter, LxCommandParameterMode};
use rustc_hash::FxHashMap;

#[salsa::derive_debug_with_db]
#[derive(Debug)]
pub struct LxCommandSignatureTable {
    pub signatures: FxHashMap<LxCommandName, LxCommandSignature>,
}

impl LxCommandSignatureTable {
    // TODO: return a closest match if the command is not found
    pub fn signature(&self, index: LxCommandName) -> Option<&LxCommandSignature> {
        self.signatures.get(&index)
    }
}

impl LxCommandSignatureTable {
    fn new(
        begin: LxCommandPath,
        end: LxCommandPath,
        letter_style_commands: &[(LxCommandPath, LxMathLetterStyle)],
        complete_commands: &[(LxCommandPath, &[LxCommandParameterMode])],
    ) -> Self {
        Self {
            signatures: [
                (begin.name(), LxCommandSignature::Begin),
                (end.name(), LxCommandSignature::End),
            ]
            .into_iter()
            .chain(
                letter_style_commands
                    .iter()
                    .copied()
                    .map(|(path, style)| (path.name(), LxCommandSignature::MathLetterStyle(style))),
            )
            .chain(
                complete_commands
                    .into_iter()
                    .copied()
                    .map(|(path, parameter_modes)| {
                        (
                            path.name(),
                            LxCommandSignature::Complete(LxCompleteCommandSignature {
                                path,
                                options: (),
                                parameters: parameter_modes
                                    .into_iter()
                                    .copied()
                                    .map(LxCommandParameter::new)
                                    .collect(),
                            }),
                        )
                    }),
            )
            .collect(),
        }
    }
}

impl std::ops::Deref for LxCommandSignatureTable {
    type Target = FxHashMap<LxCommandName, LxCommandSignature>;

    fn deref(&self) -> &Self::Target {
        &self.signatures
    }
}

impl LxCommandSignatureTable {
    pub fn new_default(db: &salsa::Db) -> Self {
        use LxCommandParameterMode::*;

        let LxCommandPathMenu {
            // - root
            begin,
            end,
            usepackage,
            documentclass,
            newtheorem,
            // - divisions
            part,
            chapter,
            section,
            subsection,
            subsubsection,
            // - maths
            // ## letter style
            mathbb,
            mathbf,
            mathcal,
            mathit,
            mathrm,
            mathsf,
            mathscr,
            // - operators
            // -- relations
            eq,
            ne,
            le,
            ge,
            r#in,
            subset,
            supset,
            subseteq,
            supseteq,
            subseteqq,
            supseteqq,
            subsetneq,
            supsetneq,
            // -- arithmetic
            int,
            sum,
            prod,
            times,
            otimes,
            // -- extended letters
            alpha,
            beta,
            gamma,
            pi,
            // -- functions
            sin,
            cos,
            // -- layouts
            sqrt,
            frac,
            text,
        } = *command_path_menu(db);
        Self::new(
            begin,
            end,
            &[
                (mathbb, LxMathLetterStyle::MATHBB),
                (mathbf, LxMathLetterStyle::MATHFRAK),
                (mathcal, LxMathLetterStyle::MATHCAL),
                (mathit, LxMathLetterStyle::MATHIT),
                (mathrm, LxMathLetterStyle::MATHRM),
                (mathsf, LxMathLetterStyle::MATHSF),
                (mathscr, LxMathLetterStyle::MATHSCR),
            ],
            &[
                // - root
                (usepackage, &[Name]),
                (documentclass, &[Name]),
                (newtheorem, &[Name, Name]),
                // - divisions
                (part, &[Rose]),
                (chapter, &[Rose]),
                (section, &[Rose]),
                (subsection, &[Rose]),
                (subsubsection, &[Rose]),
                // - operators
                // -- relations
                (eq, &[]),
                (ne, &[]),
                (le, &[]),
                (ge, &[]),
                (r#in, &[]),
                (subset, &[]),
                (supset, &[]),
                (subseteq, &[]),
                (supseteq, &[]),
                (subseteqq, &[]),
                (supseteqq, &[]),
                (subsetneq, &[]),
                (supsetneq, &[]),
                // -- arithmetic
                (int, &[]),
                (sum, &[]),
                (prod, &[]),
                (times, &[]),
                (otimes, &[]),
                // -- extended letters
                (alpha, &[]),
                (beta, &[]),
                (gamma, &[]),
                (pi, &[]),
                // -- functions
                (sqrt, &[Math]),
                (sin, &[]),
                (cos, &[]),
                // -- layouts
                (frac, &[Math, Math]),
                (text, &[Rose]),
            ],
        )
    }
}

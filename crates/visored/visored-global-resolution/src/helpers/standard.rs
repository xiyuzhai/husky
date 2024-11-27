use latex_command::path::menu::{LxCommandPathMenu, LX_COMMAND_PATH_MENU};
use latex_environment::path::menu::{LxEnvironmentPathMenu, LX_ENVIRONMENT_PATH_MENU};
use latex_math_letter::letter::LxMathLetter;
use latex_math_punctuation::{LxMathPunctuation, LxMathPunctuationMap};
use visored_entity_path::path::VdItemPath;

use crate::{
    default_table::VdDefaultGlobalResolutionTable,
    resolution::{
        command::{VdCompleteCommandGlobalResolution, VdCompleteCommandGlobalResolutionMap},
        environment::{VdEnvironmentGlobalResolution, VdEnvironmentGlobalResolutionMap},
        letter::{VdLetterGlobalResolution, VdLetterGlobalResolutionMap},
        punctuation::VdPunctuationGlobalResolution,
    },
};

impl VdDefaultGlobalResolutionTable {
    pub fn new_standard() -> Self {
        let punctuation_resolution_map =
            LxMathPunctuationMap::new(lx_math_punctuation_standard_resolution);
        let command_resolution_map = standard_command_resolution_map();
        let environment_resolution_map = standard_environment_resolution_map();
        let letter_resolution_map = standard_letter_resolution_map();
        Self::new(
            punctuation_resolution_map,
            command_resolution_map,
            environment_resolution_map,
            letter_resolution_map,
        )
    }
}

fn standard_command_resolution_map() -> std::collections::HashMap<
    latex_command::path::LxCommandPath,
    crate::resolution::command::VdCompleteCommandGlobalResolution,
    rustc_hash::FxBuildHasher,
> {
    let LxCommandPathMenu {
        begin: _,
        end: _,
        usepackage,
        documentclass,
        newtheorem,
        part,
        chapter,
        section,
        subsection,
        subsubsection,
        // maths
        // - letter style
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
        times,
        otimes,
        prod,
        // - extended letters
        alpha,
        beta,
        gamma,
        pi,
        // - functions
        sin,
        cos,
        // - layouts
        sqrt,
        frac,
        // - environments
        text,
    } = *LX_COMMAND_PATH_MENU;
    VdCompleteCommandGlobalResolutionMap::from_iter([
        // - root
        (usepackage, VdCompleteCommandGlobalResolution::USEPACKAGE),
        (
            documentclass,
            VdCompleteCommandGlobalResolution::DOCUMENTCLASS,
        ),
        (part, VdCompleteCommandGlobalResolution::PART),
        (chapter, VdCompleteCommandGlobalResolution::CHAPTER),
        (section, VdCompleteCommandGlobalResolution::SECTION),
        (subsection, VdCompleteCommandGlobalResolution::SUBSECTION),
        (
            subsubsection,
            VdCompleteCommandGlobalResolution::SUBSUBSECTION,
        ),
        // - operators
        // -- relations
        (eq, VdCompleteCommandGlobalResolution::EQ),
        (ne, VdCompleteCommandGlobalResolution::NE),
        (le, VdCompleteCommandGlobalResolution::LE),
        (ge, VdCompleteCommandGlobalResolution::GE),
        (r#in, VdCompleteCommandGlobalResolution::IN),
        (subset, VdCompleteCommandGlobalResolution::SUBSET),
        (supset, VdCompleteCommandGlobalResolution::SUPSET),
        (subseteq, VdCompleteCommandGlobalResolution::SUBSETEQ),
        (supseteq, VdCompleteCommandGlobalResolution::SUPSETEQ),
        (subseteqq, VdCompleteCommandGlobalResolution::SUBSETEQQ),
        (supseteqq, VdCompleteCommandGlobalResolution::SUPSETEQQ),
        (subsetneq, VdCompleteCommandGlobalResolution::SUBSETNEQ),
        (supsetneq, VdCompleteCommandGlobalResolution::SUPSETNEQ),
        // -- arithmetic
        (int, VdCompleteCommandGlobalResolution::INT),
        (sum, VdCompleteCommandGlobalResolution::SUM),
        (prod, VdCompleteCommandGlobalResolution::PROD),
        // - extended letters
        (alpha, VdCompleteCommandGlobalResolution::LOWER_ALPHA),
        (beta, VdCompleteCommandGlobalResolution::LOWER_BETA),
        (gamma, VdCompleteCommandGlobalResolution::LOWER_GAMMA),
        (pi, VdCompleteCommandGlobalResolution::LOWER_PI),
        (
            sin,
            VdCompleteCommandGlobalResolution::Item(VdItemPath::SIN),
        ),
        (
            cos,
            VdCompleteCommandGlobalResolution::Item(VdItemPath::COS),
        ),
        (sqrt, VdCompleteCommandGlobalResolution::Sqrt),
        (frac, VdCompleteCommandGlobalResolution::Frac),
        (text, VdCompleteCommandGlobalResolution::Text),
    ])
}

fn standard_environment_resolution_map() -> VdEnvironmentGlobalResolutionMap {
    let LxEnvironmentPathMenu {
        document,
        example,
        proof,
        remark,
        definition,
        theorem,
        lemma,
        corollary,
        proposition,
        align,
        array,
        matrix,
        cases,
        equation,
        figure,
        table,
    } = *LX_ENVIRONMENT_PATH_MENU;
    [
        (document, VdEnvironmentGlobalResolution::DOCUMENT),
        (example, VdEnvironmentGlobalResolution::EXAMPLE),
        (equation, VdEnvironmentGlobalResolution::EQUATION),
    ]
    .into_iter()
    .collect()
}

fn lx_math_punctuation_standard_resolution(
    punctuation: LxMathPunctuation,
) -> Option<VdPunctuationGlobalResolution> {
    match punctuation {
        LxMathPunctuation::Add => Some(VdPunctuationGlobalResolution::ADD),
        LxMathPunctuation::Sub => Some(VdPunctuationGlobalResolution::SUB),
        LxMathPunctuation::Mul => Some(VdPunctuationGlobalResolution::SEPARATOR_MUL),
        LxMathPunctuation::Div => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::In => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::NotIn => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Subset => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Superset => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::SubsetEq => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::SupersetEq => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::ForAll => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Exists => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::NotExists => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Infinity => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Equals => Some(VdPunctuationGlobalResolution::EQ),
        LxMathPunctuation::NotEquals => Some(VdPunctuationGlobalResolution::NE),
        LxMathPunctuation::LessThan => Some(VdPunctuationGlobalResolution::LT),
        LxMathPunctuation::GreaterThan => Some(VdPunctuationGlobalResolution::GT),
        LxMathPunctuation::LessEq => Some(VdPunctuationGlobalResolution::LE),
        LxMathPunctuation::GreaterEq => Some(VdPunctuationGlobalResolution::GE),
        LxMathPunctuation::PlusMinus => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Times => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Lpar => Some(VdPunctuationGlobalResolution::LPAR),
        LxMathPunctuation::Rpar => Some(VdPunctuationGlobalResolution::RPAR),
        LxMathPunctuation::Lbox => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Rbox => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::EscapedLcurl => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::EscapedRcurl => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Ldot => Some(VdPunctuationGlobalResolution::Todo),
    }
}

fn standard_letter_resolution_map() -> VdLetterGlobalResolutionMap {
    [
        (
            LxMathLetter::MATHBB_N,
            VdLetterGlobalResolution::NATURAL_NUMBER,
        ),
        (LxMathLetter::MATHBB_Z, VdLetterGlobalResolution::INTEGER),
        (
            LxMathLetter::MATHBB_Q,
            VdLetterGlobalResolution::RATIONAL_NUMBER,
        ),
        (
            LxMathLetter::MATHBB_R,
            VdLetterGlobalResolution::REAL_NUMBER,
        ),
        (
            LxMathLetter::MATHBB_C,
            VdLetterGlobalResolution::COMPLEX_NUMBER,
        ),
    ]
    .into_iter()
    .collect()
}

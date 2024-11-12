use latex_command::path::menu::{command_path_menu, LxCommandPathMenu};
use latex_math_letter::letter::LxMathLetter;
use latex_math_punctuation::{LxMathPunctuation, LxMathPunctuationMap};
use visored_item_path::path::VdItemPath;

use crate::{
    resolution::{
        command::{VdCompleteCommandGlobalResolution, VdCompleteCommandGlobalResolutionMap},
        letter::{VdLetterGlobalResolution, VdLetterGlobalResolutionMap},
        punctuation::VdPunctuationGlobalResolution,
    },
    table::VdDefaultGlobalResolutionTable,
};

impl VdDefaultGlobalResolutionTable {
    pub fn new_standard(db: &salsa::Db) -> Self {
        let punctuation_resolution_map =
            LxMathPunctuationMap::new(lx_math_punctuation_standard_resolution);
        let command_resolution_map = standard_command_resolution_map(db);
        let letter_resolution_map = standard_letter_resolution_map(db);
        Self::new(
            punctuation_resolution_map,
            command_resolution_map,
            letter_resolution_map,
        )
    }
}

fn standard_command_resolution_map(
    db: &salsa::Db,
) -> std::collections::HashMap<
    latex_command::path::LxCommandPath,
    crate::resolution::command::VdCompleteCommandGlobalResolution,
    rustc_hash::FxBuildHasher,
> {
    let LxCommandPathMenu {
        begin: _,
        end: _,
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
    } = *command_path_menu(db);
    VdCompleteCommandGlobalResolutionMap::from_iter([
        // - operators
        // -- relations
        (eq, VdCompleteCommandGlobalResolution::EQ),
        (ne, VdCompleteCommandGlobalResolution::NE),
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
        (times, VdCompleteCommandGlobalResolution::TIMES),
        (otimes, VdCompleteCommandGlobalResolution::OTIMES),
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

fn lx_math_punctuation_standard_resolution(
    punctuation: LxMathPunctuation,
) -> Option<VdPunctuationGlobalResolution> {
    match punctuation {
        LxMathPunctuation::Add => Some(VdPunctuationGlobalResolution::SEPARATOR_ADD),
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
        LxMathPunctuation::NotEquals => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::LessThan => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::GreaterThan => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::LessEq => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::GreaterEq => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::PlusMinus => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Times => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Lpar => Some(VdPunctuationGlobalResolution::LPAR),
        LxMathPunctuation::Rpar => Some(VdPunctuationGlobalResolution::RPAR),
        LxMathPunctuation::Lbox => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::Rbox => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::EscapedLcurl => Some(VdPunctuationGlobalResolution::Todo),
        LxMathPunctuation::EscapedRcurl => Some(VdPunctuationGlobalResolution::Todo),
    }
}

fn standard_letter_resolution_map(db: &salsa::Db) -> VdLetterGlobalResolutionMap {
    [
        (
            LxMathLetter::MATHBB_N,
            VdLetterGlobalResolution::NATURAL_NUMBER,
        ),
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

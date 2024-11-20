use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxMathLetterStyle {
    Mathbb,
    Mathcal,
    Mathfrak,
    Mathit,
    Mathrm,
    Mathscr,
    Mathsf,
}

impl LxMathLetterStyle {
    pub const MATHBB: Self = Self::Mathbb;
    pub const MATHFRAK: Self = Self::Mathfrak;
    pub const MATHCAL: Self = Self::Mathcal;
    pub const MATHIT: Self = Self::Mathit;
    pub const MATHRM: Self = Self::Mathrm;
    pub const MATHSCR: Self = Self::Mathscr;
    pub const MATHSF: Self = Self::Mathsf;
}

impl LxMathLetterStyle {
    pub fn latex_code(self) -> String {
        match self {
            Self::Mathbb => "\\mathbb".to_string(),
            Self::Mathcal => "\\mathcal".to_string(),
            Self::Mathfrak => "\\mathfrak".to_string(),
            Self::Mathit => "\\mathit".to_string(),
            Self::Mathrm => "\\mathrm".to_string(),
            Self::Mathscr => "\\mathscr".to_string(),
            Self::Mathsf => "\\mathsf".to_string(),
        }
    }
}

impl LxMathLetterStyle {
    pub fn apply(self, letter: LxMathLetter) -> LxMathLetterResult<LxMathLetter> {
        match letter {
            LxMathLetter::UpperLatin(l) => Ok(LxMathLetter::StyledUpperLatin(self, l)),
            LxMathLetter::LowerLatin(l) => Ok(LxMathLetter::StyledLowerLatin(self, l)),
            LxMathLetter::StyledUpperLatin(_, _) => todo!(),
            LxMathLetter::StyledLowerLatin(_, _) => todo!(),
            LxMathLetter::DistinctUpperGreek(_) => todo!(),
            LxMathLetter::DistinctLowerGreek(_) => todo!(),
        }
    }
}

impl LxMathLetter {
    pub const MATHBB_N: Self =
        Self::StyledUpperLatin(LxMathLetterStyle::Mathbb, LxMathLatinLetter::N);
    pub const MATHBB_Q: Self =
        Self::StyledUpperLatin(LxMathLetterStyle::Mathbb, LxMathLatinLetter::Q);
    pub const MATHBB_R: Self =
        Self::StyledUpperLatin(LxMathLetterStyle::Mathbb, LxMathLatinLetter::R);
    pub const MATHBB_C: Self =
        Self::StyledUpperLatin(LxMathLetterStyle::Mathbb, LxMathLatinLetter::C);
    pub const MATHBB_Z: Self =
        Self::StyledUpperLatin(LxMathLetterStyle::Mathbb, LxMathLatinLetter::Z);
}

pub mod greek;
pub mod latin;
pub mod styled;

use self::greek::*;
use self::latin::*;
use self::styled::*;
use crate::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxMathLetter {
    UpperLatin(LxMathLatinLetter),
    LowerLatin(LxMathLatinLetter),
    StyledUpperLatin(LxMathLetterStyle, LxMathLatinLetter),
    StyledLowerLatin(LxMathLetterStyle, LxMathLatinLetter),
    DistinctUpperGreek(LxMathDistinctUpperGreekLetter),
    DistinctLowerGreek(LxMathDistinctLowerGreekLetter),
}

impl std::fmt::Display for LxMathLetter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.latex_code())
    }
}

impl LxMathLetter {
    pub fn latex_code(self) -> String {
        match self {
            LxMathLetter::UpperLatin(l) => l.upper_case_latex_code().to_string(),
            LxMathLetter::LowerLatin(l) => l.lower_case_latex_code().to_string(),
            LxMathLetter::StyledUpperLatin(style, l) => {
                format!("{}{{{}}}", style.latex_code(), l.upper_case_latex_code())
            }
            LxMathLetter::StyledLowerLatin(style, l) => {
                format!("{}{{{}}}", style.latex_code(), l.lower_case_latex_code())
            }
            LxMathLetter::DistinctUpperGreek(l) => l.latex_code().to_string(),
            LxMathLetter::DistinctLowerGreek(l) => l.latex_code().to_string(),
        }
    }

    pub fn try_from_char(c: char) -> Option<Self> {
        Some(match c {
            'A' => LxMathLetter::UPPER_A,
            'B' => LxMathLetter::UPPER_B,
            'C' => LxMathLetter::UPPER_C,
            'D' => LxMathLetter::UPPER_D,
            'E' => LxMathLetter::UPPER_E,
            'F' => LxMathLetter::UPPER_F,
            'G' => LxMathLetter::UPPER_G,
            'H' => LxMathLetter::UPPER_H,
            'I' => LxMathLetter::UPPER_I,
            'J' => LxMathLetter::UPPER_J,
            'K' => LxMathLetter::UPPER_K,
            'L' => LxMathLetter::UPPER_L,
            'M' => LxMathLetter::UPPER_M,
            'N' => LxMathLetter::UPPER_N,
            'O' => LxMathLetter::UPPER_O,
            'P' => LxMathLetter::UPPER_P,
            'Q' => LxMathLetter::UPPER_Q,
            'R' => LxMathLetter::UPPER_R,
            'S' => LxMathLetter::UPPER_S,
            'T' => LxMathLetter::UPPER_T,
            'U' => LxMathLetter::UPPER_U,
            'V' => LxMathLetter::UPPER_V,
            'W' => LxMathLetter::UPPER_W,
            'X' => LxMathLetter::UPPER_X,
            'Y' => LxMathLetter::UPPER_Y,
            'Z' => LxMathLetter::UPPER_Z,
            'a' => LxMathLetter::LOWER_A,
            'b' => LxMathLetter::LOWER_B,
            'c' => LxMathLetter::LOWER_C,
            'd' => LxMathLetter::LOWER_D,
            'e' => LxMathLetter::LOWER_E,
            'f' => LxMathLetter::LOWER_F,
            'g' => LxMathLetter::LOWER_G,
            'h' => LxMathLetter::LOWER_H,
            'i' => LxMathLetter::LOWER_I,
            'j' => LxMathLetter::LOWER_J,
            'k' => LxMathLetter::LOWER_K,
            'l' => LxMathLetter::LOWER_L,
            'm' => LxMathLetter::LOWER_M,
            'n' => LxMathLetter::LOWER_N,
            'o' => LxMathLetter::LOWER_O,
            'p' => LxMathLetter::LOWER_P,
            'q' => LxMathLetter::LOWER_Q,
            'r' => LxMathLetter::LOWER_R,
            's' => LxMathLetter::LOWER_S,
            't' => LxMathLetter::LOWER_T,
            'u' => LxMathLetter::LOWER_U,
            'v' => LxMathLetter::LOWER_V,
            'w' => LxMathLetter::LOWER_W,
            'x' => LxMathLetter::LOWER_X,
            'y' => LxMathLetter::LOWER_Y,
            'z' => LxMathLetter::LOWER_Z,
            'Γ' => LxMathLetter::UPPER_GAMMA,
            'Δ' => LxMathLetter::UPPER_DELTA,
            'Θ' => LxMathLetter::UPPER_THETA,
            'Λ' => LxMathLetter::UPPER_LAMBDA,
            'Ξ' => LxMathLetter::UPPER_XI,
            'Π' => LxMathLetter::UPPER_PI,
            'Σ' => LxMathLetter::UPPER_SIGMA,
            'Φ' => LxMathLetter::UPPER_PHI,
            'Ψ' => LxMathLetter::UPPER_PSI,
            'Ω' => LxMathLetter::UPPER_OMEGA,
            'α' => LxMathLetter::LOWER_ALPHA,
            'β' => LxMathLetter::LOWER_BETA,
            'γ' => LxMathLetter::LOWER_GAMMA,
            'δ' => LxMathLetter::LOWER_DELTA,
            'ε' => LxMathLetter::LOWER_EPSILON,
            'ζ' => LxMathLetter::LOWER_ZETA,
            'η' => LxMathLetter::LOWER_ETA,
            'θ' => LxMathLetter::LOWER_THETA,
            'ι' => LxMathLetter::LOWER_IOTA,
            'κ' => LxMathLetter::LOWER_KAPPA,
            'λ' => LxMathLetter::LOWER_LAMBDA,
            'μ' => LxMathLetter::LOWER_MU,
            'ν' => LxMathLetter::LOWER_NU,
            'ξ' => LxMathLetter::LOWER_XI,
            'ο' => LxMathLetter::LOWER_OMICRON,
            'π' => LxMathLetter::LOWER_PI,
            'ρ' => LxMathLetter::LOWER_RHO,
            'σ' => LxMathLetter::LOWER_SIGMA,
            'τ' => LxMathLetter::LOWER_TAU,
            'υ' => LxMathLetter::LOWER_UPSILON,
            'φ' => LxMathLetter::LOWER_PHI,
            'χ' => LxMathLetter::LOWER_CHI,
            'ψ' => LxMathLetter::LOWER_PSI,
            'ω' => LxMathLetter::LOWER_OMEGA,
            _ => return None,
        })
    }
}

use super::*;

/// only those visually different from the latin letters are listed here
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxMathDistinctUpperGreekLetter {
    Gamma,
    Delta,
    Theta,
    Lambda,
    Xi,
    Pi,
    Sigma,
    Phi,
    Psi,
    Omega,
}

impl LxMathDistinctUpperGreekLetter {
    pub fn latex_code(self) -> String {
        match self {
            Self::Gamma => "\\Gamma".to_string(),
            Self::Delta => "\\Delta".to_string(),
            Self::Theta => "\\Theta".to_string(),
            Self::Lambda => "\\Lambda".to_string(),
            Self::Xi => "\\Xi".to_string(),
            Self::Pi => "\\Pi".to_string(),
            Self::Sigma => "\\Sigma".to_string(),
            Self::Phi => "\\Phi".to_string(),
            Self::Psi => "\\Psi".to_string(),
            Self::Omega => "\\Omega".to_string(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxMathDistinctLowerGreekLetter {
    Alpha,
    Beta,
    Gamma,
    Delta,
    Epsilon,
    Zeta,
    Eta,
    Theta,
    Iota,
    Kappa,
    Lambda,
    Mu,
    Nu,
    Xi,
    Omicron,
    Pi,
    Rho,
    Sigma,
    Tau,
    Upsilon,
    Phi,
    Chi,
    Psi,
    Omega,
}

impl LxMathDistinctLowerGreekLetter {
    pub fn latex_code(self) -> &'static str {
        match self {
            LxMathDistinctLowerGreekLetter::Alpha => "\\alpha",
            LxMathDistinctLowerGreekLetter::Beta => "\\beta",
            LxMathDistinctLowerGreekLetter::Gamma => "\\gamma",
            LxMathDistinctLowerGreekLetter::Delta => "\\delta",
            LxMathDistinctLowerGreekLetter::Epsilon => "\\epsilon",
            LxMathDistinctLowerGreekLetter::Zeta => "\\zeta",
            LxMathDistinctLowerGreekLetter::Eta => "\\eta",
            LxMathDistinctLowerGreekLetter::Theta => "\\theta",
            LxMathDistinctLowerGreekLetter::Iota => "\\iota",
            LxMathDistinctLowerGreekLetter::Kappa => "\\kappa",
            LxMathDistinctLowerGreekLetter::Lambda => "\\lambda",
            LxMathDistinctLowerGreekLetter::Mu => "\\mu",
            LxMathDistinctLowerGreekLetter::Nu => "\\nu",
            LxMathDistinctLowerGreekLetter::Xi => "\\xi",
            LxMathDistinctLowerGreekLetter::Omicron => "\\omicron",
            LxMathDistinctLowerGreekLetter::Pi => "\\pi",
            LxMathDistinctLowerGreekLetter::Rho => "\\rho",
            LxMathDistinctLowerGreekLetter::Sigma => "\\sigma",
            LxMathDistinctLowerGreekLetter::Tau => "\\tau",
            LxMathDistinctLowerGreekLetter::Upsilon => "\\upsilon",
            LxMathDistinctLowerGreekLetter::Phi => "\\phi",
            LxMathDistinctLowerGreekLetter::Chi => "\\chi",
            LxMathDistinctLowerGreekLetter::Psi => "\\psi",
            LxMathDistinctLowerGreekLetter::Omega => "\\omega",
        }
    }
}

impl LxMathLetter {
    pub const UPPER_GAMMA: Self =
        LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Gamma);
    pub const UPPER_DELTA: Self =
        LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Delta);
    pub const UPPER_THETA: Self =
        LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Theta);
    pub const UPPER_LAMBDA: Self =
        LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Lambda);
    pub const UPPER_XI: Self = LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Xi);
    pub const UPPER_PI: Self = LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Pi);
    pub const UPPER_SIGMA: Self =
        LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Sigma);
    pub const UPPER_PHI: Self =
        LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Phi);
    pub const UPPER_PSI: Self =
        LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Psi);
    pub const UPPER_OMEGA: Self =
        LxMathLetter::DistinctUpperGreek(LxMathDistinctUpperGreekLetter::Omega);

    pub const LOWER_ALPHA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Alpha);
    pub const LOWER_BETA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Beta);
    pub const LOWER_GAMMA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Gamma);
    pub const LOWER_DELTA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Delta);
    pub const LOWER_EPSILON: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Epsilon);
    pub const LOWER_ZETA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Zeta);
    pub const LOWER_ETA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Eta);
    pub const LOWER_THETA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Theta);
    pub const LOWER_IOTA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Iota);
    pub const LOWER_KAPPA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Kappa);
    pub const LOWER_LAMBDA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Lambda);
    pub const LOWER_MU: Self = LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Mu);
    pub const LOWER_NU: Self = LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Nu);
    pub const LOWER_XI: Self = LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Xi);
    pub const LOWER_OMICRON: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Omicron);
    pub const LOWER_PI: Self = LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Pi);
    pub const LOWER_RHO: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Rho);
    pub const LOWER_SIGMA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Sigma);
    pub const LOWER_TAU: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Tau);
    pub const LOWER_UPSILON: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Upsilon);
    pub const LOWER_PHI: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Phi);
    pub const LOWER_CHI: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Chi);
    pub const LOWER_PSI: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Psi);
    pub const LOWER_OMEGA: Self =
        LxMathLetter::DistinctLowerGreek(LxMathDistinctLowerGreekLetter::Omega);
}

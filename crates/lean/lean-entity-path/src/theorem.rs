use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum LnTheoremPath {
    SquareNonnegative,
    TermDerivation(LnTermDerivationTheoremPath),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord, Hash)]
pub enum LnTermDerivationTheoremPath {
    Reflection,
    NumComparison,
    SubEqsAddNeg,
    LiteralAddLiteral,
    AddEq,
    AdditionInterchange,
    AdditionAssociativity,
    AdditionIdentity,
    AdditionInverse,
    AdditionDistributivity,
    NegEqsMinusOneMul,
    AtomAddSwap,
    LiteralMul,
    MulEq,
    AtomMulSwap,
    OneMulNormalized,
    NonOneLiteralMulAtom,
    NonZeroLiteralAddAtom,
    NfAddZero,
    NonTrivialFinish,
    AtomMulAtomLess,
    AtomMulAtomEqual,
    AtomMulAtomGreater,
    Sqrt,
}

impl LnTheoremPath {
    pub const SQUARE_NONNEGATIVE: Self = Self::SquareNonnegative;
}

impl LnTheoremPath {
    pub fn code(&self) -> &str {
        match self {
            LnTheoremPath::SquareNonnegative => "sq_nonneg",
            LnTheoremPath::TermDerivation(path) => path.code(),
        }
    }

    pub fn show(&self, db: &EternerDb) -> String {
        match self {
            Self::SquareNonnegative => "sq_nonneg".to_string(),
            Self::TermDerivation(path) => path.show(db),
        }
    }
}

impl LnTermDerivationTheoremPath {
    pub fn code(&self) -> &str {
        match self {
            LnTermDerivationTheoremPath::Reflection => "term_derivation_reflection",
            LnTermDerivationTheoremPath::NumComparison => "term_derivation_num_comparison",
            LnTermDerivationTheoremPath::SubEqsAddNeg => "term_derivation_sub_eqs_add_neg",
            LnTermDerivationTheoremPath::LiteralAddLiteral => "term_derivation_literal_add_literal",
            LnTermDerivationTheoremPath::AddEq => "term_derivation_add_eq",
            LnTermDerivationTheoremPath::AdditionInterchange => {
                "term_derivation_addition_interchange"
            }
            LnTermDerivationTheoremPath::AdditionAssociativity => {
                "term_derivation_addition_associativity"
            }
            LnTermDerivationTheoremPath::AdditionIdentity => "term_derivation_addition_identity",
            LnTermDerivationTheoremPath::AdditionInverse => "term_derivation_addition_inverse",
            LnTermDerivationTheoremPath::AdditionDistributivity => {
                "term_derivation_addition_distributivity"
            }
            LnTermDerivationTheoremPath::NegEqsMinusOneMul => {
                "term_derivation_neg_eqs_minus_one_mul"
            }
            LnTermDerivationTheoremPath::AtomAddSwap => "term_derivation_atom_add_swap",
            LnTermDerivationTheoremPath::LiteralMul => "term_derivation_literal_mul",
            LnTermDerivationTheoremPath::MulEq => "term_derivation_mul_eq",
            LnTermDerivationTheoremPath::AtomMulSwap => "term_derivation_atom_mul_swap",
            LnTermDerivationTheoremPath::OneMulNormalized => "term_derivation_one_mul_atom",
            LnTermDerivationTheoremPath::NonOneLiteralMulAtom => {
                "term_derivation_non_one_literal_mul_atom"
            }
            LnTermDerivationTheoremPath::NonZeroLiteralAddAtom => {
                "term_derivation_non_zero_literal_add_atom"
            }
            LnTermDerivationTheoremPath::NfAddZero => "term_derivation_nf_add_zero",
            LnTermDerivationTheoremPath::NonTrivialFinish => "term_derivation_non_trivial_finish",
            LnTermDerivationTheoremPath::AtomMulAtomLess => "term_derivation_atom_mul_atom_less",
            LnTermDerivationTheoremPath::AtomMulAtomEqual => "term_derivation_atom_mul_atom_equal",
            LnTermDerivationTheoremPath::AtomMulAtomGreater => {
                "term_derivation_atom_mul_atom_greater"
            }
            LnTermDerivationTheoremPath::Sqrt => "term_derivation_sqrt",
        }
    }

    pub fn show(&self, db: &EternerDb) -> String {
        match self {
            LnTermDerivationTheoremPath::Reflection => "term_derivation_reflection".to_string(),
            LnTermDerivationTheoremPath::NumComparison => {
                "term_derivation_num_comparison".to_string()
            }
            LnTermDerivationTheoremPath::SubEqsAddNeg => {
                "term_derivation_sub_eqs_add_neg".to_string()
            }
            LnTermDerivationTheoremPath::LiteralAddLiteral => {
                "term_derivation_literal_add_literal".to_string()
            }
            LnTermDerivationTheoremPath::AddEq => "term_derivation_add_eq".to_string(),
            LnTermDerivationTheoremPath::AdditionInterchange => {
                "term_derivation_addition_interchange".to_string()
            }
            LnTermDerivationTheoremPath::AdditionAssociativity => {
                "term_derivation_addition_associativity".to_string()
            }
            LnTermDerivationTheoremPath::AdditionIdentity => {
                "term_derivation_addition_identity".to_string()
            }
            LnTermDerivationTheoremPath::AdditionInverse => {
                "term_derivation_addition_inverse".to_string()
            }
            LnTermDerivationTheoremPath::AdditionDistributivity => {
                "term_derivation_addition_distributivity".to_string()
            }
            LnTermDerivationTheoremPath::NegEqsMinusOneMul => {
                "term_derivation_neg_eqs_minus_one_mul".to_string()
            }
            LnTermDerivationTheoremPath::AtomAddSwap => "term_derivation_atom_add_swap".to_string(),
            LnTermDerivationTheoremPath::LiteralMul => "term_derivation_literal_mul".to_string(),
            LnTermDerivationTheoremPath::MulEq => "term_derivation_mul_eq".to_string(),
            LnTermDerivationTheoremPath::AtomMulSwap => "term_derivation_atom_mul_swap".to_string(),
            LnTermDerivationTheoremPath::OneMulNormalized => {
                "term_derivation_one_mul_atom".to_string()
            }
            LnTermDerivationTheoremPath::NonOneLiteralMulAtom => {
                "term_derivation_non_one_literal_mul_atom".to_string()
            }
            LnTermDerivationTheoremPath::NonZeroLiteralAddAtom => {
                "term_derivation_non_zero_literal_add_atom".to_string()
            }
            LnTermDerivationTheoremPath::NfAddZero => "term_derivation_nf_add_zero".to_string(),
            LnTermDerivationTheoremPath::NonTrivialFinish => {
                "term_derivation_non_trivial_finish".to_string()
            }
            LnTermDerivationTheoremPath::AtomMulAtomLess => {
                "term_derivation_atom_mul_atom_less".to_string()
            }
            LnTermDerivationTheoremPath::AtomMulAtomEqual => {
                "term_derivation_atom_mul_atom_equal".to_string()
            }
            LnTermDerivationTheoremPath::AtomMulAtomGreater => {
                "term_derivation_atom_mul_atom_greater".to_string()
            }
            LnTermDerivationTheoremPath::Sqrt => "term_derivation_sqrt".to_string(),
        }
    }
}

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
    NegLiteral,
    NegEq,
    NegAtom,
    NegSum,
    NegProduct,
    NegExponential,
    AtomAddSwap,
    LiteralMul,
    MulEq,
    AtomMulSwap,
    OneMul,
    NonOneLiteralMulAtom,
    NfAddZero,
    NonTrivialFinish,
    AtomMulAtomLess,
    AtomMulAtomEqual,
    AtomMulAtomGreater,
    Sqrt,
    AddAtom,
    MulProduct,
    NonReducedPower,
    PowerOne,
    AtomAddProduct,
    ZeroAdd,
    SumAddProductEqualKeep,
    SumAddProductEqualCancel,
    SumAddProductGreater,
    ProductAddProductLess,
    ProductAddProductEqualKeep,
    ProductAddProductEqualCancel,
    ProductAddProductGreater,
    SimpleProductMulExponentialLess,
    SimpleProductMulExponentialGreater,
    AddSum,
    DivEq,
    DivLiteral,
    LiteralMulSum,
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
            LnTermDerivationTheoremPath::NegLiteral => "term_derivation_neg_literal",
            LnTermDerivationTheoremPath::NegEq => "term_derivation_neg_eq",
            LnTermDerivationTheoremPath::NegAtom => "term_derivation_neg_atom",
            LnTermDerivationTheoremPath::NegSum => "term_derivation_neg_sum",
            LnTermDerivationTheoremPath::NegProduct => "term_derivation_neg_product",
            LnTermDerivationTheoremPath::NegExponential => "term_derivation_neg_exponential",
            LnTermDerivationTheoremPath::AtomAddSwap => "term_derivation_atom_add_swap",
            LnTermDerivationTheoremPath::LiteralMul => "term_derivation_literal_mul",
            LnTermDerivationTheoremPath::MulEq => "term_derivation_mul_eq",
            LnTermDerivationTheoremPath::AtomMulSwap => "term_derivation_atom_mul_swap",
            LnTermDerivationTheoremPath::OneMul => "term_derivation_one_mul",
            LnTermDerivationTheoremPath::NonOneLiteralMulAtom => {
                "term_derivation_non_one_literal_mul_atom"
            }
            LnTermDerivationTheoremPath::NfAddZero => "term_derivation_nf_add_zero",
            LnTermDerivationTheoremPath::NonTrivialFinish => "term_derivation_non_trivial_finish",
            LnTermDerivationTheoremPath::AtomMulAtomLess => "term_derivation_atom_mul_atom_less",
            LnTermDerivationTheoremPath::AtomMulAtomEqual => "term_derivation_atom_mul_atom_equal",
            LnTermDerivationTheoremPath::AtomMulAtomGreater => {
                "term_derivation_atom_mul_atom_greater"
            }
            LnTermDerivationTheoremPath::Sqrt => "term_derivation_sqrt",
            LnTermDerivationTheoremPath::AddAtom => "term_derivation_add_atom",
            LnTermDerivationTheoremPath::MulProduct => "term_derivation_mul_product",
            LnTermDerivationTheoremPath::NonReducedPower => "term_derivation_non_reduced_power",
            LnTermDerivationTheoremPath::PowerOne => "term_derivation_power_one",
            LnTermDerivationTheoremPath::AtomAddProduct => "term_derivation_atom_add_product",
            LnTermDerivationTheoremPath::ZeroAdd => "term_derivation_zero_add",
            LnTermDerivationTheoremPath::SumAddProductEqualKeep => {
                "term_derivation_sum_add_product_equal_keep"
            }
            LnTermDerivationTheoremPath::SumAddProductEqualCancel => {
                "term_derivation_sum_add_product_equal_cancel"
            }
            LnTermDerivationTheoremPath::SumAddProductGreater => {
                "term_derivation_sum_add_product_greater"
            }
            LnTermDerivationTheoremPath::ProductAddProductLess => {
                "term_derivation_product_add_product_less"
            }
            LnTermDerivationTheoremPath::ProductAddProductEqualKeep => {
                "term_derivation_product_add_product_equal_keep"
            }
            LnTermDerivationTheoremPath::ProductAddProductEqualCancel => {
                "term_derivation_product_add_product_equal_cancel"
            }
            LnTermDerivationTheoremPath::ProductAddProductGreater => {
                "term_derivation_product_add_product_greater"
            }
            LnTermDerivationTheoremPath::SimpleProductMulExponentialLess => {
                "term_derivation_simple_product_mul_exponential_less"
            }
            LnTermDerivationTheoremPath::SimpleProductMulExponentialGreater => {
                "term_derivation_simple_product_mul_exponential_greater"
            }
            LnTermDerivationTheoremPath::AddSum => "term_derivation_add_sum",
            LnTermDerivationTheoremPath::DivEq => "term_derivation_div_eq",
            LnTermDerivationTheoremPath::DivLiteral => "term_derivation_div_literal",
            LnTermDerivationTheoremPath::LiteralMulSum => "term_derivation_literal_mul_sum",
        }
    }

    pub fn show(&self, db: &EternerDb) -> String {
        self.code().to_string()
    }
}

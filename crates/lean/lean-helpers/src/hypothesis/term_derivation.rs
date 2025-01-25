use super::*;
use enum_index::IsEnumIndex;
use lean_entity_path::theorem::LnTermDerivationTheoremPath;

lazy_static! {
    pub static ref TERM_DERIVATION_HEADER: String = gen_term_derivation_header();
}

fn gen_term_derivation_header() -> String {
    let mut header = String::new();
    for theorem in LnTermDerivationTheoremPath::all() {
        use std::fmt::Write;

        write!(
            header,
            r#"
-- {:?}{}"#,
            theorem,
            theorem.header()
        )
        .unwrap();
    }
    header
}

impl HasHeader for LnTermDerivationTheoremPath {
    fn header(&self) -> &'static str {
        match self {
            LnTermDerivationTheoremPath::Reflection => {
                r#"
theorem term_derivation_reflection {α} {a : α} : a = a := by rfl
"#
            }
            LnTermDerivationTheoremPath::NumComparison => {
                r#"
theorem term_derivation_num_comparison : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SubEqsAddNeg => {
                r#"
theorem term_derivation_sub_eqs_add_neg : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::LiteralAddLiteral => {
                r#"
theorem term_derivation_literal_add_literal : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AddEq => {
                r#"
theorem term_derivation_add_eq : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AdditionInterchange => {
                r#"
theorem term_derivation_addition_interchange : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AdditionAssociativity => {
                r#"
theorem term_derivation_addition_associativity : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AdditionIdentity => {
                r#"
theorem term_derivation_addition_identity : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AdditionInverse => {
                r#"
theorem term_derivation_addition_inverse : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AdditionDistributivity => {
                r#"
theorem term_derivation_addition_distributivity : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AtomAddProduct => {
                r#"
theorem term_derivation_atom_add_product : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SumAddProductEqualKeep => {
                r#"
theorem term_derivation_sum_add_product_equal_keep : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SumAddProductEqualCancel => {
                r#"
theorem term_derivation_sum_add_product_equal_cancel : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::MulEq => {
                r#"
theorem term_derivation_mul_eq : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AtomMulSwap => {
                r#"
theorem term_derivation_atom_mul_swap : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::OneMul => {
                r#"
theorem term_derivation_one_mul : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NonOneLiteralMulAtom => {
                r#"
theorem term_derivation_nonone_literal_mul_atom : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NfAddZero => {
                r#"
theorem term_derivation_nf_add_zero : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::Sqrt => {
                r#"
theorem term_derivation_sqrt : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::MulProduct => {
                r#"
theorem term_derivation_mul_product : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NonReducedPower => {
                r#"
theorem term_derivation_non_reduced_power : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::PowerOne => {
                r#"
theorem term_derivation_power_one : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NegLiteral => {
                r#"
theorem term_derivation_neg_literal { α } { a : α } [Neg α] : -a = -a := by rfl
"#
            }
            LnTermDerivationTheoremPath::NegEq => {
                r#"
theorem term_derivation_neg_eq : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NegAtom => {
                r#"
theorem term_derivation_neg_atom : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NegSum => {
                r#"
theorem term_derivation_neg_sum : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NegProduct => {
                r#"
theorem term_derivation_neg_product : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NegExponential => {
                r#"
theorem term_derivation_neg_exponential : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::ZeroAdd => {
                r#"
theorem term_derivation_zero_add : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AddAtom => {
                r#"
theorem term_derivation_add_atom : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::ProductAddProductLess => {
                r#"
theorem term_derivation_product_add_product_less : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::ProductAddProductEqualKeep => {
                r#"
theorem term_derivation_product_add_product_equal_keep : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::ProductAddProductEqualCancel => {
                r#"
theorem term_derivation_product_add_product_equal_cancel : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::ProductAddProductGreater => {
                r#"
theorem term_derivation_product_add_product_greater : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SimpleProductMulExponentialLess => {
                r#"
theorem term_derivation_simple_product_mul_exponential_less : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SimpleProductMulExponentialGreater => {
                r#"
theorem term_derivation_simple_product_mul_exponential_greater : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SimpleProductMulBaseLess => {
                r#"
theorem term_derivation_simple_product_mul_base_less : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SimpleProductMulBaseGreater => {
                r#"
theorem term_derivation_simple_product_mul_base_greater : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AddSum => {
                r#"
theorem term_derivation_add_sum : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::DivEq => {
                r#"
theorem term_derivation_div_eq : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::DivLiteral => {
                r#"
theorem term_derivation_div_literal : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::LiteralMulSum => {
                r#"
theorem term_derivation_literal_mul_sum : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SumAddLiteral => {
                r#"
theorem term_derivation_sum_add_literal : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::ProductAddLiteral => {
                r#"
theorem term_derivation_product_add_literal : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::DivAtom => {
                r#"
theorem term_derivation_div_atom : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AtomMulExponentialLess => {
                r#"
theorem term_derivation_atom_mul_exponential_less : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AtomMulExponentialGreater => {
                r#"
theorem term_derivation_atom_mul_exponential_greater : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AtomAddNonZeroLiteral => {
                // derive `a + c => c + 1 * a` if `a` is an atom and `c` is a nonzero literal
                r#"
theorem term_derivation_atom_add_non_zero_literal { α } { a : α } { c : α } [CommRing α] : a + c = c + 1 * a := by ring
"#
            }
            LnTermDerivationTheoremPath::LiteralMul => {
                r#"
theorem term_derivation_literal_mul : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::NonTrivialFinish => {
                r#"
theorem term_derivation_non_trivial_finish : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AtomMulAtomLess => {
                r#"
theorem term_derivation_atom_mul_atom_less : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AtomMulAtomEqual => {
                r#"
theorem term_derivation_atom_mul_atom_equal : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::AtomMulAtomGreater => {
                r#"
theorem term_derivation_atom_mul_atom_greater : true := by sorry
"#
            }
            LnTermDerivationTheoremPath::SumAddProductGreater => {
                r#"
theorem term_derivation_sum_add_product_greater : true := by sorry
"#
            }
        }
    }
}

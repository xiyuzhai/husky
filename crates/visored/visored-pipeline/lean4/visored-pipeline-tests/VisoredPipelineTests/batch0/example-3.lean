import Mathlib
syntax "attack" : tactic

macro_rules
| `(tactic| attack) => `(tactic|
  first
  | simp; done
  | ring; done
  | ring_nf; rw [Real.sq_sqrt]; ring; all_goals attack; done
  | nlinarith; done
  | apply sq_nonneg; all_goals attack; done
  | apply div_nonneg; all_goals attack; done
  | field_simp; ring; done
  | linarith; done
)

macro "obvious": tactic =>`(tactic|
  first
  | attack; done
  | congr; all_goals attack; done
  | gcongr; all_goals attack; done
  | fail "Could not prove this goal automatically. It might not be as obvious as you think!"
)

macro "in_set" : term => `(true)


macro "term_trivial": tactic =>`(tactic|
  first
  | simp; done
  | ring; done
  | ring_nf; done
  | linarith; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "old_main_hypothesis": tactic =>`(tactic|
  first
  | assumption; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "let_assigned": tactic =>`(tactic|
  first
  | dsimp; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_equivalence": tactic =>`(tactic|
  first
  | simp; done
  | ring; done
  | ring_nf; done
  | linarith; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "comm_ring": tactic =>`(tactic|
  first
  | ring; done
  | ring_nf; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "litnum_reduce": tactic =>`(tactic|
  first
  | simp; done
  | simp [*]; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "litnum_bound": tactic =>`(tactic|
  first
  | linarith; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)


-- Reflection
theorem term_derivation_reflection {α} {a : α} : a = a := by rfl

-- NumComparison
theorem term_derivation_num_comparison : true := by sorry

-- SubEqsAddNeg
theorem term_derivation_sub_eqs_add_neg : true := by sorry

-- LiteralAddLiteral
theorem term_derivation_literal_add_literal : true := by sorry

-- AddEq
theorem term_derivation_add_eq : true := by sorry

-- AdditionInterchange
theorem term_derivation_addition_interchange : true := by sorry

-- AdditionAssociativity
theorem term_derivation_addition_associativity : true := by sorry

-- AdditionIdentity
theorem term_derivation_addition_identity : true := by sorry

-- AdditionInverse
theorem term_derivation_addition_inverse : true := by sorry

-- AdditionDistributivity
theorem term_derivation_addition_distributivity : true := by sorry

-- NegLiteral
theorem term_derivation_neg_literal { α } { a : α } [Neg α] : -a = -a := by rfl

-- NegEq
theorem term_derivation_neg_eq : true := by sorry

-- NegAtom
theorem term_derivation_neg_atom : true := by sorry

-- NegSum
theorem term_derivation_neg_sum : true := by sorry

-- NegProduct
theorem term_derivation_neg_product : true := by sorry

-- NegExponential
theorem term_derivation_neg_exponential : true := by sorry

-- AtomAddNonZeroLiteral
theorem term_derivation_atom_add_non_zero_literal {α} {a c : α} [CommRing α] : 
  a + c = c + 1 * a^1 := by ring

-- LiteralMul
theorem term_derivation_literal_mul : true := by sorry

-- MulEq
theorem term_derivation_mul_eq : true := by sorry

-- AtomMulSwap
theorem term_derivation_atom_mul_swap : true := by sorry

-- OneMul
theorem term_derivation_one_mul : true := by sorry

-- NonOneLiteralMulAtom
theorem term_derivation_nonone_literal_mul_atom : true := by sorry

-- NfAddZero
theorem term_derivation_nf_add_zero : true := by sorry

-- NonTrivialFinish
theorem term_derivation_non_trivial_finish : true := by sorry

-- AtomMulAtomLess
theorem term_derivation_atom_mul_atom_less : true := by sorry

-- AtomMulAtomEqual
theorem term_derivation_atom_mul_atom_equal : true := by sorry

-- AtomMulAtomGreater
theorem term_derivation_atom_mul_atom_greater : true := by sorry

-- Sqrt
theorem term_derivation_sqrt : true := by sorry

-- AddAtom
theorem term_derivation_add_atom : true := by sorry

-- MulProduct
theorem term_derivation_mul_product : true := by sorry

-- NonReducedPower
theorem term_derivation_non_reduced_power : true := by sorry

-- PowerOne
theorem term_derivation_power_one : true := by sorry

-- AtomAddProduct
theorem term_derivation_atom_add_product : true := by sorry

-- ZeroAdd
theorem term_derivation_zero_add : true := by sorry

-- SumAddProductEqualKeep
theorem term_derivation_sum_add_product_equal_keep : true := by sorry

-- SumAddProductEqualCancel
theorem term_derivation_sum_add_product_equal_cancel : true := by sorry

-- SumAddProductGreater
theorem term_derivation_sum_add_product_greater : true := by sorry

-- ProductAddProductLess
theorem term_derivation_product_add_product_less : true := by sorry

-- ProductAddProductEqualKeep
theorem term_derivation_product_add_product_equal_keep : true := by sorry

-- ProductAddProductEqualCancel
theorem term_derivation_product_add_product_equal_cancel : true := by sorry

-- ProductAddProductGreater
theorem term_derivation_product_add_product_greater : true := by sorry

-- SimpleProductMulExponentialLess
theorem term_derivation_simple_product_mul_exponential_less : true := by sorry

-- SimpleProductMulExponentialGreater
theorem term_derivation_simple_product_mul_exponential_greater : true := by sorry

-- SimpleProductMulBaseLess
theorem term_derivation_simple_product_mul_base_less : true := by sorry

-- SimpleProductMulBaseGreater
theorem term_derivation_simple_product_mul_base_greater : true := by sorry

-- AddSum
theorem term_derivation_add_sum : true := by sorry

-- DivEq
theorem term_derivation_div_eq : true := by sorry

-- DivLiteral
theorem term_derivation_div_literal : true := by sorry

-- LiteralMulSum
theorem term_derivation_literal_mul_sum : true := by sorry

-- SumAddLiteral
theorem term_derivation_sum_add_literal : true := by sorry

-- ProductAddLiteral
theorem term_derivation_product_add_literal : true := by sorry

-- DivAtom
theorem term_derivation_div_atom : true := by sorry

-- AtomMulExponentialLess
theorem term_derivation_atom_mul_exponential_less : true := by sorry

-- AtomMulExponentialGreater
theorem term_derivation_atom_mul_exponential_greater : true := by sorry


def h (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
  first
  | have h1 : (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) = (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by calc
    (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) = (2 : ℝ) * a ^ 2 + (2 : ℝ) * b ^ 2 + (2 : ℝ) * c ^ 2 - (2 : ℝ) * a * b - (2 : ℝ) * b * c - (2 : ℝ) * c * a := by obvious
    _ = a ^ 2 - (2 : ℝ) * a * b + b ^ 2 + (b ^ 2 - (2 : ℝ) * b * c + c ^ 2) + (c ^ 2 - (2 : ℝ) * c * a + a ^ 2) := by obvious
    _ = (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by obvious
  | have h2 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by calc
    (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = a ^ 2 - (2 : ℝ) * a * b + b ^ 2 + (b ^ 2 - (2 : ℝ) * b * c + c ^ 2) + (c ^ 2 - (2 : ℝ) * c * a + a ^ 2) := by obvious
    _ = (2 : ℝ) * a ^ 2 + (2 : ℝ) * b ^ 2 + (2 : ℝ) * c ^ 2 - (2 : ℝ) * a * b - (2 : ℝ) * b * c - (2 : ℝ) * c * a := by obvious
    _ = (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by obvious
  have h3 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ (0 : ℝ) := by obvious
  have h4 : (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) ≥ (0 : ℝ) := by obvious
  have h5 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a ≥ (0 : ℝ) := by litnum_bound
  have h6 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have d : a = a := by term_derivation_reflection
    have d1 : 2 = 2 := by term_derivation_reflection
    have d2 : a ^ 2 = (1 : ℝ) * a ^ 2 := by term_derivation_non_reduced_power
    have d3 : b = b := by term_derivation_reflection
    have d4 : 2 = 2 := by term_derivation_reflection
    have d5 : b ^ 2 = (1 : ℝ) * b ^ 2 := by term_derivation_non_reduced_power
    have d6 : (1 : ℝ) * a ^ 2 + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_product_add_product_greater
    have d7 : a ^ 2 + b ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_eq
    have d8 : c = c := by term_derivation_reflection
    have d9 : 2 = 2 := by term_derivation_reflection
    have d10 : c ^ 2 = (1 : ℝ) * c ^ 2 := by term_derivation_non_reduced_power
    have d11 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_reflection
    have d12 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_reflection
    have d13 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_sum_add_product_greater
    have d14 : a ^ 2 + b ^ 2 + c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_eq
    have d15 : a = a := by term_derivation_reflection
    have d16 : b = b := by term_derivation_reflection
    have d17 : a * b = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d18 : a * b = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d19 : -((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_neg_product
    have d20 : -(a * b) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_neg_eq
    have d21 : -1 = -1 := by term_derivation_reflection
    have d22 : b = b := by term_derivation_reflection
    have d23 : b ^ 1 = b := by term_derivation_power_one
    have d24 : a = a := by term_derivation_reflection
    have d25 : a ^ 1 = a := by term_derivation_power_one
    have d26 : b * a = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d27 : b ^ 1 * a ^ 1 = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d28 : (-1 : ℤ) * (1 : ℤ) = -1 := by term_derivation_literal_mul_literal
    have d29 : (-1 : ℝ) * b ^ 1 = (-1 : ℝ) * b ^ 1 := by term_derivation_reflection
    have d30 : (-1 : ℝ) * b ^ 1 * a ^ 1 = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_simple_product_mul_exponential_less
    have d31 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_product
    have d32 : (-1 : ℝ) * ((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_product
    have d33 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d34 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_zero_add
    have d35 : (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_product_add_product_less
    have d36 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_sum_add_product_greater
    have d37 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_reflection
    have d38 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_sum_add_product_greater
    have d39 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_reflection
    have d40 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_sum_add_product_greater
    have d41 : a ^ 2 + b ^ 2 + c ^ 2 + (-(a * b) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_eq
    have d42 : a ^ 2 + b ^ 2 + c ^ 2 - a * b = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_sub_eqs_add_neg
    have d43 : b = b := by term_derivation_reflection
    have d44 : c = c := by term_derivation_reflection
    have d45 : b * c = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_atom_mul_atom
    have d46 : b * c = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_mul_eq
    have d47 : -((1 : ℝ) * (c ^ 1 * b ^ 1)) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_neg_product
    have d48 : -(b * c) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_neg_eq
    have d49 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_reflection
    have d50 : a ^ 2 + b ^ 2 + c ^ 2 - a * b + (-(b * c) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_eq
    have d51 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_sub_eqs_add_neg
    have d52 : c = c := by term_derivation_reflection
    have d53 : a = a := by term_derivation_reflection
    have d54 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d55 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d56 : -((1 : ℝ) * (c ^ 1 * a ^ 1)) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_neg_product
    have d57 : -(c * a) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_neg_eq
    have d58 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_reflection
    have d59 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_reflection
    have d60 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_sum_add_product_greater
    have d61 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_reflection
    have d62 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_sum_add_product_greater
    have d63 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_reflection
    have d64 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_sum_add_product_greater
    have d65 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_reflection
    have d66 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_sum_add_product_greater
    have d67 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c + (-(c * a) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_eq
    have d68 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_sub_eqs_add_neg
    have d69 : 0 = 0 := by term_derivation_reflection
    have d70 : -1 = -1 := by term_derivation_reflection
    have d71 : b = b := by term_derivation_reflection
    have d72 : b ^ 1 = b := by term_derivation_power_one
    have d73 : a = a := by term_derivation_reflection
    have d74 : a ^ 1 = a := by term_derivation_power_one
    have d75 : b * a = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d76 : b ^ 1 * a ^ 1 = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d77 : (-1 : ℤ) * (1 : ℤ) = -1 := by term_derivation_literal_mul_literal
    have d78 : (-1 : ℝ) * b ^ 1 = (-1 : ℝ) * b ^ 1 := by term_derivation_reflection
    have d79 : (-1 : ℝ) * b ^ 1 * a ^ 1 = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_simple_product_mul_exponential_less
    have d80 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_product
    have d81 : (-1 : ℝ) * ((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_product
    have d82 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d83 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_zero_add
    have d84 : -1 = -1 := by term_derivation_reflection
    have d85 : c = c := by term_derivation_reflection
    have d86 : c ^ 1 = c := by term_derivation_power_one
    have d87 : a = a := by term_derivation_reflection
    have d88 : a ^ 1 = a := by term_derivation_power_one
    have d89 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d90 : c ^ 1 * a ^ 1 = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d91 : (-1 : ℤ) * (1 : ℤ) = -1 := by term_derivation_literal_mul_literal
    have d92 : (-1 : ℝ) * c ^ 1 = (-1 : ℝ) * c ^ 1 := by term_derivation_reflection
    have d93 : (-1 : ℝ) * c ^ 1 * a ^ 1 = (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_simple_product_mul_exponential_less
    have d94 : (-1 : ℝ) * (c ^ 1 * a ^ 1) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_mul_product
    have d95 : (-1 : ℝ) * ((1 : ℝ) * (c ^ 1 * a ^ 1)) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_mul_product
    have d96 : (-1 : ℝ) * (c ^ 1 * a ^ 1) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d97 : (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_product_add_product_less
    have d98 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_add_eq
    have d99 : b = b := by term_derivation_reflection
    have d100 : 2 = 2 := by term_derivation_reflection
    have d101 : b ^ 2 = (1 : ℝ) * b ^ 2 := by term_derivation_non_reduced_power
    have d102 : (1 : ℝ) * b ^ 2 = (1 : ℝ) * b ^ 2 := by term_derivation_one_mul
    have d103 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_reflection
    have d104 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_add_eq
    have d105 : c = c := by term_derivation_reflection
    have d106 : 2 = 2 := by term_derivation_reflection
    have d107 : c ^ 2 = (1 : ℝ) * c ^ 2 := by term_derivation_non_reduced_power
    have d108 : (1 : ℝ) * c ^ 2 = (1 : ℝ) * c ^ 2 := by term_derivation_one_mul
    have d109 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_reflection
    have d110 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_add_eq
    have d111 : a = a := by term_derivation_reflection
    have d112 : 2 = 2 := by term_derivation_reflection
    have d113 : a ^ 2 = (1 : ℝ) * a ^ 2 := by term_derivation_non_reduced_power
    have d114 : (1 : ℝ) * a ^ 2 = (1 : ℝ) * a ^ 2 := by term_derivation_one_mul
    have d115 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_reflection
    have d116 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_eq
    have d117 : -1 = -1 := by term_derivation_reflection
    have d118 : c = c := by term_derivation_reflection
    have d119 : c ^ 1 = c := by term_derivation_power_one
    have d120 : b = b := by term_derivation_reflection
    have d121 : b ^ 1 = b := by term_derivation_power_one
    have d122 : c * b = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_atom_mul_atom
    have d123 : c ^ 1 * b ^ 1 = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_mul_eq
    have d124 : (-1 : ℤ) * (1 : ℤ) = -1 := by term_derivation_literal_mul_literal
    have d125 : (-1 : ℝ) * c ^ 1 = (-1 : ℝ) * c ^ 1 := by term_derivation_reflection
    have d126 : (-1 : ℝ) * c ^ 1 * b ^ 1 = (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_simple_product_mul_exponential_less
    have d127 : (-1 : ℝ) * (c ^ 1 * b ^ 1) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_mul_product
    have d128 : (-1 : ℝ) * ((1 : ℝ) * (c ^ 1 * b ^ 1)) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_mul_product
    have d129 : (-1 : ℝ) * (c ^ 1 * b ^ 1) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_mul_eq
    have d130 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_reflection
    have d131 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_eq
    have d132 : -(0 : ℤ) = 0 := by term_derivation_neg_literal
    have d133 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) + (0 : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_nf_add_zero
    have d134 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) + (-(0 : ℤ) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_eq
    have d135 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) - (0 : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_sub_eqs_add_neg
    have d136 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a ≥ (0 : ℝ) ↔ (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) ≥ (0 : ℝ) := by term_derivation_num_comparison
    have d137 : a = a := by term_derivation_reflection
    have d138 : 2 = 2 := by term_derivation_reflection
    have d139 : a ^ 2 = (1 : ℝ) * a ^ 2 := by term_derivation_non_reduced_power
    have d140 : b = b := by term_derivation_reflection
    have d141 : 2 = 2 := by term_derivation_reflection
    have d142 : b ^ 2 = (1 : ℝ) * b ^ 2 := by term_derivation_non_reduced_power
    have d143 : (1 : ℝ) * a ^ 2 + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_product_add_product_greater
    have d144 : a ^ 2 + b ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_eq
    have d145 : c = c := by term_derivation_reflection
    have d146 : 2 = 2 := by term_derivation_reflection
    have d147 : c ^ 2 = (1 : ℝ) * c ^ 2 := by term_derivation_non_reduced_power
    have d148 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_reflection
    have d149 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_reflection
    have d150 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_sum_add_product_greater
    have d151 : a ^ 2 + b ^ 2 + c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_eq
    have d152 : a = a := by term_derivation_reflection
    have d153 : b = b := by term_derivation_reflection
    have d154 : a * b = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d155 : a * b = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d156 : b = b := by term_derivation_reflection
    have d157 : c = c := by term_derivation_reflection
    have d158 : b * c = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_atom_mul_atom
    have d159 : b * c = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_mul_eq
    have d160 : (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_product_add_product_less
    have d161 : a * b + b * c = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_eq
    have d162 : c = c := by term_derivation_reflection
    have d163 : a = a := by term_derivation_reflection
    have d164 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d165 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d166 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_reflection
    have d167 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_reflection
    have d168 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_sum_add_product_greater
    have d169 : a * b + b * c + c * a = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_eq
    have d170 : b = b := by term_derivation_reflection
    have d171 : 2 = 2 := by term_derivation_reflection
    have d172 : b ^ 2 = (1 : ℝ) * b ^ 2 := by term_derivation_non_reduced_power
    have d173 : (1 : ℝ) * b ^ 2 = (1 : ℝ) * b ^ 2 := by term_derivation_one_mul
    have d174 : (0 : ℝ) + (1 : ℝ) * b ^ 2 = (1 : ℝ) * b ^ 2 := by term_derivation_zero_add
    have d175 : c = c := by term_derivation_reflection
    have d176 : 2 = 2 := by term_derivation_reflection
    have d177 : c ^ 2 = (1 : ℝ) * c ^ 2 := by term_derivation_non_reduced_power
    have d178 : (1 : ℝ) * c ^ 2 = (1 : ℝ) * c ^ 2 := by term_derivation_one_mul
    have d179 : (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_product_add_product_less
    have d180 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_add_eq
    have d181 : a = a := by term_derivation_reflection
    have d182 : 2 = 2 := by term_derivation_reflection
    have d183 : a ^ 2 = (1 : ℝ) * a ^ 2 := by term_derivation_non_reduced_power
    have d184 : (1 : ℝ) * a ^ 2 = (1 : ℝ) * a ^ 2 := by term_derivation_one_mul
    have d185 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_reflection
    have d186 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_eq
    have d187 : b = b := by term_derivation_reflection
    have d188 : b ^ 1 = b := by term_derivation_power_one
    have d189 : a = a := by term_derivation_reflection
    have d190 : a ^ 1 = a := by term_derivation_power_one
    have d191 : b * a = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d192 : b ^ 1 * a ^ 1 = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d193 : (1 : ℝ) * (b ^ 1 * a ^ 1) = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_one_mul
    have d194 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_zero_add
    have d195 : c = c := by term_derivation_reflection
    have d196 : c ^ 1 = c := by term_derivation_power_one
    have d197 : a = a := by term_derivation_reflection
    have d198 : a ^ 1 = a := by term_derivation_power_one
    have d199 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d200 : c ^ 1 * a ^ 1 = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d201 : (1 : ℝ) * (c ^ 1 * a ^ 1) = (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_one_mul
    have d202 : (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_product_add_product_less
    have d203 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_add_eq
    have d204 : c = c := by term_derivation_reflection
    have d205 : c ^ 1 = c := by term_derivation_power_one
    have d206 : b = b := by term_derivation_reflection
    have d207 : b ^ 1 = b := by term_derivation_power_one
    have d208 : c * b = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_atom_mul_atom
    have d209 : c ^ 1 * b ^ 1 = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_mul_eq
    have d210 : (1 : ℝ) * (c ^ 1 * b ^ 1) = (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_one_mul
    have d211 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_reflection
    have d212 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_eq
    have d213 : -(0 : ℤ) = 0 := by term_derivation_neg_literal
    have d214 : -((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_neg_product
    have d215 : -((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_neg_sum
    have d216 : -((1 : ℝ) * (c ^ 1 * a ^ 1)) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_neg_product
    have d217 : -((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_neg_sum
    have d218 : -((1 : ℝ) * (c ^ 1 * b ^ 1)) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_neg_product
    have d219 : -((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_neg_sum
    have d220 : -((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_neg_eq
    have d221 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (0 : ℝ) = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_nf_add_zero
    have d222 : -1 = -1 := by term_derivation_reflection
    have d223 : b = b := by term_derivation_reflection
    have d224 : b ^ 1 = b := by term_derivation_power_one
    have d225 : a = a := by term_derivation_reflection
    have d226 : a ^ 1 = a := by term_derivation_power_one
    have d227 : b * a = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_atom_mul_atom
    have d228 : b ^ 1 * a ^ 1 = (1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d229 : (-1 : ℤ) * (1 : ℤ) = -1 := by term_derivation_literal_mul_literal
    have d230 : (-1 : ℝ) * b ^ 1 = (-1 : ℝ) * b ^ 1 := by term_derivation_reflection
    have d231 : (-1 : ℝ) * b ^ 1 * a ^ 1 = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_simple_product_mul_exponential_less
    have d232 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_product
    have d233 : (-1 : ℝ) * ((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_product
    have d234 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_mul_eq
    have d235 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := by term_derivation_zero_add
    have d236 : (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_product_add_product_less
    have d237 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_sum_add_product_greater
    have d238 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_reflection
    have d239 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_sum_add_product_greater
    have d240 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_reflection
    have d241 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_sum_add_product_greater
    have d242 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + ((0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_sum
    have d243 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := by term_derivation_reflection
    have d244 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_reflection
    have d245 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := by term_derivation_sum_add_product_greater
    have d246 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_reflection
    have d247 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := by term_derivation_sum_add_product_greater
    have d248 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_reflection
    have d249 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_sum_add_product_greater
    have d250 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + ((0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := by term_derivation_add_sum
    have d251 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_reflection
    have d252 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + ((0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * b ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_sum
    have d253 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1)) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_add_eq
    have d254 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 - ((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := by term_derivation_sub_eqs_add_neg
    have d255 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a ↔ (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) ≥ (0 : ℝ) := by term_derivation_num_comparison
    have d256 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by term_derivation_non_trivial_finish
    assumption
  obvious

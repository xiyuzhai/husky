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

-- AtomAddSwap
theorem term_derivation_atom_add_swap : true := by sorry

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


def h (a b : ℝ) : (a + b) ^ 2 ≥ (0 : ℝ) := by
  have h1 : (a + b) ^ 2 ≥ (0 : ℝ) := by apply sq_nonneg
  obvious

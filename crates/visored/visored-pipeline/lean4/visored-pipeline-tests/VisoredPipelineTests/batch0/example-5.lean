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

def h (a b : ℝ) : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) ≥ ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) := by
  first
  | have h1 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) - ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by calc
    (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) - ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) = (((2:ℕ) : ℝ) * a ^ (2:ℕ) + ((2:ℕ) : ℝ) * b ^ (2:ℕ)) / ((4:ℕ) : ℝ) - (a ^ (2:ℕ) + ((2:ℕ) : ℝ) * a * b + b ^ (2:ℕ)) / ((4:ℕ) : ℝ) := by obvious
    _ = (a ^ (2:ℕ) - ((2:ℕ) : ℝ) * a * b + b ^ (2:ℕ)) / ((4:ℕ) : ℝ) := by obvious
    _ = (a - b) ^ (2:ℕ) / ((4:ℕ) : ℝ) := by obvious
    _ ≥ (0:ℕ) : ℝ := by obvious
  | have h2 : (a - b) ^ (2:ℕ) / ((4:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    (a - b) ^ (2:ℕ) / ((4:ℕ) : ℝ) = (a ^ (2:ℕ) - ((2:ℕ) : ℝ) * a * b + b ^ (2:ℕ)) / ((4:ℕ) : ℝ) := by obvious
    _ = (((2:ℕ) : ℝ) * a ^ (2:ℕ) + ((2:ℕ) : ℝ) * b ^ (2:ℕ)) / ((4:ℕ) : ℝ) - (a ^ (2:ℕ) + ((2:ℕ) : ℝ) * a * b + b ^ (2:ℕ)) / ((4:ℕ) : ℝ) := by obvious
    _ = (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) - ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) := by obvious
    _ ≥ (0:ℕ) : ℝ := by obvious
  have h3 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) - ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by obvious
  have h4 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) ≥ ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) := by
    have d : a = a := by term_derivation_reflection
    have d1 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d2 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d3 : b = b := by term_derivation_reflection
    have d4 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d5 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d6 : ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_greater
    have d7 : a ^ (2:ℕ) + b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d2 d5 eq_identity_coercion eq_identity_coercion d6
    have d8 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d9 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) ^ (1:ℕ) := by term_derivation_base_mul_literal
    have d10 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d11 : (1 : ℚ) / 2 * ((0:ℕ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d12 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d13 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d14 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d15 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_literal_mul_sum
    have d16 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d17 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d18 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_product
    have d19 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_literal_mul_sum
    have d20 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_div_literal
    have d21 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_div_eq
    have d22 : a = a := by term_derivation_reflection
    have d23 : b = b := by term_derivation_reflection
    have d24 : a + ((1:ℕ) : ℝ) * b ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_atom_add_product
    have d25 : a + b = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_add_atom d24
    have d26 : a + b = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_identity_coercion d25
    have d27 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d28 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) ^ (1:ℕ) := by term_derivation_base_mul_literal
    have d29 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (1 : ℚ) / 2 * ((0:ℕ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d31 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d32 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_reflection
    have d33 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_product
    have d34 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_literal_mul_sum
    have d35 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d36 : ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_reflection
    have d37 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_mul_product
    have d38 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_literal_mul_sum
    have d39 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_div_literal
    have d40 : (a + b) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_div_eq
    have d41 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d42 : ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d43 : (-(((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) : ℝ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_neg_product
    have d44 : (-((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_neg_eq
    have d45 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_reflection
    have d46 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d47 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d48 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) + (-((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d21 d44 eq_identity_coercion eq_identity_coercion d47
    have d49 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) - ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sub_eqs_add_neg d48 neg_identity_coercion
    have d50 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d51 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d52 : b = b := by term_derivation_reflection
    have d53 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d54 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d55 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d56 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d57 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d58 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_eq
    have d59 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_zero_add
    have d60 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d61 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d62 : b = b := by term_derivation_reflection
    have d63 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d64 : ((1 : ℚ) / 2 : ℝ) * b = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d65 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_eq
    have d66 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_zero_add
    have d67 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d68 : a = a := by term_derivation_reflection
    have d69 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d70 : ((1 : ℚ) / 2 : ℝ) * a = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d71 : ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_mul_eq
    have d72 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_product_add_product_less
    have d73 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_add_eq d66 d71 eq_identity_coercion eq_identity_coercion d72
    have d74 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d75 : (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d76 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d77 : ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_reflection
    have d78 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_mul_product
    have d79 : ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_mul_eq
    have d80 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d81 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_add_eq d59 d79 eq_identity_coercion eq_identity_coercion d80
    have d82 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d83 : a = a := by term_derivation_reflection
    have d84 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d85 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d86 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d87 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d88 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_product
    have d89 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_eq
    have d90 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d91 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d81 d89 eq_identity_coercion eq_identity_coercion d90
    have d92 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d93 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_nf_add_zero
    have d94 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d91 d92 eq_identity_coercion eq_nat_to_real_coercion d93
    have d95 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) - ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sub_eqs_add_neg d94 neg_nat_to_real_coercion
    have d96 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) - ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) ↔ ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d97 : a = a := by term_derivation_reflection
    have d98 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d99 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d100 : b = b := by term_derivation_reflection
    have d101 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d102 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d103 : ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_greater
    have d104 : a ^ (2:ℕ) + b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d99 d102 eq_identity_coercion eq_identity_coercion d103
    have d105 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d106 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) ^ (1:ℕ) := by term_derivation_base_mul_literal
    have d107 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d108 : (1 : ℚ) / 2 * ((0:ℕ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d109 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d110 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d111 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d112 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_literal_mul_sum
    have d113 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d114 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d115 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_product
    have d116 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_literal_mul_sum
    have d117 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_div_literal
    have d118 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_div_eq
    have d119 : a = a := by term_derivation_reflection
    have d120 : b = b := by term_derivation_reflection
    have d121 : a + ((1:ℕ) : ℝ) * b ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_atom_add_product
    have d122 : a + b = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_add_atom d121
    have d123 : a + b = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_add_eq d119 d120 eq_identity_coercion eq_identity_coercion d122
    have d124 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d125 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) ^ (1:ℕ) := by term_derivation_base_mul_literal
    have d126 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d127 : (1 : ℚ) / 2 * ((0:ℕ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d128 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d129 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_reflection
    have d130 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_product
    have d131 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_literal_mul_sum
    have d132 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d133 : ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_reflection
    have d134 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_mul_product
    have d135 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_literal_mul_sum
    have d136 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_div_literal
    have d137 : (a + b) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_div_eq
    have d138 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d139 : ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d140 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d141 : b = b := by term_derivation_reflection
    have d142 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d143 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d144 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d145 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d146 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d147 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_eq
    have d148 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_zero_add
    have d149 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d150 : a = a := by term_derivation_reflection
    have d151 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d152 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d153 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_literal_mul_literal
    have d154 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d155 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_product
    have d156 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_eq
    have d157 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d158 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d148 d156 eq_identity_coercion eq_identity_coercion d157
    have d159 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d160 : b = b := by term_derivation_reflection
    have d161 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d162 : ((1 : ℚ) / 2 : ℝ) * b = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d163 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_eq
    have d164 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_zero_add
    have d165 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d166 : a = a := by term_derivation_reflection
    have d167 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d168 : ((1 : ℚ) / 2 : ℝ) * a = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d169 : ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_mul_eq
    have d170 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_product_add_product_less
    have d171 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_add_eq d164 d169 eq_identity_coercion eq_identity_coercion d170
    have d172 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d173 : (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d174 : ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_one_mul
    have d175 : (-(((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) : ℝ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_neg_product
    have d176 : (-(((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) : ℝ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_neg_eq
    have d177 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_reflection
    have d178 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d179 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d180 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + (-(((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d158 d176 eq_identity_coercion eq_identity_coercion d179
    have d181 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) - ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sub_eqs_add_neg d180 neg_identity_coercion
    have d182 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) ≥ ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) ↔ ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d183 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) ≥ ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) := by term_derivation_non_trivial_finish
    assumption
  obvious

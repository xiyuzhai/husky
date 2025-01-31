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
    have d12 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d13 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d14 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d15 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d16 : b = b := by term_derivation_reflection
    have d17 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d18 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d19 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d20 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d21 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d22 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_eq
    have d23 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_zero_add
    have d24 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_literal_mul_sum
    have d25 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d26 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d27 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_product
    have d28 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d29 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_literal_mul_sum
    have d30 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_div_literal
    have d31 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_div_eq
    have d32 : a = a := by term_derivation_reflection
    have d33 : b = b := by term_derivation_reflection
    have d34 : a + ((1:ℕ) : ℝ) * b ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_atom_add_product
    have d35 : a + b = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_add_atom d34
    have d36 : a + b = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_add_eq d32 d33 eq_identity_coercion eq_identity_coercion d35
    have d37 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d38 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) ^ (1:ℕ) := by term_derivation_base_mul_literal
    have d39 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d40 : (1 : ℚ) / 2 * ((0:ℕ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d41 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d42 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_reflection
    have d43 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_product
    have d44 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d45 : b = b := by term_derivation_reflection
    have d46 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d47 : ((1 : ℚ) / 2 : ℝ) * b = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d48 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_eq
    have d49 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_zero_add
    have d50 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_literal_mul_sum
    have d51 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d52 : ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_reflection
    have d53 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_mul_product
    have d54 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_product_add_product_less
    have d55 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_literal_mul_sum
    have d56 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_div_literal
    have d57 : (a + b) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_div_eq
    have d58 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d59 : ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d60 : (-(((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) : ℝ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_neg_product
    have d61 : (-((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_neg_eq
    have d62 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_reflection
    have d63 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d64 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d65 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) + (-((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d31 d61 eq_identity_coercion eq_identity_coercion d64
    have d66 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) - ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sub_eqs_add_neg d65 neg_identity_coercion
    have d67 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d68 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d69 : b = b := by term_derivation_reflection
    have d70 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d71 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d72 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d73 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d74 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d75 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_eq
    have d76 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_zero_add
    have d77 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d78 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d79 : b = b := by term_derivation_reflection
    have d80 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d81 : ((1 : ℚ) / 2 : ℝ) * b = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d82 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_eq
    have d83 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_zero_add
    have d84 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d85 : a = a := by term_derivation_reflection
    have d86 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d87 : ((1 : ℚ) / 2 : ℝ) * a = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d88 : ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_mul_eq
    have d89 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_product_add_product_less
    have d90 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_add_eq d83 d88 eq_identity_coercion eq_identity_coercion d89
    have d91 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d92 : (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d93 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d94 : ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_reflection
    have d95 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_mul_product
    have d96 : ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_mul_eq
    have d97 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d98 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_add_eq d76 d96 eq_identity_coercion eq_identity_coercion d97
    have d99 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d100 : a = a := by term_derivation_reflection
    have d101 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d102 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d103 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d104 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d105 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_product
    have d106 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_eq
    have d107 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d108 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d98 d106 eq_identity_coercion eq_identity_coercion d107
    have d109 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d110 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_nf_add_zero
    have d111 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d108 d109 eq_identity_coercion eq_int_to_real_coercion d110
    have d112 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) - ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sub_eqs_add_neg d111 neg_nat_to_real_coercion
    have d113 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) - ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) ↔ ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d114 : a = a := by term_derivation_reflection
    have d115 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d116 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d117 : b = b := by term_derivation_reflection
    have d118 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d119 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d120 : ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_greater
    have d121 : a ^ (2:ℕ) + b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d116 d119 eq_identity_coercion eq_identity_coercion d120
    have d122 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d123 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) ^ (1:ℕ) := by term_derivation_base_mul_literal
    have d124 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d125 : (1 : ℚ) / 2 * ((0:ℕ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d126 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d127 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d128 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d129 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d130 : b = b := by term_derivation_reflection
    have d131 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d132 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d133 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d134 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d135 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d136 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_eq
    have d137 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_zero_add
    have d138 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_literal_mul_sum
    have d139 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d140 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d141 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_product
    have d142 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d143 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_literal_mul_sum
    have d144 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_div_literal
    have d145 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_div_eq
    have d146 : a = a := by term_derivation_reflection
    have d147 : b = b := by term_derivation_reflection
    have d148 : a + ((1:ℕ) : ℝ) * b ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_atom_add_product
    have d149 : a + b = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_add_atom d148
    have d150 : a + b = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ) := by term_derivation_add_eq d146 d147 eq_identity_coercion eq_identity_coercion d149
    have d151 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d152 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) ^ (1:ℕ) := by term_derivation_base_mul_literal
    have d153 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d154 : (1 : ℚ) / 2 * ((0:ℕ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d155 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d156 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_reflection
    have d157 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_product
    have d158 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d159 : b = b := by term_derivation_reflection
    have d160 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d161 : ((1 : ℚ) / 2 : ℝ) * b = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d162 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_eq
    have d163 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_zero_add
    have d164 : ((1 : ℚ) / 2 : ℝ) * (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_literal_mul_sum
    have d165 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d166 : ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_reflection
    have d167 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (1:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_mul_product
    have d168 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_product_add_product_less
    have d169 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) * ((1 : ℚ) / 2 : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_literal_mul_sum
    have d170 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (1:ℕ) + ((1:ℕ) : ℝ) * a ^ (1:ℕ)) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_div_literal
    have d171 : (a + b) / ((2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_div_eq
    have d172 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d173 : ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d174 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d175 : b = b := by term_derivation_reflection
    have d176 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d177 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d178 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d179 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d180 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * b ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_product
    have d181 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_mul_eq
    have d182 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) := by term_derivation_zero_add
    have d183 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d184 : a = a := by term_derivation_reflection
    have d185 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d186 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d187 : (1 : ℚ) / 2 * ((1:ℕ) : ℚ) = (1 : ℚ) / 2 := by term_derivation_mul_one
    have d188 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d189 : ((1 : ℚ) / 2 : ℝ) * (((1:ℕ) : ℝ) * a ^ (2:ℕ)) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_product
    have d190 : ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_mul_eq
    have d191 : ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d192 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d182 d190 eq_identity_coercion eq_identity_coercion d191
    have d193 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d194 : b = b := by term_derivation_reflection
    have d195 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d196 : ((1 : ℚ) / 2 : ℝ) * b = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d197 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_mul_eq
    have d198 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) := by term_derivation_zero_add
    have d199 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := by term_derivation_reflection
    have d200 : a = a := by term_derivation_reflection
    have d201 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d202 : ((1 : ℚ) / 2 : ℝ) * a = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_non_one_literal_mul_atom
    have d203 : ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_mul_eq
    have d204 : ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_product_add_product_less
    have d205 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ) := by term_derivation_add_eq d198 d203 eq_identity_coercion eq_identity_coercion d204
    have d206 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d207 : (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d208 : ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_one_mul
    have d209 : (-(((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) : ℝ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_neg_product
    have d210 : (-(((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) : ℝ) = ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_neg_eq
    have d211 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) := by term_derivation_reflection
    have d212 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d213 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d214 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) + (-(((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ)) : ℝ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d192 d210 eq_identity_coercion eq_identity_coercion d213
    have d215 : ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) - ((1:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) := by term_derivation_sub_eqs_add_neg d214 neg_identity_coercion
    have d216 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) ≥ ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) ↔ ((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (((0:ℕ) : ℝ) + ((1 : ℚ) / 2 : ℝ) * b ^ (1:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (1:ℕ)) ^ (2:ℕ) + ((1 : ℚ) / 2 : ℝ) * a ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d217 : (a ^ (2:ℕ) + b ^ (2:ℕ)) / ((2:ℕ) : ℝ) ≥ ((a + b) / ((2:ℕ) : ℝ)) ^ (2:ℕ) := by term_derivation_non_trivial_hypothesis_equivalence h3 d113 d216
    assumption
  obvious

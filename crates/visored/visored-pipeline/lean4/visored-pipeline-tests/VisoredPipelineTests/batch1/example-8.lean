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

def h (a b : ℝ) (h1 : a > (0 : ℝ)) (h2 : b > (0 : ℝ)) : a / b + b / a ≥ (2 : ℝ) := by
  have h3 : a > (0 : ℝ) := by old_main_hypothesis
  have h4 : b > (0 : ℝ) := by old_main_hypothesis
  first
  | have h5 : (√ (a / b) - √ (b / a)) ^ 2 ≥ (0 : ℝ) := by calc
    (√ (a / b) - √ (b / a)) ^ 2 = √ (a / b) ^ 2 - (2 : ℝ) * √ (a / b) * √ (b / a) + √ (b / a) ^ 2 := by obvious
    _ = a / b - (2 : ℝ) + b / a := by obvious
    _ ≥ 0 : ℝ := by obvious
  | have h6 : a / b - (2 : ℝ) + b / a ≥ (0 : ℝ) := by calc
    a / b - (2 : ℝ) + b / a = √ (a / b) ^ 2 - (2 : ℝ) * √ (a / b) * √ (b / a) + √ (b / a) ^ 2 := by obvious
    _ = (√ (a / b) - √ (b / a)) ^ 2 := by obvious
    _ ≥ 0 : ℝ := by obvious
  have h7 : a / b - (2 : ℝ) + b / a ≥ (0 : ℝ) := by obvious
  have h8 : a / b + b / a ≥ (2 : ℝ) := by
    have d : a = a := by term_derivation_reflection
    have d1 : b = b := by term_derivation_reflection
    have d2 : a * b ^ (-1 : ℤ) = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_atom_mul_exponential_greater
    have d3 : a / b = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_div_atom
    have d4 : a / b = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_div_eq
    have d5 : (-(2 : ℤ) : ℤ) = (-2 : ℤ) := by term_derivation_neg_literal
    have d6 : (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + ((-2 : ℤ) : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_product_add_literal
    have d7 : a / b + ((-(2 : ℤ) : ℤ) : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_add_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d6
    have d8 : a / b - (2 : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_sub_eqs_add_neg
    have d9 : b = b := by term_derivation_reflection
    have d10 : a = a := by term_derivation_reflection
    have d11 : b * a ^ (-1 : ℤ) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_atom_mul_exponential_less
    have d12 : b / a = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_div_atom
    have d13 : b / a = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_div_eq
    have d14 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_reflection
    have d15 : a / b - (2 : ℝ) + b / a = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_add_eq d8 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : 0 = 0 := by term_derivation_reflection
    have d17 : (-2 : ℤ) = (-2 : ℤ) := by term_derivation_reflection
    have d18 : b = b := by term_derivation_reflection
    have d19 : (-1 : ℤ) = (-1 : ℤ) := by term_derivation_reflection
    have d20 : b ^ (-1 : ℤ) = (1 : ℝ) * b ^ (-1 : ℤ) := by term_derivation_non_reduced_power
    have d21 : a = a := by term_derivation_reflection
    have d22 : a ^ 1 = a := by term_derivation_power_one
    have d23 : (1 : ℝ) * b ^ (-1 : ℤ) * a = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_simple_product_mul_base_less
    have d24 : b ^ (-1 : ℤ) * a ^ 1 = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_mul_eq
    have d25 : (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_one_mul
    have d26 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_reflection
    have d27 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_add_eq d17 d25 eq_int_to_real_coercion eq_identity_coercion d26
    have d28 : b = b := by term_derivation_reflection
    have d29 : b ^ 1 = b := by term_derivation_power_one
    have d30 : a = a := by term_derivation_reflection
    have d31 : (-1 : ℤ) = (-1 : ℤ) := by term_derivation_reflection
    have d32 : a ^ (-1 : ℤ) = (1 : ℝ) * a ^ (-1 : ℤ) := by term_derivation_non_reduced_power
    have d33 : b * (1 : ℝ) = (1 : ℝ) * b ^ 1 := by term_derivation_base_mul_literal
    have d34 : (1 : ℝ) * b ^ 1 * a ^ (-1 : ℤ) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_simple_product_mul_exponential_less
    have d35 : b * ((1 : ℝ) * a ^ (-1 : ℤ)) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_mul_product
    have d36 : b ^ 1 * a ^ (-1 : ℤ) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_mul_eq
    have d37 : (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_one_mul
    have d38 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_reflection
    have d39 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_add_eq d27 d37 eq_identity_coercion eq_identity_coercion d38
    have d40 : (-(0 : ℤ) : ℤ) = 0 := by term_derivation_neg_literal
    have d41 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) + (0 : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_nf_add_zero
    have d42 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) + ((-(0 : ℤ) : ℤ) : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_add_eq d39 d40 eq_identity_coercion eq_nat_to_real_coercion d41
    have d43 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) - (0 : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_sub_eqs_add_neg
    have d44 : a / b - (2 : ℝ) + b / a ≥ (0 : ℝ) ↔ ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) ≥ (0 : ℝ) := by term_derivation_num_comparison
    have d45 : a = a := by term_derivation_reflection
    have d46 : b = b := by term_derivation_reflection
    have d47 : a * b ^ (-1 : ℤ) = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_atom_mul_exponential_greater
    have d48 : a / b = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_div_atom
    have d49 : a / b = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_div_eq
    have d50 : b = b := by term_derivation_reflection
    have d51 : a = a := by term_derivation_reflection
    have d52 : b * a ^ (-1 : ℤ) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_atom_mul_exponential_less
    have d53 : b / a = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_div_atom
    have d54 : b / a = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_div_eq
    have d55 : (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_product_add_product_less
    have d56 : a / b + b / a = (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_add_eq d49 d54 eq_identity_coercion eq_identity_coercion d55
    have d57 : 2 = 2 := by term_derivation_reflection
    have d58 : b = b := by term_derivation_reflection
    have d59 : (-1 : ℤ) = (-1 : ℤ) := by term_derivation_reflection
    have d60 : b ^ (-1 : ℤ) = (1 : ℝ) * b ^ (-1 : ℤ) := by term_derivation_non_reduced_power
    have d61 : a = a := by term_derivation_reflection
    have d62 : a ^ 1 = a := by term_derivation_power_one
    have d63 : (1 : ℝ) * b ^ (-1 : ℤ) * a = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_simple_product_mul_base_less
    have d64 : b ^ (-1 : ℤ) * a ^ 1 = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_mul_eq
    have d65 : (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_one_mul
    have d66 : (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) = (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_zero_add
    have d67 : b = b := by term_derivation_reflection
    have d68 : b ^ 1 = b := by term_derivation_power_one
    have d69 : a = a := by term_derivation_reflection
    have d70 : (-1 : ℤ) = (-1 : ℤ) := by term_derivation_reflection
    have d71 : a ^ (-1 : ℤ) = (1 : ℝ) * a ^ (-1 : ℤ) := by term_derivation_non_reduced_power
    have d72 : b * (1 : ℝ) = (1 : ℝ) * b ^ 1 := by term_derivation_base_mul_literal
    have d73 : (1 : ℝ) * b ^ 1 * a ^ (-1 : ℤ) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_simple_product_mul_exponential_less
    have d74 : b * ((1 : ℝ) * a ^ (-1 : ℤ)) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_mul_product
    have d75 : b ^ 1 * a ^ (-1 : ℤ) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_mul_eq
    have d76 : (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_one_mul
    have d77 : (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_product_add_product_less
    have d78 : (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_add_eq d66 d76 eq_identity_coercion eq_identity_coercion d77
    have d79 : (-(2 : ℤ) : ℤ) = (-2 : ℤ) := by term_derivation_neg_literal
    have d80 : (-2 : ℤ) = (-2 : ℤ) := by term_derivation_reflection
    have d81 : (0 : ℤ) + (-2 : ℤ) = (-2 : ℤ) := by term_derivation_zero_add
    have d82 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_reflection
    have d83 : (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + ((-2 : ℤ) : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) := by term_derivation_sum_add_literal
    have d84 : ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_reflection
    have d85 : (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) + ((-2 : ℤ) : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_sum_add_literal
    have d86 : (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) + ((-(2 : ℤ) : ℤ) : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_add_eq d78 d79 eq_identity_coercion eq_int_to_real_coercion d85
    have d87 : (0 : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) - (2 : ℝ) = ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) := by term_derivation_sub_eqs_add_neg
    have d88 : a / b + b / a ≥ (2 : ℝ) ↔ ((-2 : ℤ) : ℝ) + (1 : ℝ) * (b ^ (-1 : ℤ) * a ^ 1) + (1 : ℝ) * (b ^ 1 * a ^ (-1 : ℤ)) ≥ (0 : ℝ) := by term_derivation_num_comparison
    have d89 : a / b + b / a ≥ (2 : ℝ) := by term_derivation_non_trivial_finish
    assumption
  obvious

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

def h (a b c : ℝ) : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) ≥ a * b + b * c + c * a := by
  first
  | have h1 : ((2:ℕ) : ℝ) * (a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c - c * a) = (a - b) ^ (2:ℕ) + (b - c) ^ (2:ℕ) + (c - a) ^ (2:ℕ) := by calc
    ((2:ℕ) : ℝ) * (a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c - c * a) = ((2:ℕ) : ℝ) * a ^ (2:ℕ) + ((2:ℕ) : ℝ) * b ^ (2:ℕ) + ((2:ℕ) : ℝ) * c ^ (2:ℕ) - ((2:ℕ) : ℝ) * a * b - ((2:ℕ) : ℝ) * b * c - ((2:ℕ) : ℝ) * c * a := by obvious
    _ = a ^ (2:ℕ) - ((2:ℕ) : ℝ) * a * b + b ^ (2:ℕ) + (b ^ (2:ℕ) - ((2:ℕ) : ℝ) * b * c + c ^ (2:ℕ)) + (c ^ (2:ℕ) - ((2:ℕ) : ℝ) * c * a + a ^ (2:ℕ)) := by obvious
    _ = (a - b) ^ (2:ℕ) + (b - c) ^ (2:ℕ) + (c - a) ^ (2:ℕ) := by obvious
  | have h2 : (a - b) ^ (2:ℕ) + (b - c) ^ (2:ℕ) + (c - a) ^ (2:ℕ) = ((2:ℕ) : ℝ) * (a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c - c * a) := by calc
    (a - b) ^ (2:ℕ) + (b - c) ^ (2:ℕ) + (c - a) ^ (2:ℕ) = a ^ (2:ℕ) - ((2:ℕ) : ℝ) * a * b + b ^ (2:ℕ) + (b ^ (2:ℕ) - ((2:ℕ) : ℝ) * b * c + c ^ (2:ℕ)) + (c ^ (2:ℕ) - ((2:ℕ) : ℝ) * c * a + a ^ (2:ℕ)) := by obvious
    _ = ((2:ℕ) : ℝ) * a ^ (2:ℕ) + ((2:ℕ) : ℝ) * b ^ (2:ℕ) + ((2:ℕ) : ℝ) * c ^ (2:ℕ) - ((2:ℕ) : ℝ) * a * b - ((2:ℕ) : ℝ) * b * c - ((2:ℕ) : ℝ) * c * a := by obvious
    _ = ((2:ℕ) : ℝ) * (a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c - c * a) := by obvious
  have h3 : (a - b) ^ (2:ℕ) + (b - c) ^ (2:ℕ) + (c - a) ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by obvious
  have h4 : ((2:ℕ) : ℝ) * (a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c - c * a) ≥ ((0:ℕ) : ℝ) := by obvious
  have h5 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c - c * a ≥ ((0:ℕ) : ℝ) := by litnum_bound
  have h6 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) ≥ a * b + b * c + c * a := by
    have d : a = a := by term_derivation_reflection
    have d1 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d2 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d3 : b = b := by term_derivation_reflection
    have d4 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d5 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d6 : ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_greater
    have d7 : a ^ (2:ℕ) + b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d2 d5 eq_identity_coercion eq_identity_coercion d6
    have d8 : c = c := by term_derivation_reflection
    have d9 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d10 : c ^ (2:ℕ) = ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d11 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_reflection
    have d12 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d13 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d14 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d7 d10 eq_identity_coercion eq_identity_coercion d13
    have d15 : a = a := by term_derivation_reflection
    have d16 : b = b := by term_derivation_reflection
    have d17 : a * b = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d18 : a * b = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d19 : (-(((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ))) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_neg_product
    have d20 : (-(a * b) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_neg_eq
    have d21 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d22 : b = b := by term_derivation_reflection
    have d23 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d24 : a = a := by term_derivation_reflection
    have d25 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d26 : b * a = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d27 : b ^ (1:ℕ) * a ^ (1:ℕ) = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d28 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d29 : ((-1:ℤ) : ℝ) * b ^ (1:ℕ) = ((-1:ℤ) : ℝ) * b ^ (1:ℕ) := by term_derivation_reflection
    have d30 : ((-1:ℤ) : ℝ) * b ^ (1:ℕ) * a ^ (1:ℕ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_simple_product_mul_exponential_less
    have d31 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_product
    have d32 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ))) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_product
    have d33 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d34 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_zero_add
    have d35 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d36 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d37 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_reflection
    have d38 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d39 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d40 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d41 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) + (-(a * b) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d14 d20 eq_identity_coercion eq_identity_coercion d40
    have d42 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_sub_eqs_add_neg d41 neg_identity_coercion
    have d43 : b = b := by term_derivation_reflection
    have d44 : c = c := by term_derivation_reflection
    have d45 : b * c = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d46 : b * c = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_mul_eq
    have d47 : (-(((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ))) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_neg_product
    have d48 : (-(b * c) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_neg_eq
    have d49 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_reflection
    have d50 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b + (-(b * c) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_eq d42 d48 eq_identity_coercion eq_identity_coercion d49
    have d51 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_sub_eqs_add_neg d50 neg_identity_coercion
    have d52 : c = c := by term_derivation_reflection
    have d53 : a = a := by term_derivation_reflection
    have d54 : c * a = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d55 : c * a = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d56 : (-(((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ))) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_neg_product
    have d57 : (-(c * a) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_neg_eq
    have d58 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_reflection
    have d59 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d60 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d61 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_reflection
    have d62 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d63 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d64 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d65 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_reflection
    have d66 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_sum_add_product_greater
    have d67 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c + (-(c * a) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_eq d51 d57 eq_identity_coercion eq_identity_coercion d66
    have d68 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c - c * a = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_sub_eqs_add_neg d67 neg_identity_coercion
    have d69 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d70 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d71 : b = b := by term_derivation_reflection
    have d72 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d73 : a = a := by term_derivation_reflection
    have d74 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d75 : b * a = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d76 : b ^ (1:ℕ) * a ^ (1:ℕ) = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d77 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d78 : ((-1:ℤ) : ℝ) * b ^ (1:ℕ) = ((-1:ℤ) : ℝ) * b ^ (1:ℕ) := by term_derivation_reflection
    have d79 : ((-1:ℤ) : ℝ) * b ^ (1:ℕ) * a ^ (1:ℕ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_simple_product_mul_exponential_less
    have d80 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_product
    have d81 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ))) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_product
    have d82 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d83 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_zero_add
    have d84 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d85 : c = c := by term_derivation_reflection
    have d86 : c ^ (1:ℕ) = c := by term_derivation_power_one
    have d87 : a = a := by term_derivation_reflection
    have d88 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d89 : c * a = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d90 : c ^ (1:ℕ) * a ^ (1:ℕ) = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d91 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d92 : ((-1:ℤ) : ℝ) * c ^ (1:ℕ) = ((-1:ℤ) : ℝ) * c ^ (1:ℕ) := by term_derivation_reflection
    have d93 : ((-1:ℤ) : ℝ) * c ^ (1:ℕ) * a ^ (1:ℕ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_simple_product_mul_exponential_less
    have d94 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_product
    have d95 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ))) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_product
    have d96 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d97 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_product_add_product_less
    have d98 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_add_eq d83 d96 eq_identity_coercion eq_identity_coercion d97
    have d99 : b = b := by term_derivation_reflection
    have d100 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d101 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d102 : ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_one_mul
    have d103 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d104 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_add_eq d98 d102 eq_identity_coercion eq_identity_coercion d103
    have d105 : c = c := by term_derivation_reflection
    have d106 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d107 : c ^ (2:ℕ) = ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d108 : ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_one_mul
    have d109 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_reflection
    have d110 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_add_eq d104 d108 eq_identity_coercion eq_identity_coercion d109
    have d111 : a = a := by term_derivation_reflection
    have d112 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d113 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d114 : ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_one_mul
    have d115 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d116 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d110 d114 eq_identity_coercion eq_identity_coercion d115
    have d117 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d118 : c = c := by term_derivation_reflection
    have d119 : c ^ (1:ℕ) = c := by term_derivation_power_one
    have d120 : b = b := by term_derivation_reflection
    have d121 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d122 : c * b = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d123 : c ^ (1:ℕ) * b ^ (1:ℕ) = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_mul_eq
    have d124 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d125 : ((-1:ℤ) : ℝ) * c ^ (1:ℕ) = ((-1:ℤ) : ℝ) * c ^ (1:ℕ) := by term_derivation_reflection
    have d126 : ((-1:ℤ) : ℝ) * c ^ (1:ℕ) * b ^ (1:ℕ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_simple_product_mul_exponential_less
    have d127 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_mul_product
    have d128 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ))) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_mul_product
    have d129 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_mul_eq
    have d130 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_reflection
    have d131 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_eq d116 d129 eq_identity_coercion eq_identity_coercion d130
    have d132 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d133 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_nf_add_zero
    have d134 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_eq d131 d132 eq_identity_coercion eq_int_to_real_coercion d133
    have d135 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) - ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_sub_eqs_add_neg d134 neg_nat_to_real_coercion
    have d136 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) - a * b - b * c - c * a ≥ ((0:ℕ) : ℝ) ↔ ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d137 : a = a := by term_derivation_reflection
    have d138 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d139 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d140 : b = b := by term_derivation_reflection
    have d141 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d142 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d143 : ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_product_add_product_greater
    have d144 : a ^ (2:ℕ) + b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d139 d142 eq_identity_coercion eq_identity_coercion d143
    have d145 : c = c := by term_derivation_reflection
    have d146 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d147 : c ^ (2:ℕ) = ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d148 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_reflection
    have d149 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d150 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d151 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d144 d147 eq_identity_coercion eq_identity_coercion d150
    have d152 : a = a := by term_derivation_reflection
    have d153 : b = b := by term_derivation_reflection
    have d154 : a * b = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d155 : a * b = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d156 : b = b := by term_derivation_reflection
    have d157 : c = c := by term_derivation_reflection
    have d158 : b * c = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d159 : b * c = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_mul_eq
    have d160 : ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_product_add_product_less
    have d161 : a * b + b * c = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_eq d155 d159 eq_identity_coercion eq_identity_coercion d160
    have d162 : c = c := by term_derivation_reflection
    have d163 : a = a := by term_derivation_reflection
    have d164 : c * a = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d165 : c * a = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d166 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_reflection
    have d167 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_reflection
    have d168 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_sum_add_product_greater
    have d169 : a * b + b * c + c * a = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_eq d161 d165 eq_identity_coercion eq_identity_coercion d168
    have d170 : b = b := by term_derivation_reflection
    have d171 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d172 : b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d173 : ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_one_mul
    have d174 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_zero_add
    have d175 : c = c := by term_derivation_reflection
    have d176 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d177 : c ^ (2:ℕ) = ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d178 : ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_one_mul
    have d179 : ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d180 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_add_eq d174 d178 eq_identity_coercion eq_identity_coercion d179
    have d181 : a = a := by term_derivation_reflection
    have d182 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d183 : a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_non_reduced_power
    have d184 : ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_one_mul
    have d185 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d186 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_eq d180 d184 eq_identity_coercion eq_identity_coercion d185
    have d187 : b = b := by term_derivation_reflection
    have d188 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d189 : a = a := by term_derivation_reflection
    have d190 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d191 : b * a = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d192 : b ^ (1:ℕ) * a ^ (1:ℕ) = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d193 : ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_one_mul
    have d194 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_zero_add
    have d195 : c = c := by term_derivation_reflection
    have d196 : c ^ (1:ℕ) = c := by term_derivation_power_one
    have d197 : a = a := by term_derivation_reflection
    have d198 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d199 : c * a = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d200 : c ^ (1:ℕ) * a ^ (1:ℕ) = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d201 : ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_one_mul
    have d202 : ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_product_add_product_less
    have d203 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_add_eq d194 d201 eq_identity_coercion eq_identity_coercion d202
    have d204 : c = c := by term_derivation_reflection
    have d205 : c ^ (1:ℕ) = c := by term_derivation_power_one
    have d206 : b = b := by term_derivation_reflection
    have d207 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d208 : c * b = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d209 : c ^ (1:ℕ) * b ^ (1:ℕ) = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_mul_eq
    have d210 : ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_one_mul
    have d211 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_reflection
    have d212 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_eq d203 d210 eq_identity_coercion eq_identity_coercion d211
    have d213 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d214 : (-(((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ))) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_neg_product
    have d215 : (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_neg_sum
    have d216 : (-(((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ))) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_neg_product
    have d217 : (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_neg_sum
    have d218 : (-(((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ))) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_neg_product
    have d219 : (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_neg_sum
    have d220 : (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_neg_eq
    have d221 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_nf_add_zero
    have d222 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d223 : b = b := by term_derivation_reflection
    have d224 : b ^ (1:ℕ) = b := by term_derivation_power_one
    have d225 : a = a := by term_derivation_reflection
    have d226 : a ^ (1:ℕ) = a := by term_derivation_power_one
    have d227 : b * a = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_atom_mul_atom
    have d228 : b ^ (1:ℕ) * a ^ (1:ℕ) = ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d229 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d230 : ((-1:ℤ) : ℝ) * b ^ (1:ℕ) = ((-1:ℤ) : ℝ) * b ^ (1:ℕ) := by term_derivation_reflection
    have d231 : ((-1:ℤ) : ℝ) * b ^ (1:ℕ) * a ^ (1:ℕ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_simple_product_mul_exponential_less
    have d232 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_product
    have d233 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ))) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_product
    have d234 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_mul_eq
    have d235 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_zero_add
    have d236 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_product_add_product_less
    have d237 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d238 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_reflection
    have d239 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d240 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d241 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d242 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ))) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_sum
    have d243 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) := by term_derivation_reflection
    have d244 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_reflection
    have d245 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d246 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_reflection
    have d247 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d248 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_reflection
    have d249 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_sum_add_product_greater
    have d250 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ))) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) := by term_derivation_add_sum
    have d251 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_reflection
    have d252 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ))) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_sum
    have d253 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_add_eq d186 d220 eq_identity_coercion eq_identity_coercion d252
    have d254 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) - (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ))) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) := by term_derivation_sub_eqs_add_neg d253 neg_identity_coercion
    have d255 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) ≥ a * b + b * c + c * a ↔ ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) * a ^ (1:ℕ)) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * a ^ (1:ℕ)) + ((1:ℕ) : ℝ) * b ^ (2:ℕ) + ((1:ℕ) : ℝ) * c ^ (2:ℕ) + ((1:ℕ) : ℝ) * a ^ (2:ℕ) + ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) * b ^ (1:ℕ)) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d256 : a ^ (2:ℕ) + b ^ (2:ℕ) + c ^ (2:ℕ) ≥ a * b + b * c + c * a := by term_derivation_non_trivial_finish h5 d136 d255
    assumption
  obvious

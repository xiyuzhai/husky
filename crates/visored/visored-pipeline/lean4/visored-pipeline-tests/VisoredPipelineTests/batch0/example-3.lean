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

def h (a b c : ℝ) : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) ≥ a * b + b * c + c * a := by
  first
  | have h1 : ((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) = ((a - b : ℝ) ^ (2:ℕ) : ℝ) + ((b - c : ℝ) ^ (2:ℕ) : ℝ) + ((c - a : ℝ) ^ (2:ℕ) : ℝ) := by calc
    ((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) = ((((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) - ((2:ℕ) : ℝ) * a * b : ℝ) - ((2:ℕ) : ℝ) * b * c : ℝ) - ((2:ℕ) : ℝ) * c * a : ℝ := by obvious
    _ = ((a ^ (2:ℕ) : ℝ) - ((2:ℕ) : ℝ) * a * b : ℝ) + (b ^ (2:ℕ) : ℝ) + (((b ^ (2:ℕ) : ℝ) - ((2:ℕ) : ℝ) * b * c : ℝ) + (c ^ (2:ℕ) : ℝ)) + (((c ^ (2:ℕ) : ℝ) - ((2:ℕ) : ℝ) * c * a : ℝ) + (a ^ (2:ℕ) : ℝ)) := by obvious
    _ = ((a - b : ℝ) ^ (2:ℕ) : ℝ) + ((b - c : ℝ) ^ (2:ℕ) : ℝ) + ((c - a : ℝ) ^ (2:ℕ) : ℝ) := by obvious
  | have h2 : ((a - b : ℝ) ^ (2:ℕ) : ℝ) + ((b - c : ℝ) ^ (2:ℕ) : ℝ) + ((c - a : ℝ) ^ (2:ℕ) : ℝ) = ((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) := by calc
    ((a - b : ℝ) ^ (2:ℕ) : ℝ) + ((b - c : ℝ) ^ (2:ℕ) : ℝ) + ((c - a : ℝ) ^ (2:ℕ) : ℝ) = ((a ^ (2:ℕ) : ℝ) - ((2:ℕ) : ℝ) * a * b : ℝ) + (b ^ (2:ℕ) : ℝ) + (((b ^ (2:ℕ) : ℝ) - ((2:ℕ) : ℝ) * b * c : ℝ) + (c ^ (2:ℕ) : ℝ)) + (((c ^ (2:ℕ) : ℝ) - ((2:ℕ) : ℝ) * c * a : ℝ) + (a ^ (2:ℕ) : ℝ)) := by obvious
    _ = ((((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) - ((2:ℕ) : ℝ) * a * b : ℝ) - ((2:ℕ) : ℝ) * b * c : ℝ) - ((2:ℕ) : ℝ) * c * a : ℝ := by obvious
    _ = ((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) := by obvious
  have h3 : ((a - b : ℝ) ^ (2:ℕ) : ℝ) + ((b - c : ℝ) ^ (2:ℕ) : ℝ) + ((c - a : ℝ) ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by obvious
  have h4 : ((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) ≥ ((0:ℕ) : ℝ) := by obvious
  have h5 : ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : a = a := by term_derivation_reflection
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d4 : b = b := by term_derivation_reflection
    have d5 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d6 : (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d7 : ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_greater
    have d8 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d3 d6 eq_identity_coercion eq_identity_coercion d7
    have d9 : c = c := by term_derivation_reflection
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d12 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d13 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d14 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d15 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d8 d11 eq_identity_coercion eq_identity_coercion d14
    have d16 : a = a := by term_derivation_reflection
    have d17 : b = b := by term_derivation_reflection
    have d18 : a * b = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d19 : a * b = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d16 d17 d18 eq_identity_coercion eq_identity_coercion
    have d20 : (-(((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d21 : (-(a * b) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d22 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d23 : b = b := by term_derivation_reflection
    have d24 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d25 : a = a := by term_derivation_reflection
    have d26 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d27 : b * a = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d28 : (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d24 d26 d27 eq_identity_coercion eq_identity_coercion
    have d29 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d30 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d31 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d32 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d30 d31 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d33 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d29 d32 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d22 d28 d33 eq_int_to_real_coercion eq_identity_coercion
    have d35 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_zero_add
    have d36 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_less
    have d37 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d38 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d39 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d40 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d41 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d42 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) + (-(a * b) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d15 d21 eq_identity_coercion eq_identity_coercion d41
    have d43 : ((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sub_eqs_add_neg d42 neg_identity_coercion
    have d44 : b = b := by term_derivation_reflection
    have d45 : c = c := by term_derivation_reflection
    have d46 : b * c = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d47 : b * c = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d44 d45 d46 eq_identity_coercion eq_identity_coercion
    have d48 : (-(((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d49 : (-(b * c) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d50 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d51 : ((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) + (-(b * c) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d43 d49 eq_identity_coercion eq_identity_coercion d50
    have d52 : (((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d51 neg_identity_coercion
    have d53 : c = c := by term_derivation_reflection
    have d54 : a = a := by term_derivation_reflection
    have d55 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d56 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d53 d54 d55 eq_identity_coercion eq_identity_coercion
    have d57 : (-(((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d58 : (-(c * a) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d59 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d60 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d61 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d62 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d63 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d64 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d65 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d66 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d67 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sum_add_product_greater
    have d68 : (((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) + (-(c * a) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d52 d58 eq_identity_coercion eq_identity_coercion d67
    have d69 : ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d68 neg_identity_coercion
    have d70 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) = ((2:ℕ) : ℝ) * ((((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d71 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ)) = ((2:ℕ) : ℝ) * ((((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ)) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d72 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ)) = ((2:ℕ) : ℝ) * ((((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ)) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d73 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ)) = ((2:ℕ) : ℝ) * ((((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ)) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d74 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((2:ℕ) : ℝ) * ((((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d75 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((2:ℕ) : ℝ) * ((((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d76 : (2:ℕ) * (0:ℕ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d77 : ((2:ℕ) : ℤ) * (-1:ℤ) = (-2:ℤ) := by term_derivation_literal_mul_literal
    have d78 : ((-2:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-2:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d79 : ((-2:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d80 : ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d78 d79 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d81 : ((2:ℕ) : ℝ) * (((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d77 d80 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d82 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d83 : b = b := by term_derivation_reflection
    have d84 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d85 : a = a := by term_derivation_reflection
    have d86 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d87 : b * a = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d88 : (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d84 d86 d87 eq_identity_coercion eq_identity_coercion
    have d89 : (-2:ℤ) * ((1:ℕ) : ℤ) = (-2:ℤ) := by term_derivation_mul_one
    have d90 : ((-2:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-2:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d91 : ((-2:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d92 : ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d90 d91 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d93 : ((-2:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d89 d92 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d94 : ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d82 d88 d93 eq_int_to_real_coercion eq_identity_coercion
    have d95 : ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_zero_add
    have d96 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_literal_mul_sum
    have d97 : ((2:ℕ) : ℤ) * (-1:ℤ) = (-2:ℤ) := by term_derivation_literal_mul_literal
    have d98 : ((-2:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) = ((-2:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d99 : ((-2:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d100 : ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d98 d99 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d101 : ((2:ℕ) : ℝ) * (((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d97 d100 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d102 : ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_product_add_product_less
    have d103 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_literal_mul_sum
    have d104 : (2:ℕ) * (1:ℕ) = (2:ℕ) := by term_derivation_mul_one
    have d105 : ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d106 : ((2:ℕ) : ℝ) * (((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ)) = ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_mul_product d104 d105 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d107 : ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d108 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_literal_mul_sum
    have d109 : (2:ℕ) * (1:ℕ) = (2:ℕ) := by term_derivation_mul_one
    have d110 : ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d111 : ((2:ℕ) : ℝ) * (((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ)) = ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_mul_product d109 d110 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d112 : ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d113 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_literal_mul_sum
    have d114 : (2:ℕ) * (1:ℕ) = (2:ℕ) := by term_derivation_mul_one
    have d115 : ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d116 : ((2:ℕ) : ℝ) * (((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ)) = ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_mul_product d114 d115 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d117 : ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d118 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_literal_mul_sum
    have d119 : ((2:ℕ) : ℤ) * (-1:ℤ) = (-2:ℤ) := by term_derivation_literal_mul_literal
    have d120 : ((-2:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) = ((-2:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d121 : ((-2:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d122 : ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d120 d121 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d123 : ((2:ℕ) : ℝ) * (((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) = ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d119 d122 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d124 : ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d125 : ((2:ℕ) : ℝ) * (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_literal_mul_sum
    have d126 : ((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d d69 d125 eq_nat_to_real_coercion eq_identity_coercion
    have d127 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d128 : ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_nf_add_zero
    have d129 : ((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d126 d127 eq_identity_coercion eq_int_to_real_coercion d128
    have d130 : (((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d129 neg_nat_to_real_coercion
    have d131 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d132 : (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) * (((1:ℚ)/2:ℚ) : ℝ) = (((1:ℚ)/2:ℚ) : ℝ) * ((((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) ^ (1:ℕ) : ℝ) := by term_derivation_base_mul_literal
    have d133 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ)) = (((1:ℚ)/2:ℚ) : ℝ) * ((((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ)) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d134 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ)) = (((1:ℚ)/2:ℚ) : ℝ) * ((((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ)) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d135 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ)) = (((1:ℚ)/2:ℚ) : ℝ) * ((((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ)) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d136 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = (((1:ℚ)/2:ℚ) : ℝ) * ((((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d137 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = (((1:ℚ)/2:ℚ) : ℝ) * ((((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) ^ (1:ℕ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d138 : ((1:ℚ)/2:ℚ) * ((0:ℕ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d139 : ((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d140 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d141 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d142 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d140 d141 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d143 : (((1:ℚ)/2:ℚ) : ℝ) * (((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d139 d142 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d144 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d145 : b = b := by term_derivation_reflection
    have d146 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d147 : a = a := by term_derivation_reflection
    have d148 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d149 : b * a = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d150 : (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d146 d148 d149 eq_identity_coercion eq_identity_coercion
    have d151 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d152 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d153 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d154 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d152 d153 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d155 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d151 d154 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d156 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d144 d150 d155 eq_int_to_real_coercion eq_identity_coercion
    have d157 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_zero_add
    have d158 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_literal_mul_sum
    have d159 : ((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d160 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d161 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d162 : ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d160 d161 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d163 : (((1:ℚ)/2:ℚ) : ℝ) * (((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d159 d162 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d164 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_product_add_product_less
    have d165 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_literal_mul_sum
    have d166 : ((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d167 : ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d168 : (((1:ℚ)/2:ℚ) : ℝ) * (((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ)) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_mul_product d166 d167 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d169 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d170 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_literal_mul_sum
    have d171 : ((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d172 : ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d173 : (((1:ℚ)/2:ℚ) : ℝ) * (((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ)) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_mul_product d171 d172 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d174 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d175 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_literal_mul_sum
    have d176 : ((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d177 : ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d178 : (((1:ℚ)/2:ℚ) : ℝ) * (((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ)) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_mul_product d176 d177 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d179 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d180 : (((1:ℚ)/2:ℚ) : ℝ) * (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_literal_mul_sum
    have d181 : ((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d182 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d183 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d184 : ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d182 d183 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d185 : (((1:ℚ)/2:ℚ) : ℝ) * (((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d181 d184 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d186 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d187 : (((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) * (((1:ℚ)/2:ℚ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_literal_mul_sum
    have d188 : ((((0:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((2:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-2:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) / ((2:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_div_literal
    have d189 : ((((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_div_eq d130 d131 eq_identity_coercion eq_nat_to_real_coercion d188
    have d190 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d191 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_nf_add_zero
    have d192 : ((((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d189 d190 eq_identity_coercion eq_int_to_real_coercion d191
    have d193 : (((((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d192 neg_nat_to_real_coercion
    have d194 : a = a := by term_derivation_reflection
    have d195 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d196 : (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d197 : b = b := by term_derivation_reflection
    have d198 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d199 : (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d200 : ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_greater
    have d201 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d196 d199 eq_identity_coercion eq_identity_coercion d200
    have d202 : c = c := by term_derivation_reflection
    have d203 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d204 : (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d205 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d206 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d207 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d208 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d201 d204 eq_identity_coercion eq_identity_coercion d207
    have d209 : a = a := by term_derivation_reflection
    have d210 : b = b := by term_derivation_reflection
    have d211 : a * b = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d212 : a * b = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d209 d210 d211 eq_identity_coercion eq_identity_coercion
    have d213 : (-(((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d214 : (-(a * b) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d215 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d216 : b = b := by term_derivation_reflection
    have d217 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d218 : a = a := by term_derivation_reflection
    have d219 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d220 : b * a = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d221 : (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d217 d219 d220 eq_identity_coercion eq_identity_coercion
    have d222 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d223 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d224 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d225 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d223 d224 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d226 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d222 d225 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d227 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d215 d221 d226 eq_int_to_real_coercion eq_identity_coercion
    have d228 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_zero_add
    have d229 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_less
    have d230 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d231 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d232 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d233 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d234 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d235 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) + (-(a * b) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d208 d214 eq_identity_coercion eq_identity_coercion d234
    have d236 : ((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sub_eqs_add_neg d235 neg_identity_coercion
    have d237 : b = b := by term_derivation_reflection
    have d238 : c = c := by term_derivation_reflection
    have d239 : b * c = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d240 : b * c = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d237 d238 d239 eq_identity_coercion eq_identity_coercion
    have d241 : (-(((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d242 : (-(b * c) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d243 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d244 : ((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) + (-(b * c) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d236 d242 eq_identity_coercion eq_identity_coercion d243
    have d245 : (((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d244 neg_identity_coercion
    have d246 : c = c := by term_derivation_reflection
    have d247 : a = a := by term_derivation_reflection
    have d248 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d249 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d246 d247 d248 eq_identity_coercion eq_identity_coercion
    have d250 : (-(((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d251 : (-(c * a) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d252 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d253 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d254 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d255 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d256 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d257 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d258 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d259 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d260 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sum_add_product_greater
    have d261 : (((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) + (-(c * a) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d245 d251 eq_identity_coercion eq_identity_coercion d260
    have d262 : ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d261 neg_identity_coercion
    have d263 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d264 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_nf_add_zero
    have d265 : ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d262 d263 eq_identity_coercion eq_int_to_real_coercion d264
    have d266 : (((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d265 neg_nat_to_real_coercion
    have d267 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d268 : (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) * ((1:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_one
    have d269 : ((((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) / ((1:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_div_literal
    have d270 : ((((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_div_eq d266 d267 eq_identity_coercion eq_nat_to_real_coercion d269
    have d271 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d272 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_nf_add_zero
    have d273 : ((((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d270 d271 eq_identity_coercion eq_int_to_real_coercion d272
    have d274 : (((((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d273 neg_nat_to_real_coercion
    have d275 : (((((2:ℕ) : ℝ) * ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d193 d274
    have d276 : ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  have h6 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) ≥ a * b + b * c + c * a := by
    have d277 : a = a := by term_derivation_reflection
    have d278 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d279 : (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d280 : b = b := by term_derivation_reflection
    have d281 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d282 : (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d283 : ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_greater
    have d284 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d279 d282 eq_identity_coercion eq_identity_coercion d283
    have d285 : c = c := by term_derivation_reflection
    have d286 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d287 : (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d288 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d289 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d290 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d291 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d284 d287 eq_identity_coercion eq_identity_coercion d290
    have d292 : a = a := by term_derivation_reflection
    have d293 : b = b := by term_derivation_reflection
    have d294 : a * b = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d295 : a * b = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d292 d293 d294 eq_identity_coercion eq_identity_coercion
    have d296 : (-(((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d297 : (-(a * b) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d298 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d299 : b = b := by term_derivation_reflection
    have d300 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d301 : a = a := by term_derivation_reflection
    have d302 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d303 : b * a = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d304 : (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d300 d302 d303 eq_identity_coercion eq_identity_coercion
    have d305 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d306 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d307 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d308 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d306 d307 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d309 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d305 d308 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d310 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d298 d304 d309 eq_int_to_real_coercion eq_identity_coercion
    have d311 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_zero_add
    have d312 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_less
    have d313 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d314 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d315 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d316 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d317 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d318 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) + (-(a * b) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d291 d297 eq_identity_coercion eq_identity_coercion d317
    have d319 : ((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sub_eqs_add_neg d318 neg_identity_coercion
    have d320 : b = b := by term_derivation_reflection
    have d321 : c = c := by term_derivation_reflection
    have d322 : b * c = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d323 : b * c = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d320 d321 d322 eq_identity_coercion eq_identity_coercion
    have d324 : (-(((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d325 : (-(b * c) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d326 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d327 : ((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) + (-(b * c) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d319 d325 eq_identity_coercion eq_identity_coercion d326
    have d328 : (((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d327 neg_identity_coercion
    have d329 : c = c := by term_derivation_reflection
    have d330 : a = a := by term_derivation_reflection
    have d331 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d332 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d329 d330 d331 eq_identity_coercion eq_identity_coercion
    have d333 : (-(((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d334 : (-(c * a) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d335 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d336 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d337 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d338 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d339 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d340 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d341 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d342 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d343 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sum_add_product_greater
    have d344 : (((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) + (-(c * a) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d328 d334 eq_identity_coercion eq_identity_coercion d343
    have d345 : ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d344 neg_identity_coercion
    have d346 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d347 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d348 : b = b := by term_derivation_reflection
    have d349 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d350 : a = a := by term_derivation_reflection
    have d351 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d352 : b * a = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d353 : (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d349 d351 d352 eq_identity_coercion eq_identity_coercion
    have d354 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d355 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d356 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d357 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d355 d356 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d358 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d354 d357 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d359 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d347 d353 d358 eq_int_to_real_coercion eq_identity_coercion
    have d360 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_zero_add
    have d361 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d362 : c = c := by term_derivation_reflection
    have d363 : (c ^ (1:ℕ) : ℝ) = c := by term_derivation_power_one
    have d364 : a = a := by term_derivation_reflection
    have d365 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d366 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d367 : (c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d363 d365 d366 eq_identity_coercion eq_identity_coercion
    have d368 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d369 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d370 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d371 : ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d369 d370 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d372 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d368 d371 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d373 : ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d361 d367 d372 eq_int_to_real_coercion eq_identity_coercion
    have d374 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_product_add_product_less
    have d375 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d360 d373 eq_identity_coercion eq_identity_coercion d374
    have d376 : b = b := by term_derivation_reflection
    have d377 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d378 : (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d379 : ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_one_mul
    have d380 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d381 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d375 d379 eq_identity_coercion eq_identity_coercion d380
    have d382 : c = c := by term_derivation_reflection
    have d383 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d384 : (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d385 : ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_one_mul
    have d386 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d387 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d381 d385 eq_identity_coercion eq_identity_coercion d386
    have d388 : a = a := by term_derivation_reflection
    have d389 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d390 : (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d391 : ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_one_mul
    have d392 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d393 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d387 d391 eq_identity_coercion eq_identity_coercion d392
    have d394 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d395 : c = c := by term_derivation_reflection
    have d396 : (c ^ (1:ℕ) : ℝ) = c := by term_derivation_power_one
    have d397 : b = b := by term_derivation_reflection
    have d398 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d399 : c * b = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d400 : (c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d396 d398 d399 eq_identity_coercion eq_identity_coercion
    have d401 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d402 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d403 : ((-1:ℤ) : ℝ) * (c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d404 : ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d402 d403 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d405 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d401 d404 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d406 : ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d394 d400 d405 eq_int_to_real_coercion eq_identity_coercion
    have d407 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d408 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d393 d406 eq_identity_coercion eq_identity_coercion d407
    have d409 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d410 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_nf_add_zero
    have d411 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d408 d409 eq_identity_coercion eq_int_to_real_coercion d410
    have d412 : (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) - ((0:ℕ) : ℝ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d411 neg_nat_to_real_coercion
    have d413 : ((((a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) - a * b : ℝ) - b * c : ℝ) - c * a : ℝ) ≥ ((0:ℕ) : ℝ) ↔ ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d414 : a = a := by term_derivation_reflection
    have d415 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d416 : (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d417 : b = b := by term_derivation_reflection
    have d418 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d419 : (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d420 : ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_greater
    have d421 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d416 d419 eq_identity_coercion eq_identity_coercion d420
    have d422 : c = c := by term_derivation_reflection
    have d423 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d424 : (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d425 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d426 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d427 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d428 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d421 d424 eq_identity_coercion eq_identity_coercion d427
    have d429 : a = a := by term_derivation_reflection
    have d430 : b = b := by term_derivation_reflection
    have d431 : a * b = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d432 : a * b = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d429 d430 d431 eq_identity_coercion eq_identity_coercion
    have d433 : b = b := by term_derivation_reflection
    have d434 : c = c := by term_derivation_reflection
    have d435 : b * c = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d436 : b * c = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d433 d434 d435 eq_identity_coercion eq_identity_coercion
    have d437 : ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_product_add_product_less
    have d438 : a * b + b * c = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d432 d436 eq_identity_coercion eq_identity_coercion d437
    have d439 : c = c := by term_derivation_reflection
    have d440 : a = a := by term_derivation_reflection
    have d441 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d442 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d439 d440 d441 eq_identity_coercion eq_identity_coercion
    have d443 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d444 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d445 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sum_add_product_greater
    have d446 : a * b + b * c + c * a = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d438 d442 eq_identity_coercion eq_identity_coercion d445
    have d447 : b = b := by term_derivation_reflection
    have d448 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d449 : (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d450 : ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_one_mul
    have d451 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_zero_add
    have d452 : c = c := by term_derivation_reflection
    have d453 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d454 : (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d455 : ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_one_mul
    have d456 : ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_less
    have d457 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d451 d455 eq_identity_coercion eq_identity_coercion d456
    have d458 : a = a := by term_derivation_reflection
    have d459 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d460 : (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_non_reduced_power
    have d461 : ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_one_mul
    have d462 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d463 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_eq d457 d461 eq_identity_coercion eq_identity_coercion d462
    have d464 : b = b := by term_derivation_reflection
    have d465 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d466 : a = a := by term_derivation_reflection
    have d467 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d468 : b * a = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d469 : (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d465 d467 d468 eq_identity_coercion eq_identity_coercion
    have d470 : ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_one_mul
    have d471 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_zero_add
    have d472 : c = c := by term_derivation_reflection
    have d473 : (c ^ (1:ℕ) : ℝ) = c := by term_derivation_power_one
    have d474 : a = a := by term_derivation_reflection
    have d475 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d476 : c * a = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d477 : (c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d473 d475 d476 eq_identity_coercion eq_identity_coercion
    have d478 : ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_one_mul
    have d479 : ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_product_add_product_less
    have d480 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d471 d478 eq_identity_coercion eq_identity_coercion d479
    have d481 : c = c := by term_derivation_reflection
    have d482 : (c ^ (1:ℕ) : ℝ) = c := by term_derivation_power_one
    have d483 : b = b := by term_derivation_reflection
    have d484 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d485 : c * b = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d486 : (c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d482 d484 d485 eq_identity_coercion eq_identity_coercion
    have d487 : ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_one_mul
    have d488 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d489 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d480 d487 eq_identity_coercion eq_identity_coercion d488
    have d490 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d491 : (-(((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d492 : (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_sum
    have d493 : (-(((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d494 : (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_neg_sum
    have d495 : (-(((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) : ℝ) = ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_product
    have d496 : (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_sum
    have d497 : (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_neg_eq
    have d498 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((0:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_nf_add_zero
    have d499 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d500 : b = b := by term_derivation_reflection
    have d501 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d502 : a = a := by term_derivation_reflection
    have d503 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d504 : b * a = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_atom_mul_atom
    have d505 : (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d501 d503 d504 eq_identity_coercion eq_identity_coercion
    have d506 : (-1:ℤ) * ((1:ℕ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d507 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) := by term_derivation_reflection
    have d508 : ((-1:ℤ) : ℝ) * (b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_simple_product_mul_exponential_less
    have d509 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d507 d508 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d510 : ((-1:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_product d506 d509 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d511 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_mul_eq d499 d505 d510 eq_int_to_real_coercion eq_identity_coercion
    have d512 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_zero_add
    have d513 : ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_product_add_product_less
    have d514 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d515 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d516 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d517 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d518 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d519 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_sum
    have d520 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d521 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d522 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d523 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d524 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d525 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_reflection
    have d526 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_sum_add_product_greater
    have d527 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ))) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) := by term_derivation_add_sum
    have d528 : ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_reflection
    have d529 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + (((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_sum
    have d530 : ((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + (-(((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_add_eq d463 d497 eq_identity_coercion eq_identity_coercion d529
    have d531 : (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) - (((0:ℕ) : ℝ) + ((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ))) : ℝ) = ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) := by term_derivation_sub_eqs_add_neg d530 neg_identity_coercion
    have d532 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) ≥ a * b + b * c + c * a ↔ ((0:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (a ^ (1:ℕ) : ℝ)) + ((1:ℕ) : ℝ) * (b ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (c ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) * (a ^ (2:ℕ) : ℝ) + ((-1:ℤ) : ℝ) * ((c ^ (1:ℕ) : ℝ) * (b ^ (1:ℕ) : ℝ)) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d533 : (a ^ (2:ℕ) : ℝ) + (b ^ (2:ℕ) : ℝ) + (c ^ (2:ℕ) : ℝ) ≥ a * b + b * c + c * a := by term_derivation_non_trivial_hypothesis_equivalence h5 d413 d532
    assumption
  obvious

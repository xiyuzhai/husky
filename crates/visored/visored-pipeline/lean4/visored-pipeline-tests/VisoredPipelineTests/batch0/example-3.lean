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

macro "term_derivation_variable": tactic =>`(tactic|
  first
  | rfl; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_literal": tactic =>`(tactic|
  first
  | rfl; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_item_path": tactic =>`(tactic|
  first
  | rfl; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_sum": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_sub": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_product": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_div": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | field_simp; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_finalize" d1:term:1024 d2:term:1024 : tactic =>`(tactic|
  (apply (Iff.mpr $d2); apply (Iff.mp $d1); assumption)
)

macro "term_derivation_chaining_separated_list": tactic =>`(tactic|
  first
  | ring; done
  | (constructor; repeat (intro h; linarith))
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_square": tactic =>`(tactic|
  first
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_power": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

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
    have d : a = a := term_derivation_reflection
    have d1 : 2 = 2 := term_derivation_reflection
    have d2 : a ^ 2 = (1 : ℝ) * a ^ 2 := term_derivation_non_reduced_power
    have d3 : b = b := term_derivation_reflection
    have d4 : 2 = 2 := term_derivation_reflection
    have d5 : b ^ 2 = (1 : ℝ) * b ^ 2 := term_derivation_non_reduced_power
    have d6 : (1 : ℝ) * a ^ 2 + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_product_add_product_greater
    have d7 : a ^ 2 + b ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_eq
    have d8 : c = c := term_derivation_reflection
    have d9 : 2 = 2 := term_derivation_reflection
    have d10 : c ^ 2 = (1 : ℝ) * c ^ 2 := term_derivation_non_reduced_power
    have d11 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_reflection
    have d12 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_reflection
    have d13 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_sum_add_product_greater
    have d14 : a ^ 2 + b ^ 2 + c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_eq
    have d15 : a = a := term_derivation_reflection
    have d16 : b = b := term_derivation_reflection
    have d17 : a * b = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_greater
    have d18 : a * b = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d19 : -((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_neg_product
    have d20 : -(a * b) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_neg_eq
    have d21 : -1 = -1 := term_derivation_reflection
    have d22 : b = b := term_derivation_reflection
    have d23 : b ^ 1 = b := term_derivation_power_one
    have d24 : a = a := term_derivation_reflection
    have d25 : a ^ 1 = a := term_derivation_power_one
    have d26 : b * a = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_less
    have d27 : b ^ 1 * a ^ 1 = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d28 : (-1 : ℤ) * (1 : ℤ) = -1 := term_derivation_literal_mul
    have d29 : (-1 : ℝ) * b ^ 1 = (-1 : ℝ) * b ^ 1 := term_derivation_reflection
    have d30 : (-1 : ℝ) * b ^ 1 * a ^ 1 = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_simple_product_mul_exponential_less
    have d31 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_product
    have d32 : (-1 : ℝ) * ((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_product
    have d33 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d34 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_zero_add
    have d35 : (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_product_add_product_less
    have d36 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_sum_add_product_greater
    have d37 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_reflection
    have d38 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_sum_add_product_greater
    have d39 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_reflection
    have d40 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_sum_add_product_greater
    have d41 : a ^ 2 + b ^ 2 + c ^ 2 + (-(a * b) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_eq
    have d42 : a ^ 2 + b ^ 2 + c ^ 2 - a * b = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_literal_add_literal
    have d43 : b = b := term_derivation_reflection
    have d44 : c = c := term_derivation_reflection
    have d45 : b * c = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_atom_mul_atom_greater
    have d46 : b * c = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_mul_eq
    have d47 : -((1 : ℝ) * (c ^ 1 * b ^ 1)) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_neg_product
    have d48 : -(b * c) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_neg_eq
    have d49 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_reflection
    have d50 : a ^ 2 + b ^ 2 + c ^ 2 - a * b + (-(b * c) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_eq
    have d51 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_literal_add_literal
    have d52 : c = c := term_derivation_reflection
    have d53 : a = a := term_derivation_reflection
    have d54 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_less
    have d55 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d56 : -((1 : ℝ) * (c ^ 1 * a ^ 1)) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_neg_product
    have d57 : -(c * a) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_neg_eq
    have d58 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_reflection
    have d59 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_reflection
    have d60 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_sum_add_product_greater
    have d61 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_reflection
    have d62 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_sum_add_product_greater
    have d63 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_reflection
    have d64 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_sum_add_product_greater
    have d65 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_reflection
    have d66 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_sum_add_product_greater
    have d67 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c + (-(c * a) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_eq
    have d68 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_literal_add_literal
    have d69 : 0 = 0 := term_derivation_reflection
    have d70 : -1 = -1 := term_derivation_reflection
    have d71 : b = b := term_derivation_reflection
    have d72 : b ^ 1 = b := term_derivation_power_one
    have d73 : a = a := term_derivation_reflection
    have d74 : a ^ 1 = a := term_derivation_power_one
    have d75 : b * a = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_less
    have d76 : b ^ 1 * a ^ 1 = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d77 : (-1 : ℤ) * (1 : ℤ) = -1 := term_derivation_literal_mul
    have d78 : (-1 : ℝ) * b ^ 1 = (-1 : ℝ) * b ^ 1 := term_derivation_reflection
    have d79 : (-1 : ℝ) * b ^ 1 * a ^ 1 = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_simple_product_mul_exponential_less
    have d80 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_product
    have d81 : (-1 : ℝ) * ((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_product
    have d82 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d83 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_zero_add
    have d84 : -1 = -1 := term_derivation_reflection
    have d85 : c = c := term_derivation_reflection
    have d86 : c ^ 1 = c := term_derivation_power_one
    have d87 : a = a := term_derivation_reflection
    have d88 : a ^ 1 = a := term_derivation_power_one
    have d89 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_less
    have d90 : c ^ 1 * a ^ 1 = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d91 : (-1 : ℤ) * (1 : ℤ) = -1 := term_derivation_literal_mul
    have d92 : (-1 : ℝ) * c ^ 1 = (-1 : ℝ) * c ^ 1 := term_derivation_reflection
    have d93 : (-1 : ℝ) * c ^ 1 * a ^ 1 = (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_simple_product_mul_exponential_less
    have d94 : (-1 : ℝ) * (c ^ 1 * a ^ 1) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_mul_product
    have d95 : (-1 : ℝ) * ((1 : ℝ) * (c ^ 1 * a ^ 1)) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_mul_product
    have d96 : (-1 : ℝ) * (c ^ 1 * a ^ 1) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d97 : (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_product_add_product_less
    have d98 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_add_eq
    have d99 : b = b := term_derivation_reflection
    have d100 : 2 = 2 := term_derivation_reflection
    have d101 : b ^ 2 = (1 : ℝ) * b ^ 2 := term_derivation_non_reduced_power
    have d102 : (1 : ℝ) * b ^ 2 = (1 : ℝ) * b ^ 2 := term_derivation_one_mul
    have d103 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_reflection
    have d104 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_add_eq
    have d105 : c = c := term_derivation_reflection
    have d106 : 2 = 2 := term_derivation_reflection
    have d107 : c ^ 2 = (1 : ℝ) * c ^ 2 := term_derivation_non_reduced_power
    have d108 : (1 : ℝ) * c ^ 2 = (1 : ℝ) * c ^ 2 := term_derivation_one_mul
    have d109 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_reflection
    have d110 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_add_eq
    have d111 : a = a := term_derivation_reflection
    have d112 : 2 = 2 := term_derivation_reflection
    have d113 : a ^ 2 = (1 : ℝ) * a ^ 2 := term_derivation_non_reduced_power
    have d114 : (1 : ℝ) * a ^ 2 = (1 : ℝ) * a ^ 2 := term_derivation_one_mul
    have d115 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_reflection
    have d116 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_eq
    have d117 : -1 = -1 := term_derivation_reflection
    have d118 : c = c := term_derivation_reflection
    have d119 : c ^ 1 = c := term_derivation_power_one
    have d120 : b = b := term_derivation_reflection
    have d121 : b ^ 1 = b := term_derivation_power_one
    have d122 : c * b = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_atom_mul_atom_less
    have d123 : c ^ 1 * b ^ 1 = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_mul_eq
    have d124 : (-1 : ℤ) * (1 : ℤ) = -1 := term_derivation_literal_mul
    have d125 : (-1 : ℝ) * c ^ 1 = (-1 : ℝ) * c ^ 1 := term_derivation_reflection
    have d126 : (-1 : ℝ) * c ^ 1 * b ^ 1 = (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_simple_product_mul_exponential_less
    have d127 : (-1 : ℝ) * (c ^ 1 * b ^ 1) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_mul_product
    have d128 : (-1 : ℝ) * ((1 : ℝ) * (c ^ 1 * b ^ 1)) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_mul_product
    have d129 : (-1 : ℝ) * (c ^ 1 * b ^ 1) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_mul_eq
    have d130 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_reflection
    have d131 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_eq
    have d132 : -(0 : ℤ) = 0 := term_derivation_neg_literal
    have d133 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) + (0 : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_nf_add_zero
    have d134 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) + (-(0 : ℤ) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_eq
    have d135 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) - (0 : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_literal_add_literal
    have d136 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a ≥ (0 : ℝ) ↔ (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) ≥ (0 : ℝ) := term_derivation_num_comparison
    have d137 : a = a := term_derivation_reflection
    have d138 : 2 = 2 := term_derivation_reflection
    have d139 : a ^ 2 = (1 : ℝ) * a ^ 2 := term_derivation_non_reduced_power
    have d140 : b = b := term_derivation_reflection
    have d141 : 2 = 2 := term_derivation_reflection
    have d142 : b ^ 2 = (1 : ℝ) * b ^ 2 := term_derivation_non_reduced_power
    have d143 : (1 : ℝ) * a ^ 2 + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_product_add_product_greater
    have d144 : a ^ 2 + b ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_eq
    have d145 : c = c := term_derivation_reflection
    have d146 : 2 = 2 := term_derivation_reflection
    have d147 : c ^ 2 = (1 : ℝ) * c ^ 2 := term_derivation_non_reduced_power
    have d148 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_reflection
    have d149 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_reflection
    have d150 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * a ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_sum_add_product_greater
    have d151 : a ^ 2 + b ^ 2 + c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_eq
    have d152 : a = a := term_derivation_reflection
    have d153 : b = b := term_derivation_reflection
    have d154 : a * b = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_greater
    have d155 : a * b = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d156 : b = b := term_derivation_reflection
    have d157 : c = c := term_derivation_reflection
    have d158 : b * c = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_atom_mul_atom_greater
    have d159 : b * c = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_mul_eq
    have d160 : (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_product_add_product_less
    have d161 : a * b + b * c = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_eq
    have d162 : c = c := term_derivation_reflection
    have d163 : a = a := term_derivation_reflection
    have d164 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_less
    have d165 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d166 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_reflection
    have d167 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_reflection
    have d168 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_sum_add_product_greater
    have d169 : a * b + b * c + c * a = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_eq
    have d170 : b = b := term_derivation_reflection
    have d171 : 2 = 2 := term_derivation_reflection
    have d172 : b ^ 2 = (1 : ℝ) * b ^ 2 := term_derivation_non_reduced_power
    have d173 : (1 : ℝ) * b ^ 2 = (1 : ℝ) * b ^ 2 := term_derivation_one_mul
    have d174 : (0 : ℝ) + (1 : ℝ) * b ^ 2 = (1 : ℝ) * b ^ 2 := term_derivation_zero_add
    have d175 : c = c := term_derivation_reflection
    have d176 : 2 = 2 := term_derivation_reflection
    have d177 : c ^ 2 = (1 : ℝ) * c ^ 2 := term_derivation_non_reduced_power
    have d178 : (1 : ℝ) * c ^ 2 = (1 : ℝ) * c ^ 2 := term_derivation_one_mul
    have d179 : (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_product_add_product_less
    have d180 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_add_eq
    have d181 : a = a := term_derivation_reflection
    have d182 : 2 = 2 := term_derivation_reflection
    have d183 : a ^ 2 = (1 : ℝ) * a ^ 2 := term_derivation_non_reduced_power
    have d184 : (1 : ℝ) * a ^ 2 = (1 : ℝ) * a ^ 2 := term_derivation_one_mul
    have d185 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_reflection
    have d186 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_eq
    have d187 : b = b := term_derivation_reflection
    have d188 : b ^ 1 = b := term_derivation_power_one
    have d189 : a = a := term_derivation_reflection
    have d190 : a ^ 1 = a := term_derivation_power_one
    have d191 : b * a = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_less
    have d192 : b ^ 1 * a ^ 1 = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d193 : (1 : ℝ) * (b ^ 1 * a ^ 1) = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_one_mul
    have d194 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_zero_add
    have d195 : c = c := term_derivation_reflection
    have d196 : c ^ 1 = c := term_derivation_power_one
    have d197 : a = a := term_derivation_reflection
    have d198 : a ^ 1 = a := term_derivation_power_one
    have d199 : c * a = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_less
    have d200 : c ^ 1 * a ^ 1 = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d201 : (1 : ℝ) * (c ^ 1 * a ^ 1) = (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_one_mul
    have d202 : (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_product_add_product_less
    have d203 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_add_eq
    have d204 : c = c := term_derivation_reflection
    have d205 : c ^ 1 = c := term_derivation_power_one
    have d206 : b = b := term_derivation_reflection
    have d207 : b ^ 1 = b := term_derivation_power_one
    have d208 : c * b = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_atom_mul_atom_less
    have d209 : c ^ 1 * b ^ 1 = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_mul_eq
    have d210 : (1 : ℝ) * (c ^ 1 * b ^ 1) = (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_one_mul
    have d211 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_reflection
    have d212 : (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_eq
    have d213 : -(0 : ℤ) = 0 := term_derivation_neg_literal
    have d214 : -((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_neg_product
    have d215 : -((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_neg_sum
    have d216 : -((1 : ℝ) * (c ^ 1 * a ^ 1)) = (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_neg_product
    have d217 : -((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_neg_sum
    have d218 : -((1 : ℝ) * (c ^ 1 * b ^ 1)) = (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_neg_product
    have d219 : -((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_neg_sum
    have d220 : -((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_neg_eq
    have d221 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (0 : ℝ) = (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_nf_add_zero
    have d222 : -1 = -1 := term_derivation_reflection
    have d223 : b = b := term_derivation_reflection
    have d224 : b ^ 1 = b := term_derivation_power_one
    have d225 : a = a := term_derivation_reflection
    have d226 : a ^ 1 = a := term_derivation_power_one
    have d227 : b * a = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_atom_mul_atom_less
    have d228 : b ^ 1 * a ^ 1 = (1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d229 : (-1 : ℤ) * (1 : ℤ) = -1 := term_derivation_literal_mul
    have d230 : (-1 : ℝ) * b ^ 1 = (-1 : ℝ) * b ^ 1 := term_derivation_reflection
    have d231 : (-1 : ℝ) * b ^ 1 * a ^ 1 = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_simple_product_mul_exponential_less
    have d232 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_product
    have d233 : (-1 : ℝ) * ((1 : ℝ) * (b ^ 1 * a ^ 1)) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_product
    have d234 : (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_mul_eq
    have d235 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (-1 : ℝ) * (b ^ 1 * a ^ 1) := term_derivation_zero_add
    have d236 : (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_product_add_product_less
    have d237 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_sum_add_product_greater
    have d238 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_reflection
    have d239 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_sum_add_product_greater
    have d240 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_reflection
    have d241 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (b ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_sum_add_product_greater
    have d242 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + ((0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_sum
    have d243 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) := term_derivation_reflection
    have d244 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_reflection
    have d245 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 := term_derivation_sum_add_product_greater
    have d246 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_reflection
    have d247 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 := term_derivation_sum_add_product_greater
    have d248 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_reflection
    have d249 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * a ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_sum_add_product_greater
    have d250 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + ((0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 := term_derivation_add_sum
    have d251 : (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_reflection
    have d252 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + ((0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * b ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_sum
    have d253 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1)) : ℝ) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_add_eq
    have d254 : (0 : ℝ) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 - ((0 : ℝ) + (1 : ℝ) * (b ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * (c ^ 1 * b ^ 1)) = (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) := term_derivation_literal_add_literal
    have d255 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a ↔ (0 : ℝ) + (-1 : ℝ) * (b ^ 1 * a ^ 1) + (-1 : ℝ) * (c ^ 1 * a ^ 1) + (1 : ℝ) * b ^ 2 + (1 : ℝ) * c ^ 2 + (1 : ℝ) * a ^ 2 + (-1 : ℝ) * (c ^ 1 * b ^ 1) ≥ (0 : ℝ) := term_derivation_num_comparison
    have d256 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := term_derivation_non_trivial_finish
    assumption
  obvious

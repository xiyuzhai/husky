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

def h (x : ℝ) (h1 : x ≥ (0 : ℝ)) (y : ℝ) (h2 : y ≥ (0 : ℝ)) : (x + y) / (2 : ℝ) ≥ √ (x * y) := by
  have h3 : (√ x - √ y) ^ 2 = √ x ^ 2 - (2 : ℝ) * √ x * √ y + √ y ^ 2 := by obvious
  have h4 : √ x ^ 2 - (2 : ℝ) * √ x * √ y + √ y ^ 2 = x - (2 : ℝ) * √ (x * y) + y := by obvious
  have h5 : x - (2 : ℝ) * √ (x * y) + y ≥ (0 : ℝ) := by obvious
  have h6 : (√ x - √ y) ^ 2 ≥ (0 : ℝ) := by apply sq_nonneg
  have h7 : x + y ≥ (2 : ℝ) * √ (x * y) := by
    have d : x = x := term_derivation_reflection
    have d1 : 2 = 2 := term_derivation_reflection
    have d2 : x = x := term_derivation_reflection
    have d3 : y = y := term_derivation_reflection
    have d4 : x * y = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_atom_mul_atom_less
    have d5 : x * y = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_mul_eq
    have d6 : √ (x * y) = (1 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_sqrt
    have d7 : 2 * 1 = 2 := term_derivation_literal_mul
    have d8 : (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_reflection
    have d9 : (2 : ℝ) * ((1 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2)) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_mul_product
    have d10 : (2 : ℝ) * √ (x * y) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_mul_eq
    have d11 : -((2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2)) = (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_neg_product
    have d12 : -((2 : ℝ) * √ (x * y)) = (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_neg_eq
    have d13 : x + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_atom_add_product
    have d14 : x + (-((2 : ℝ) * √ (x * y)) : ℝ) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_add_eq
    have d15 : x - (2 : ℝ) * √ (x * y) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_literal_add_literal
    have d16 : y = y := term_derivation_reflection
    have d17 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_reflection
    have d18 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_reflection
    have d19 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) + (1 : ℝ) * y ^ 1 = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_sum_add_product_greater
    have d20 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) + y = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_add_atom
    have d21 : x - (2 : ℝ) * √ (x * y) + y = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_add_eq
    have d22 : 0 = 0 := term_derivation_reflection
    have d23 : x = x := term_derivation_reflection
    have d24 : x ^ 1 = x := term_derivation_power_one
    have d25 : (1 : ℝ) * x ^ 1 = x := term_derivation_one_mul
    have d26 : (0 : ℝ) + (1 : ℝ) * x ^ 1 = x := term_derivation_zero_add
    have d27 : y = y := term_derivation_reflection
    have d28 : y ^ 1 = y := term_derivation_power_one
    have d29 : (1 : ℝ) * y ^ 1 = y := term_derivation_one_mul
    have d30 : x + (1 : ℝ) * y ^ 1 = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_atom_add_product
    have d31 : x + y = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_add_atom
    have d32 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_add_eq
    have d33 : -2 = -2 := term_derivation_reflection
    have d34 : x = x := term_derivation_reflection
    have d35 : x ^ 1 = x := term_derivation_power_one
    have d36 : y = y := term_derivation_reflection
    have d37 : y ^ 1 = y := term_derivation_power_one
    have d38 : x * y = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_atom_mul_atom_less
    have d39 : x ^ 1 * y ^ 1 = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_mul_eq
    have d40 : (1 : ℝ) * (x ^ 1 * y ^ 1) = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_one_mul
    have d41 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := term_derivation_reflection
    have d42 : ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (1 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_non_reduced_power
    have d43 : (-2 : ℤ) * (1 : ℤ) = -2 := term_derivation_literal_mul
    have d44 : (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_reflection
    have d45 : (-2 : ℝ) * ((1 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2)) = (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_mul_product
    have d46 : (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_mul_eq
    have d47 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_reflection
    have d48 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_add_eq
    have d49 : -(0 : ℤ) = 0 := term_derivation_neg_literal
    have d50 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) + (0 : ℝ) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_nf_add_zero
    have d51 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) + (-(0 : ℤ) : ℝ) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_add_eq
    have d52 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) - (0 : ℝ) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_literal_add_literal
    have d53 : x - (2 : ℝ) * √ (x * y) + y ≥ (0 : ℝ) ↔ (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) ≥ (0 : ℝ) := term_derivation_num_comparison
    have d54 : x = x := term_derivation_reflection
    have d55 : y = y := term_derivation_reflection
    have d56 : x + (1 : ℝ) * y ^ 1 = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_atom_add_product
    have d57 : x + y = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_add_atom
    have d58 : x + y = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_add_eq
    have d59 : 2 = 2 := term_derivation_reflection
    have d60 : x = x := term_derivation_reflection
    have d61 : y = y := term_derivation_reflection
    have d62 : x * y = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_atom_mul_atom_less
    have d63 : x * y = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_mul_eq
    have d64 : √ (x * y) = (1 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_sqrt
    have d65 : 2 * 1 = 2 := term_derivation_literal_mul
    have d66 : (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_reflection
    have d67 : (2 : ℝ) * ((1 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2)) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_mul_product
    have d68 : (2 : ℝ) * √ (x * y) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_mul_eq
    have d69 : x = x := term_derivation_reflection
    have d70 : x ^ 1 = x := term_derivation_power_one
    have d71 : (1 : ℝ) * x ^ 1 = x := term_derivation_one_mul
    have d72 : (0 : ℝ) + (1 : ℝ) * x ^ 1 = x := term_derivation_zero_add
    have d73 : y = y := term_derivation_reflection
    have d74 : y ^ 1 = y := term_derivation_power_one
    have d75 : (1 : ℝ) * y ^ 1 = y := term_derivation_one_mul
    have d76 : x + (1 : ℝ) * y ^ 1 = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_atom_add_product
    have d77 : x + y = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_add_atom
    have d78 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 := term_derivation_add_eq
    have d79 : 2 = 2 := term_derivation_reflection
    have d80 : x = x := term_derivation_reflection
    have d81 : x ^ 1 = x := term_derivation_power_one
    have d82 : y = y := term_derivation_reflection
    have d83 : y ^ 1 = y := term_derivation_power_one
    have d84 : x * y = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_atom_mul_atom_less
    have d85 : x ^ 1 * y ^ 1 = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_mul_eq
    have d86 : (1 : ℝ) * (x ^ 1 * y ^ 1) = (1 : ℝ) * (x ^ 1 * y ^ 1) := term_derivation_one_mul
    have d87 : (1 : ℚ) / 2 = (1 : ℚ) / 2 := term_derivation_reflection
    have d88 : ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (1 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_non_reduced_power
    have d89 : 2 * 1 = 2 := term_derivation_literal_mul
    have d90 : (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_reflection
    have d91 : (2 : ℝ) * ((1 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2)) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_mul_product
    have d92 : (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_mul_eq
    have d93 : -((2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2)) = (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_neg_product
    have d94 : -((2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2)) = (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_neg_eq
    have d95 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_reflection
    have d96 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-((2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2)) : ℝ) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_add_eq
    have d97 : (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 - (2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) = (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) := term_derivation_literal_add_literal
    have d98 : x + y ≥ (2 : ℝ) * √ (x * y) ↔ (0 : ℝ) + (1 : ℝ) * x ^ 1 + (1 : ℝ) * y ^ 1 + (-2 : ℝ) * ((1 : ℝ) * (x ^ 1 * y ^ 1)) ^ ((1 : ℚ) / 2) ≥ (0 : ℝ) := term_derivation_num_comparison
    have d99 : x + y ≥ (2 : ℝ) * √ (x * y) := term_derivation_non_trivial_finish
    assumption
  have h8 : (x + y) / (2 : ℝ) ≥ √ (x * y) := by obvious
  obvious

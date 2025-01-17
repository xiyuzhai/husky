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
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_sub": tactic =>`(tactic|
  first
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_product": tactic =>`(tactic|
  first
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_div": tactic =>`(tactic|
  first
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_finalize": tactic =>`(tactic|
  first
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_chaining_separated_list": tactic =>`(tactic|
  first
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_square": tactic =>`(tactic|
  first
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
    (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) = (2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2) + (2 : ℝ) * (c ^ 2) - (2 : ℝ) * a * b - (2 : ℝ) * b * c - (2 : ℝ) * c * a := by obvious
    _ = a ^ 2 - (2 : ℝ) * a * b + b ^ 2 + (b ^ 2 - (2 : ℝ) * b * c + c ^ 2) + (c ^ 2 - (2 : ℝ) * c * a + a ^ 2) := by obvious
    _ = (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by obvious
  | have h2 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by calc
    (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = a ^ 2 - (2 : ℝ) * a * b + b ^ 2 + (b ^ 2 - (2 : ℝ) * b * c + c ^ 2) + (c ^ 2 - (2 : ℝ) * c * a + a ^ 2) := by obvious
    _ = (2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2) + (2 : ℝ) * (c ^ 2) - (2 : ℝ) * a * b - (2 : ℝ) * b * c - (2 : ℝ) * c * a := by obvious
    _ = (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) := by obvious
  have h3 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ (0 : ℝ) := by obvious
  have h4 : (2 : ℝ) * (a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a) ≥ (0 : ℝ) := by obvious
  have h5 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a ≥ (0 : ℝ) := by litnum_bound
  have h6 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have d : a = a := by term_derivation_variable
    have d1 : 2 = 2 := by term_derivation_literal
    have d2 : a ^ 2 = a ^ 2 := by term_derivation_power
    have d3 : b = b := by term_derivation_variable
    have d4 : 2 = 2 := by term_derivation_literal
    have d5 : b ^ 2 = b ^ 2 := by term_derivation_power
    have d6 : c = c := by term_derivation_variable
    have d7 : 2 = 2 := by term_derivation_literal
    have d8 : c ^ 2 = c ^ 2 := by term_derivation_power
    have d9 : a ^ 2 + b ^ 2 + c ^ 2 = b ^ 2 + c ^ 2 + a ^ 2 := by term_derivation_sum
    have d10 : a = a := by term_derivation_variable
    have d11 : b = b := by term_derivation_variable
    have d12 : a * b = b + a := by term_derivation_product
    have d13 : a ^ 2 + b ^ 2 + c ^ 2 - a * b = (-1 : ℝ) + b + a + b ^ 2 + c ^ 2 + a ^ 2 := by term_derivation_sub
    have d14 : b = b := by term_derivation_variable
    have d15 : c = c := by term_derivation_variable
    have d16 : b * c = c + b := by term_derivation_product
    have d17 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c = (-1 : ℝ) + b + a + b ^ 2 + c ^ 2 + a ^ 2 + ((-1 : ℝ) + c + b) := by term_derivation_sub
    have d18 : c = c := by term_derivation_variable
    have d19 : a = a := by term_derivation_variable
    have d20 : c * a = c + a := by term_derivation_product
    have d21 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a = (-1 : ℝ) + b + a + ((-1 : ℝ) + c + a) + b ^ 2 + c ^ 2 + a ^ 2 + ((-1 : ℝ) + c + b) := by term_derivation_sub
    have d22 : (0 : ℝ) = (0 : ℝ) := by term_derivation_literal
    have d23 : a ^ 2 + b ^ 2 + c ^ 2 - a * b - b * c - c * a ≥ (0 : ℝ) = ((-1 : ℝ) + b + a + ((-1 : ℝ) + c + a) + b ^ 2 + c ^ 2 + a ^ 2 + ((-1 : ℝ) + c + b) ≥ (0 : ℝ)) := by term_derivation_chaining_separated_list
    have d24 : a = a := by term_derivation_variable
    have d25 : 2 = 2 := by term_derivation_literal
    have d26 : a ^ 2 = a ^ 2 := by term_derivation_power
    have d27 : b = b := by term_derivation_variable
    have d28 : 2 = 2 := by term_derivation_literal
    have d29 : b ^ 2 = b ^ 2 := by term_derivation_power
    have d30 : c = c := by term_derivation_variable
    have d31 : 2 = 2 := by term_derivation_literal
    have d32 : c ^ 2 = c ^ 2 := by term_derivation_power
    have d33 : a ^ 2 + b ^ 2 + c ^ 2 = b ^ 2 + c ^ 2 + a ^ 2 := by term_derivation_sum
    have d34 : a = a := by term_derivation_variable
    have d35 : b = b := by term_derivation_variable
    have d36 : a * b = b + a := by term_derivation_product
    have d37 : b = b := by term_derivation_variable
    have d38 : c = c := by term_derivation_variable
    have d39 : b * c = c + b := by term_derivation_product
    have d40 : c = c := by term_derivation_variable
    have d41 : a = a := by term_derivation_variable
    have d42 : c * a = c + a := by term_derivation_product
    have d43 : a * b + b * c + c * a = b + a + (c + a) + (c + b) := by term_derivation_sum
    have d44 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a = ((-1 : ℝ) + b + a + ((-1 : ℝ) + c + a) + b ^ 2 + c ^ 2 + a ^ 2 + ((-1 : ℝ) + c + b) ≥ (0 : ℝ)) := by term_derivation_chaining_separated_list
    have d45 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by term_derivation_finalize
    term_derivation_finalize
  obvious

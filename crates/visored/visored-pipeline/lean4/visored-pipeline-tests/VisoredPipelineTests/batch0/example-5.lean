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

def h (a b : ℝ) : (a ^ 2 + b ^ 2) / (2 : ℝ) ≥ ((a + b) / (2 : ℝ)) ^ 2 := by
  first
  | have h1 : (a ^ 2 + b ^ 2) / (2 : ℝ) - ((a + b) / (2 : ℝ)) ^ 2 ≥ (0 : ℝ) := by calc
    (a ^ 2 + b ^ 2) / (2 : ℝ) - ((a + b) / (2 : ℝ)) ^ 2 = ((2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2)) / (4 : ℝ) - (a ^ 2 + (2 : ℝ) * a * b + b ^ 2) / (4 : ℝ) := by obvious
    _ = (a ^ 2 - (2 : ℝ) * a * b + b ^ 2) / (4 : ℝ) := by obvious
    _ = (a - b) ^ 2 / (4 : ℝ) := by obvious
    _ ≥ (0 : ℝ) := by obvious
  | have h2 : (a - b) ^ 2 / (4 : ℝ) ≥ (0 : ℝ) := by calc
    (a - b) ^ 2 / (4 : ℝ) = (a ^ 2 - (2 : ℝ) * a * b + b ^ 2) / (4 : ℝ) := by obvious
    _ = ((2 : ℝ) * (a ^ 2) + (2 : ℝ) * (b ^ 2)) / (4 : ℝ) - (a ^ 2 + (2 : ℝ) * a * b + b ^ 2) / (4 : ℝ) := by obvious
    _ = (a ^ 2 + b ^ 2) / (2 : ℝ) - ((a + b) / (2 : ℝ)) ^ 2 := by obvious
    _ ≥ (0 : ℝ) := by obvious
  have h3 : (a ^ 2 + b ^ 2) / (2 : ℝ) - ((a + b) / (2 : ℝ)) ^ 2 ≥ (0 : ℝ) := by obvious
  have h4 : (a ^ 2 + b ^ 2) / (2 : ℝ) ≥ ((a + b) / (2 : ℝ)) ^ 2 := by
    have d : a = a := by term_derivation_variable
    have d1 : 2 = 2 := by term_derivation_literal
    have d2 : a ^ 2 = a ^ 2 := by term_derivation_power
    have d3 : b = b := by term_derivation_variable
    have d4 : 2 = 2 := by term_derivation_literal
    have d5 : b ^ 2 = b ^ 2 := by term_derivation_power
    have d6 : a ^ 2 + b ^ 2 = b ^ 2 + a ^ 2 := by term_derivation_sum
    have d7 : (2 : ℝ) = (2 : ℝ) := by term_derivation_literal
    have d8 : (a ^ 2 + b ^ 2) / (2 : ℝ) = ((1 : ℚ) / (2 : ℚ) : ℝ) * (b ^ 2) + ((1 : ℚ) / (2 : ℚ) : ℝ) * (a ^ 2) := by term_derivation_div
    have d9 : a = a := by term_derivation_variable
    have d10 : b = b := by term_derivation_variable
    have d11 : a + b = b + a := by term_derivation_sum
    have d12 : (2 : ℝ) = (2 : ℝ) := by term_derivation_literal
    have d13 : (a + b) / (2 : ℝ) = ((1 : ℚ) / (2 : ℚ) : ℝ) * b + ((1 : ℚ) / (2 : ℚ) : ℝ) * a := by term_derivation_div
    have d14 : 2 = 2 := by term_derivation_literal
    have d15 : ((a + b) / (2 : ℝ)) ^ 2 = (((1 : ℚ) / (2 : ℚ) : ℝ) * b + ((1 : ℚ) / (2 : ℚ) : ℝ) * a) ^ 2 := by term_derivation_power
    have d16 : (a ^ 2 + b ^ 2) / (2 : ℝ) - ((a + b) / (2 : ℝ)) ^ 2 = ((1 : ℚ) / (2 : ℚ) : ℝ) * (b ^ 2) + (-1 : ℝ) * ((((1 : ℚ) / (2 : ℚ) : ℝ) * b + ((1 : ℚ) / (2 : ℚ) : ℝ) * a) ^ 2) + ((1 : ℚ) / (2 : ℚ) : ℝ) * (a ^ 2) := by term_derivation_sub
    have d17 : (0 : ℝ) = (0 : ℝ) := by term_derivation_literal
    have d18 : (a ^ 2 + b ^ 2) / (2 : ℝ) - ((a + b) / (2 : ℝ)) ^ 2 ≥ (0 : ℝ) = (((1 : ℚ) / (2 : ℚ) : ℝ) * (b ^ 2) + (-1 : ℝ) * ((((1 : ℚ) / (2 : ℚ) : ℝ) * b + ((1 : ℚ) / (2 : ℚ) : ℝ) * a) ^ 2) + ((1 : ℚ) / (2 : ℚ) : ℝ) * (a ^ 2) ≥ (0 : ℝ)) := by term_derivation_chaining_separated_list
    have d19 : a = a := by term_derivation_variable
    have d20 : 2 = 2 := by term_derivation_literal
    have d21 : a ^ 2 = a ^ 2 := by term_derivation_power
    have d22 : b = b := by term_derivation_variable
    have d23 : 2 = 2 := by term_derivation_literal
    have d24 : b ^ 2 = b ^ 2 := by term_derivation_power
    have d25 : a ^ 2 + b ^ 2 = b ^ 2 + a ^ 2 := by term_derivation_sum
    have d26 : (2 : ℝ) = (2 : ℝ) := by term_derivation_literal
    have d27 : (a ^ 2 + b ^ 2) / (2 : ℝ) = ((1 : ℚ) / (2 : ℚ) : ℝ) * (b ^ 2) + ((1 : ℚ) / (2 : ℚ) : ℝ) * (a ^ 2) := by term_derivation_div
    have d28 : a = a := by term_derivation_variable
    have d29 : b = b := by term_derivation_variable
    have d30 : a + b = b + a := by term_derivation_sum
    have d31 : (2 : ℝ) = (2 : ℝ) := by term_derivation_literal
    have d32 : (a + b) / (2 : ℝ) = ((1 : ℚ) / (2 : ℚ) : ℝ) * b + ((1 : ℚ) / (2 : ℚ) : ℝ) * a := by term_derivation_div
    have d33 : 2 = 2 := by term_derivation_literal
    have d34 : ((a + b) / (2 : ℝ)) ^ 2 = (((1 : ℚ) / (2 : ℚ) : ℝ) * b + ((1 : ℚ) / (2 : ℚ) : ℝ) * a) ^ 2 := by term_derivation_power
    have d35 : (a ^ 2 + b ^ 2) / (2 : ℝ) ≥ ((a + b) / (2 : ℝ)) ^ 2 = (((1 : ℚ) / (2 : ℚ) : ℝ) * (b ^ 2) + (-1 : ℝ) * ((((1 : ℚ) / (2 : ℚ) : ℝ) * b + ((1 : ℚ) / (2 : ℚ) : ℝ) * a) ^ 2) + ((1 : ℚ) / (2 : ℚ) : ℝ) * (a ^ 2) ≥ (0 : ℝ)) := by term_derivation_chaining_separated_list
    have d36 : (a ^ 2 + b ^ 2) / (2 : ℝ) ≥ ((a + b) / (2 : ℝ)) ^ 2 := by term_derivation_finalize
    term_derivation_finalize
  obvious

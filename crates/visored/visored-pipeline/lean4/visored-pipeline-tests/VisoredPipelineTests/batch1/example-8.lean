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
    _ ≥ (0 : ℝ) := by obvious
  | have h6 : a / b - (2 : ℝ) + b / a ≥ (0 : ℝ) := by calc
    a / b - (2 : ℝ) + b / a = √ (a / b) ^ 2 - (2 : ℝ) * √ (a / b) * √ (b / a) + √ (b / a) ^ 2 := by obvious
    _ = (√ (a / b) - √ (b / a)) ^ 2 := by obvious
    _ ≥ (0 : ℝ) := by obvious
  have h7 : a / b - (2 : ℝ) + b / a ≥ (0 : ℝ) := by obvious
  have h8 : a / b + b / a ≥ (2 : ℝ) := by
    have d : a = a := by term_derivation_variable
    have d1 : b = b := by term_derivation_variable
    have d2 : a / b = b + a := by term_derivation_div
    have d3 : (2 : ℝ) = (2 : ℝ) := by term_derivation_literal
    have d4 : a / b - (2 : ℝ) = (-2 : ℝ) + (b + a) := by term_derivation_sub
    have d5 : b = b := by term_derivation_variable
    have d6 : a = a := by term_derivation_variable
    have d7 : b / a = b + a := by term_derivation_div
    have d8 : a / b - (2 : ℝ) + b / a = (-2 : ℝ) + ((2 : ℝ) + b + a) := by term_derivation_sum
    have d9 : (0 : ℝ) = (0 : ℝ) := by term_derivation_literal
    have d10 : a / b - (2 : ℝ) + b / a ≥ (0 : ℝ) = ((-2 : ℝ) + ((2 : ℝ) + b + a) ≥ (0 : ℝ)) := by term_derivation_chaining_separated_list
    have d11 : a = a := by term_derivation_variable
    have d12 : b = b := by term_derivation_variable
    have d13 : a / b = b + a := by term_derivation_div
    have d14 : b = b := by term_derivation_variable
    have d15 : a = a := by term_derivation_variable
    have d16 : b / a = b + a := by term_derivation_div
    have d17 : a / b + b / a = (2 : ℝ) + b + a := by term_derivation_sum
    have d18 : (2 : ℝ) = (2 : ℝ) := by term_derivation_literal
    have d19 : a / b + b / a ≥ (2 : ℝ) = ((-2 : ℝ) + ((2 : ℝ) + b + a) ≥ (0 : ℝ)) := by term_derivation_chaining_separated_list
    have d20 : a / b + b / a ≥ (2 : ℝ) := by term_derivation_finalize
    term_derivation_finalize
  obvious

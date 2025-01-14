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
  have h6 : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by term_equivalence
  obvious

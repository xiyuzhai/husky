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

def h (a b : ℝ) : (a + b) ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by
  have h1 : (a + b) ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by
    simp
    apply sq_nonneg
  obvious

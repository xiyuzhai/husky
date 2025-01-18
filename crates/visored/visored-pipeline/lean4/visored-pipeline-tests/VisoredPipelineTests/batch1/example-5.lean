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

def h (x : ℝ) : x ^ 2 + (1 : ℝ) ≥ (2 : ℝ) * x := by
  first
  | have h1 : (x - (1 : ℝ)) ^ 2 ≥ (0 : ℝ) := by calc
    (x - (1 : ℝ)) ^ 2 = x ^ 2 - (2 : ℝ) * x + (1 : ℝ) := by obvious
    _ ≥ (0 : ℝ) := by obvious
  | have h2 : x ^ 2 - (2 : ℝ) * x + (1 : ℝ) ≥ (0 : ℝ) := by calc
    x ^ 2 - (2 : ℝ) * x + (1 : ℝ) = (x - (1 : ℝ)) ^ 2 := by obvious
    _ ≥ (0 : ℝ) := by obvious
  have h3 : x ^ 2 + (1 : ℝ) ≥ (2 : ℝ) * x := by obvious
  obvious

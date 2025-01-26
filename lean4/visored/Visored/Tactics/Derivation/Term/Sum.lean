import Mathlib

theorem term_derivation_add_atom_thm {α} {a b term: α} [CommRing α] (h: a + 1 * b^1 = term) : a + b = term := by
  rw [←h]
  ring

/-- derive `a + b => term` from `a + 1 * b^1 => term` if `b` is an atom
-/
macro "term_derivation_add_atom" d:term : tactic => `(tactic| (exact term_derivation_add_atom_thm $d))

example (x: ℝ) (d18: (-1 : ℝ) + (1 : ℝ) * x ^ 1 = (-1 : ℝ) + (1 : ℝ) * x ^ 1)
  : (-1 : ℝ) + x = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := by
  term_derivation_add_atom d18

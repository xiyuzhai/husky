import Mathlib

theorem term_derivation_add_atom {α} {a b term: α} [CommRing α] (h: a + 1 * b^1 = term) : a + b = term := by
  rw [←h]
  ring

/-- derive `a + b => term` from `a + 1 * b^1 => term` if `b` is an atom
-/
macro "term_derivation_add_atom" d:term : tactic => `(tactic| (exact term_derivation_add_atom $d))

example (x: ℝ) (d18: (-1 : ℝ) + (1 : ℝ) * x ^ 1 = (-1 : ℝ) + (1 : ℝ) * x ^ 1)
  : (-1 : ℝ) + x = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := by
  term_derivation_add_atom d18

theorem term_derivation_atom_add_non_zero_literal {α} {a c: α} [CommRing α] : a + c = c + 1 * a^1 := by
  ring

/-- derive `a + c => c + 1 * a^1` if `a` is an atom and `c` is a litnum -/
macro "term_derivation_atom_add_non_zero_literal" : tactic => `(tactic| (exact term_derivation_atom_add_non_zero_literal))

example (x: ℝ) : x + 2 = 2 + 1 * x^1 := by
  term_derivation_atom_add_non_zero_literal

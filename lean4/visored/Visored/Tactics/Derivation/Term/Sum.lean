import Mathlib

theorem term_derivation_add_assoc {α} {a b c b_add_c a_add_b: α} [CommRing α]
  (hbc: b + c = b_add_c)
  (hab: a + b = a_add_b)
  : a + b_add_c = a_add_b + c := by
  rw [← hbc, ← hab]
  ring

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

theorem term_derivation_add_eq {α β γ} {a term_a :α} {b term_b:β} {term: γ} [CommRing γ][CoeTC α γ] [CoeTC β γ]
  (ha: a = term_a) (hb: b = term_b) (hab: (term_a:γ)+ (term_b:γ)= term) : (a:γ) + (b:γ) = term := by
  rw [ha, hb, hab]

/-- derive `a + b => term` from `a => term_a`, `b => term_b` and `term_a + term_b => term`
-/
macro "term_derivation_add_eq" ha:term:1024 hb:term:1024 hab:term:1024 : tactic =>
  `(tactic| exact term_derivation_add_eq $ha $hb $hab)

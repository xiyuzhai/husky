import Mathlib
import Visored.Obvious
import Visored.Tactics

def h (a b : ℝ) : (a + b : ℝ) = (b + a : ℝ) := by
  have h1 : (a + b : ℝ) = (b + a : ℝ) := by term_trivial
  obvious

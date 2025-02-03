import Mathlib
import Visored.Obvious
import Visored.Tactics

def h (x : ℝ) : (x ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
  have h1 : (x ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    simp
    apply sq_nonneg
  obvious

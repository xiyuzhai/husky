import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h (x : ℝ) : (x ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
  have h1 : (x ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    simp
    apply sq_nonneg
  obvious

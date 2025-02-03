import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h (x y : ℝ) : ((x ^ (2:ℕ) : ℝ) + (y ^ (2:ℕ) : ℝ) : ℝ) ≥ ((((2:ℕ) : ℝ) * x : ℝ) * y : ℝ) := by
  first
  | have h1 : ((x - y : ℝ) ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    ((x - y : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ (2:ℕ) : ℝ) - ((((2:ℕ) : ℝ) * x : ℝ) * y : ℝ) : ℝ) + (y ^ (2:ℕ) : ℝ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  | have h2 : (((x ^ (2:ℕ) : ℝ) - ((((2:ℕ) : ℝ) * x : ℝ) * y : ℝ) : ℝ) + (y ^ (2:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    (((x ^ (2:ℕ) : ℝ) - ((((2:ℕ) : ℝ) * x : ℝ) * y : ℝ) : ℝ) + (y ^ (2:ℕ) : ℝ) : ℝ) = ((x - y : ℝ) ^ (2:ℕ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  have h3 : ((x ^ (2:ℕ) : ℝ) + (y ^ (2:ℕ) : ℝ) : ℝ) ≥ ((((2:ℕ) : ℝ) * x : ℝ) * y : ℝ) := by obvious
  obvious

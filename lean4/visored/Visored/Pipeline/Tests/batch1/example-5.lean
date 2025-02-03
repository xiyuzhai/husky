import Mathlib
import Visored.Obvious
import Visored.Tactics

def h (x : ℝ) : ((x ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((2:ℕ) * x : ℝ) := by
  first
  | have h1 : ((x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    ((x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  | have h2 : (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  have h3 : ((x ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((2:ℕ) * x : ℝ) := by obvious
  obvious

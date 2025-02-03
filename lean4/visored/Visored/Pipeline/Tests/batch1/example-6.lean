import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h (x : ℝ) (h1 : x ≥ ((0:ℕ) : ℝ)) : ((x : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ (((2:ℕ) : ℝ) * √ x : ℝ) := by
  first
  | have h2 : ((√ x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    ((√ x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x - (((2:ℕ) : ℝ) * √ x : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  | have h3 : (((x - (((2:ℕ) : ℝ) * √ x : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    (((x - (((2:ℕ) : ℝ) * √ x : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((√ x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  have h4 : ((x : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ (((2:ℕ) : ℝ) * √ x : ℝ) := by obvious
  obvious

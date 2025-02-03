import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h (a b : ℝ) : ((a : ℝ) + b : ℝ) = ((b : ℝ) + a : ℝ) := by
  have h1 : ((a : ℝ) + b : ℝ) = ((b : ℝ) + a : ℝ) := by term_trivial
  obvious

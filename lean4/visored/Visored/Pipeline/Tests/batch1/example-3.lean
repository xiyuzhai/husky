import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h (a b : ℝ) : (a + b : ℝ) = (b + a : ℝ) := by
  have h1 : (a + b : ℝ) = (b + a : ℝ) := by term_trivial
  obvious

import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h : ((1:ℕ) + (1:ℕ) : ℕ) = (2:ℕ) := by
  have h1 : ((1:ℕ) + (1:ℕ) : ℕ) = (2:ℕ) := by term_trivial
  obvious

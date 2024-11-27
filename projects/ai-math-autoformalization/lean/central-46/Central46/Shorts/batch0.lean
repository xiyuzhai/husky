import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Explode

namespace Example1
def h : 1 + 1 = 2 := sorry
end Example1

namespace Example2
variable (x : ℝ)

def h : x ^ 2 ≥ 0 := sorry
end Example2

namespace Example3
variable (x : ℝ)

def h : x ^ 2 + 1 ≥ 2 * x := sorry
end Example3

namespace Example4
def h : 1 = 1 := by
  calc
    1 = 1 := sorry
    _ = 1 := sorry

def h1 : 1 < 2 := by
  calc
    1 = 1 := sorry
    _ < 2 := sorry

def h2 : 1.0 ≤ 1 := by
  calc
    1.0 ≤ 1 := sorry
    _ ≤ 1 := sorry
end Example4

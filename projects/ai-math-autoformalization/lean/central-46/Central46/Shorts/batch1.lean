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
variable (a : ℝ)

variable (b : ℝ)

def h : a + b = b + a := sorry
end Example3

namespace Example4
variable (x : ℝ)

def h : x ^ 2 ≥ 0 := sorry
end Example4

namespace Example5
variable (x : ℝ)

variable (h : x > 0)

def h1 : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := sorry

def h2 : (x ^ 2 + 1 - 2 * x) / x = (x - 1) ^ 2 / x := sorry

def h3 : x + 1 / x - 2 = (x - 1) ^ 2 / x := sorry

def h4 : (x - 1) ^ 2 / x ≥ 0 := sorry

def h5 : x + 1 / x - 2 ≥ 0 := sorry

def h6 : x + 1 / x ≥ 2 := sorry
end Example5

namespace Example6
variable (x : ℝ)

def h : x + 1 / x - 2 = (x ^ 2 + 1 - 2 * x) / x := sorry

def h1 : (x ^ 2 + 1 - 2 * x) / x = (x - 1) ^ 2 / x := sorry

def h2 : x + 1 / x - 2 = (x - 1) ^ 2 / x := sorry

def h3 : (x - 1) ^ 2 / x ≥ 0 := sorry

def h4 : x + 1 / x - 2 ≥ 0 := sorry

def h5 : x + 1 / x ≥ 2 := sorry
end Example6

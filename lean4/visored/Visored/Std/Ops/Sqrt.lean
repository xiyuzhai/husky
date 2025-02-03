import Mathlib

/-- refer to https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html#Real.instPow -/
noncomputable instance : HPow ℝ ℚ ℝ where
  hPow (x : ℝ) (q : ℚ) :=
    x^(q:ℝ)

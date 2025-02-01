import Mathlib

theorem litnum_bound_derivation_normalize_ge {α} { x y k : α } [LinearOrderedField α] (hk : k > 0) : x ≥ y ↔ (x - y) / k ≥ ((0:ℕ) : α) := by
  constructor
  · intro h
    have h1 : x - y ≥ 0 := by linarith
    have h2 : (x - y) / k ≥ 0 := by apply div_nonneg h1 (le_of_lt hk)
    have h3 : (x - y) / k ≥ 0 := by linarith
    simp
    exact h3
  · intro h
    have h1 : (x - y) / k ≥ 0 := by linarith
    have h2 : (x - y) / k * k ≥ 0 := by apply mul_nonneg h1 (le_of_lt hk)
    have h3 : (x - y) / k * k = x - y := by field_simp
    rw[h3] at h2
    linarith

macro "litnum_bound_derivation_normalize" "≥" : tactic => `(tactic| exact litnum_bound_derivation_normalize_ge (by norm_num))


theorem litnum_bound_derivation_normalize_gt {α} { x y k : α } [LinearOrderedField α] (hk : k > 0) : x > y ↔ (x - y) / k > ((0:ℕ) : α) := by
  constructor
  · intro h
    have h1 : x - y > 0 := by linarith
    have h2 : (x - y) / k > 0 := by apply div_pos h1 hk
    simp
    exact h2
  · intro h
    have h1 : (x - y) / k > 0 := by linarith
    have h2 : (x - y) / k * k > 0 := by apply mul_pos h1 hk
    have h3 : (x - y) / k * k = x - y := by field_simp
    rw[h3] at h2
    linarith

macro "litnum_bound_derivation_normalize" ">" : tactic => `(tactic| exact litnum_bound_derivation_normalize_gt (by norm_num))

macro "litnum_bound_derivation_finish" : tactic => `(tactic| fail "not implemented")

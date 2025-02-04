import Mathlib

theorem term_derivation_num_comparison_gt
  {α β αβ}
  [LinearOrderedCommRing αβ]
  {a a_nf : α}
  {b b_nf : β}
  {a_αβ b_αβ a_nf_αβ b_nf_αβ term: αβ}
  (ha_nf: a = a_nf)
  (hb_nf: b = b_nf)
  (h: a_nf_αβ - b_nf_αβ = term)
  (ha_eq_coercion: a = a_nf ↔ a_αβ = a_nf_αβ)
  (hb_eq_coercion: b = b_nf ↔ b_αβ = b_nf_αβ)
  : a_αβ > b_αβ ↔ term > ((0:ℕ):αβ) := by
  have ha_nf: a_αβ = a_nf_αβ := ha_eq_coercion.mp ha_nf
  have hb_nf: b_αβ = b_nf_αβ := hb_eq_coercion.mp hb_nf
  constructor
  . intro hab
    rw [← h]
    rw [← ha_nf, ← hb_nf]
    simp
    linarith
  . intro hab
    rw [ha_nf, hb_nf]
    linarith

macro "term_derivation_num_comparison"
  ">"
  ha_nf:term:1024
  hb_nf:term:1024
  h:term:1024
  ha_eq_coercion:term:1024
  hb_eq_coercion:term:1024
  : tactic => `(tactic| exact term_derivation_num_comparison_gt $ha_nf $hb_nf $h $ha_eq_coercion $hb_eq_coercion)

theorem term_derivation_num_comparison_ge
  {α β αβ}
  [LinearOrderedCommRing αβ]
  {a a_nf : α}
  {b b_nf : β}
  {a_αβ b_αβ a_nf_αβ b_nf_αβ term: αβ}
  (ha_nf: a = a_nf)
  (hb_nf: b = b_nf)
  (h: a_nf_αβ - b_nf_αβ = term)
  (ha_eq_coercion: a = a_nf ↔ a_αβ = a_nf_αβ)
  (hb_eq_coercion: b = b_nf ↔ b_αβ = b_nf_αβ)
  : a_αβ ≥ b_αβ ↔ term ≥ ((0:ℕ):αβ) := by
  have ha_nf: a_αβ = a_nf_αβ := ha_eq_coercion.mp ha_nf
  have hb_nf: b_αβ = b_nf_αβ := hb_eq_coercion.mp hb_nf
  constructor
  . intro hab
    rw [← h]
    rw [← ha_nf, ← hb_nf]
    simp
    linarith
  . intro hab
    rw [ha_nf, hb_nf]
    linarith

macro "term_derivation_num_comparison"
  "≥"
  ha_nf:term:1024
  hb_nf:term:1024
  h:term:1024
  ha_eq_coercion:term:1024
  hb_eq_coercion:term:1024
  : tactic => `(tactic| exact term_derivation_num_comparison_ge $ha_nf $hb_nf $h $ha_eq_coercion $hb_eq_coercion)

theorem term_derivation_num_comparison_lt
  {α β αβ}
  [LinearOrderedCommRing αβ]
  {a a_nf : α}
  {b b_nf : β}
  {a_αβ b_αβ a_nf_αβ b_nf_αβ term: αβ}
  (ha_nf: a = a_nf)
  (hb_nf: b = b_nf)
  (h: a_nf_αβ - b_nf_αβ = term)
  (ha_eq_coercion: a = a_nf ↔ a_αβ = a_nf_αβ)
  (hb_eq_coercion: b = b_nf ↔ b_αβ = b_nf_αβ)
  : a_αβ < b_αβ ↔ term < ((0:ℕ):αβ) := by
  have ha_nf: a_αβ = a_nf_αβ := ha_eq_coercion.mp ha_nf
  have hb_nf: b_αβ = b_nf_αβ := hb_eq_coercion.mp hb_nf
  constructor
  . intro hab
    rw [← h]
    rw [← ha_nf, ← hb_nf]
    simp
    linarith
  . intro hab
    rw [ha_nf, hb_nf]
    simp at hab
    linarith

macro "term_derivation_num_comparison"
  "<"
  ha_nf:term:1024
  hb_nf:term:1024
  h:term:1024
  ha_eq_coercion:term:1024
  hb_eq_coercion:term:1024
  : tactic => `(tactic| exact term_derivation_num_comparison_lt $ha_nf $hb_nf $h $ha_eq_coercion $hb_eq_coercion)

theorem term_derivation_num_comparison_le
  {α β αβ}
  [LinearOrderedCommRing αβ]
  {a a_nf : α}
  {b b_nf : β}
  {a_αβ b_αβ a_nf_αβ b_nf_αβ term: αβ}
  (ha_nf: a = a_nf)
  (hb_nf: b = b_nf)
  (h: a_nf_αβ - b_nf_αβ = term)
  (ha_eq_coercion: a = a_nf ↔ a_αβ = a_nf_αβ)
  (hb_eq_coercion: b = b_nf ↔ b_αβ = b_nf_αβ)
  : a_αβ ≤ b_αβ ↔ term ≤ ((0:ℕ):αβ) := by
  have ha_nf: a_αβ = a_nf_αβ := ha_eq_coercion.mp ha_nf
  have hb_nf: b_αβ = b_nf_αβ := hb_eq_coercion.mp hb_nf
  constructor
  . intro hab
    rw [← h]
    rw [← ha_nf, ← hb_nf]
    simp
    linarith
  . intro hab
    rw [ha_nf, hb_nf]
    simp at hab
    linarith

macro "term_derivation_num_comparison"
  "≤"
  ha_nf:term:1024
  hb_nf:term:1024
  h:term:1024
  ha_eq_coercion:term:1024
  hb_eq_coercion:term:1024
  : tactic => `(tactic| exact term_derivation_num_comparison_le $ha_nf $hb_nf $h $ha_eq_coercion $hb_eq_coercion)

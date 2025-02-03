import Mathlib

theorem term_derivation_num_comparison_gt
  {α}
  [LinearOrderedCommRing α]
  {a b a_nf b_nf term: α} (ha_nf: a = a_nf) (hb_nf: b = b_nf) (h: a_nf - b_nf = term) : a > b ↔ term > ((0:ℕ):α) := by
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
  : tactic => `(tactic| exact term_derivation_num_comparison_gt $ha_nf $hb_nf $h)

theorem term_derivation_num_comparison_ge
  {α}
  [LinearOrderedCommRing α]
  {a b a_nf b_nf term: α} (ha_nf: a = a_nf) (hb_nf: b = b_nf) (h: a_nf - b_nf = term) : a ≥ b ↔ term ≥ ((0:ℕ):α) := by
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
  : tactic => `(tactic| exact term_derivation_num_comparison_ge $ha_nf $hb_nf $h)

theorem term_derivation_num_comparison_lt
  {α}
  [LinearOrderedCommRing α]
  {a b a_nf b_nf term: α} (ha_nf: a = a_nf) (hb_nf: b = b_nf) (h: a_nf - b_nf = term) : a < b ↔ term < ((0:ℕ):α) := by
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
  : tactic => `(tactic| exact term_derivation_num_comparison_lt $ha_nf $hb_nf $h)

theorem term_derivation_num_comparison_le
  {α}
  [LinearOrderedCommRing α]
  {a b a_nf b_nf term: α} (ha_nf: a = a_nf) (hb_nf: b = b_nf) (h: a_nf - b_nf = term) : a ≤ b ↔ term ≤ ((0:ℕ):α) := by
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
  : tactic => `(tactic| exact term_derivation_num_comparison_le $ha_nf $hb_nf $h)

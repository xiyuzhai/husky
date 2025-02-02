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

theorem litnum_bound_derivation_normalize_le {α} { x y k : α } [LinearOrderedField α] (hk : k < 0) : x ≤ y ↔ (x - y) / k ≥ ((0:ℕ) : α) := by
  constructor
  · intro h
    have h1 : x - y ≤ 0 := by linarith
    have h2 : (x - y) / k ≥ 0 := by
      apply div_nonneg_of_nonpos
      linarith
      linarith
    simp
    exact h2
  · intro h
    have h1 : (x - y) / k ≥ 0 := by linarith
    have h2 : (x - y) / k * k ≤ 0 := by
      have h2 : 0 ≤ (x - y) / k * (-k) := by
        apply mul_nonneg_iff.mpr
        constructor
        . constructor
          . linarith
          . linarith
      linarith
    have h5 : k ≠ 0 := by linarith
    have h3 : (x - y) / k * k = x - y := by field_simp
    rw[h3] at h2
    linarith

macro "litnum_bound_derivation_normalize" "≤" : tactic => `(tactic| exact litnum_bound_derivation_normalize_le (by norm_num))

theorem litnum_bound_derivation_normalize_lt {α} { x y k : α } [LinearOrderedField α] (hk : k < 0) : x < y ↔ (x - y) / k > ((0:ℕ) : α) := by
  constructor
  · intro h
    have h1 : x - y < 0 := by linarith
    have h2 : (x - y) / k > 0 := div_pos_iff.2 <| Or.inr ⟨h1, hk⟩
    simp
    exact h2
  · intro h
    have h1 : (x - y) / k > 0 := by linarith
    have h2 : (x - y) / k * k < 0 := by
      have h2 : 0 < (x - y) / k * (-k) := by
        apply mul_pos_iff.mpr
        constructor
        . constructor
          . linarith
          . linarith
      linarith
    have h5 : k ≠ 0 := by linarith
    have h3 : (x - y) / k * k = x - y := by field_simp
    rw[h3] at h2
    linarith

macro "litnum_bound_derivation_normalize" "<" : tactic => `(tactic| exact litnum_bound_derivation_normalize_lt (by norm_num))

theorem litnum_bound_derivation_finish_gt_gt
  {src dst: Prop}
  {α β αβ}
  { x : α }
  { y : β }
  { x_sub_a_αβ  y_sub_b_αβ x_αβ a_αβ y_αβ b_αβ : αβ }
  [OrderedCommRing α]
  [OrderedCommRing β]
  [OrderedCommRing αβ]
  (hsrc : src)
  (hsrc_dn : src ↔ x > ((0:ℕ) : α))
  (hdst_dn : dst ↔ y > ((0:ℕ) : β))
  (hab : a_αβ ≤ b_αβ)
  (hsrc_nf_and_dst_nf_equivalence : x_sub_a_αβ = y_sub_b_αβ)
  (hx_sub_a_sub_coercion : x_sub_a_αβ = x_αβ - a_αβ)
  (hy_sub_b_sub_coercion : y_sub_b_αβ = y_αβ - b_αβ)
  (hx_gt_zero_gt_coercion: x > ((0:ℕ) : α) ↔ x_αβ > ((0:ℕ) : αβ))
  (hy_gt_zero_gt_coercion: y > ((0:ℕ) : β) ↔ y_αβ > ((0:ℕ) : αβ))
  : dst := by
  have hab2 : 0 ≤ b_αβ - a_αβ := sub_nonneg.mpr hab
  have hx_gt_zero : x_αβ > ((0:ℕ) : αβ) := hx_gt_zero_gt_coercion.mp $ hsrc_dn.mp hsrc
  have hy_gt_zero : y_αβ > ((0:ℕ) : αβ) := by
    have hsrc_nf_and_dst_nf_equivalence_coerced : x_αβ - a_αβ = y_αβ - b_αβ := by
      rw[← hx_sub_a_sub_coercion]
      rw[← hy_sub_b_sub_coercion]
      exact hsrc_nf_and_dst_nf_equivalence
    calc
      y_αβ = x_αβ - a_αβ + b_αβ := by rw[hsrc_nf_and_dst_nf_equivalence_coerced]; ring
      _ = x_αβ + (b_αβ - a_αβ) := by ring
      _ ≥ x_αβ + 0 := by gcongr
      _ = x_αβ := by ring
      _ > ((0:ℕ) : αβ) := by assumption
  exact hdst_dn.mpr $ hy_gt_zero_gt_coercion.mpr hy_gt_zero

example {α} [OrderedCommRing α] {x : α} : x > 0 -> x ≥ 0 := λ h => le_of_lt h

theorem litnum_bound_derivation_finish_gt_ge
  {src dst: Prop}
  {α β αβ}
  {x : α}
  {y : β}
  {x_sub_a_αβ  y_sub_b_αβ x_αβ a_αβ y_αβ b_αβ : αβ }
  [OrderedCommRing α]
  [OrderedCommRing β]
  [OrderedCommRing αβ]
  (hsrc : src)
  (hsrc_dn : src ↔ x > ((0:ℕ) : α))
  (hdst_dn : dst ↔ y ≥ ((0:ℕ) : β))
  (hab : a_αβ ≤ b_αβ)
  (hsrc_nf_and_dst_nf_equivalence : x_sub_a_αβ = y_sub_b_αβ)
  (hx_sub_a_sub_coercion : x_sub_a_αβ = x_αβ - a_αβ)
  (hy_sub_b_sub_coercion : y_sub_b_αβ = y_αβ - b_αβ)
  (hx_gt_zero_gt_coercion: x > ((0:ℕ) : α) ↔ x_αβ > ((0:ℕ) : αβ))
  (hy_gt_zero_gt_coercion: y ≥ ((0:ℕ) : β) ↔ y_αβ ≥ ((0:ℕ) : αβ))
  : dst := by
  have hab2 : 0 ≤ b_αβ - a_αβ := sub_nonneg.mpr hab
  have hx_gt_zero : x_αβ > ((0:ℕ) : αβ) := hx_gt_zero_gt_coercion.mp $ hsrc_dn.mp hsrc
  have hy_gt_zero : y_αβ ≥ ((0:ℕ) : αβ) := by
    have hsrc_nf_and_dst_nf_equivalence_coerced : x_αβ - a_αβ = y_αβ - b_αβ := by
      rw[← hx_sub_a_sub_coercion]
      rw[← hy_sub_b_sub_coercion]
      exact hsrc_nf_and_dst_nf_equivalence
    have hy_pos : y_αβ > ((0:ℕ) : αβ) := by
      calc
        y_αβ = x_αβ - a_αβ + b_αβ := by rw[hsrc_nf_and_dst_nf_equivalence_coerced]; ring
        _ = x_αβ + (b_αβ - a_αβ) := by ring
        _ ≥ x_αβ + 0 := by gcongr
        _ = x_αβ := by ring
        _ > ((0:ℕ) : αβ) := by assumption
    exact le_of_lt hy_pos
  exact hdst_dn.mpr $ hy_gt_zero_gt_coercion.mpr hy_gt_zero

theorem litnum_bound_derivation_finish_ge_gt
  {src dst : Prop}
  {α β αβ}
  {x : α }
  {y : β}
  {x_sub_a_αβ  y_sub_b_αβ x_αβ a_αβ y_αβ b_αβ : αβ }
  [OrderedCommRing α]
  [OrderedCommRing β]
  [OrderedCommRing αβ]
  (hsrc : src)
  (hsrc_dn : src ↔ x ≥ ((0:ℕ) : α))
  (hdst_dn : dst ↔ y > ((0:ℕ) : β))
  (hab : a_αβ < b_αβ)
  (hsrc_nf_and_dst_nf_equivalence : x_sub_a_αβ = y_sub_b_αβ)
  (hx_sub_a_sub_coercion : x_sub_a_αβ = x_αβ - a_αβ)
  (hy_sub_b_sub_coercion : y_sub_b_αβ = y_αβ - b_αβ)
  (hx_gt_zero_gt_coercion: x ≥ ((0:ℕ) : α) ↔ x_αβ ≥ ((0:ℕ) : αβ))
  (hy_gt_zero_gt_coercion: y > ((0:ℕ) : β) ↔ y_αβ > ((0:ℕ) : αβ))
  : dst := by
  have hab2 : 0 < b_αβ - a_αβ := sub_pos.mpr hab
  have hx_gt_zero : x_αβ ≥ ((0:ℕ) : αβ) := hx_gt_zero_gt_coercion.mp $ hsrc_dn.mp hsrc
  have hy_gt_zero : y_αβ > ((0:ℕ) : αβ) := by
    have hsrc_nf_and_dst_nf_equivalence_coerced : x_αβ - a_αβ = y_αβ - b_αβ := by
      rw[← hx_sub_a_sub_coercion]
      rw[← hy_sub_b_sub_coercion]
      exact hsrc_nf_and_dst_nf_equivalence
    calc
      y_αβ = x_αβ - a_αβ + b_αβ := by rw[hsrc_nf_and_dst_nf_equivalence_coerced]; ring
      _ = x_αβ + (b_αβ - a_αβ) := by ring
      _ > x_αβ + ((0:ℕ) : αβ) := by simp; gcongr;
      _ = x_αβ := by ring
      _ ≥ ((0:ℕ) : αβ) := by assumption
  exact hdst_dn.mpr $ hy_gt_zero_gt_coercion.mpr hy_gt_zero

theorem litnum_bound_derivation_finish_ge_ge
  {src dst: Prop}
  {α β αβ}
  {x : α}
  {y : β}
  {x_sub_a_αβ  y_sub_b_αβ x_αβ a_αβ y_αβ b_αβ : αβ}
  [OrderedCommRing α]
  [OrderedCommRing β]
  [OrderedCommRing αβ]
  (hsrc : src)
  (hsrc_dn : src ↔ x ≥ ((0:ℕ) : α))
  (hdst_dn : dst ↔ y ≥ ((0:ℕ) : β))
  (hab : a_αβ ≤ b_αβ)
  (hsrc_nf_and_dst_nf_equivalence : x_sub_a_αβ = y_sub_b_αβ)
  (hx_sub_a_sub_coercion : x_sub_a_αβ = x_αβ - a_αβ)
  (hy_sub_b_sub_coercion : y_sub_b_αβ = y_αβ - b_αβ)
  (hx_gt_zero_gt_coercion: x ≥ ((0:ℕ) : α) ↔ x_αβ ≥ ((0:ℕ) : αβ))
  (hy_gt_zero_gt_coercion: y ≥ ((0:ℕ) : β) ↔ y_αβ ≥ ((0:ℕ) : αβ))
  : dst := by
  have hab2 : 0 ≤ b_αβ - a_αβ := sub_nonneg.mpr hab
  have hx_gt_zero : x_αβ ≥ ((0:ℕ) : αβ) := hx_gt_zero_gt_coercion.mp $ hsrc_dn.mp hsrc
  have hy_gt_zero : y_αβ ≥ ((0:ℕ) : αβ) := by
    have hsrc_nf_and_dst_nf_equivalence_coerced : x_αβ - a_αβ = y_αβ - b_αβ := by
      rw[← hx_sub_a_sub_coercion]
      rw[← hy_sub_b_sub_coercion]
      exact hsrc_nf_and_dst_nf_equivalence
    calc
      y_αβ = x_αβ - a_αβ + b_αβ := by rw[hsrc_nf_and_dst_nf_equivalence_coerced]; ring
      _ = x_αβ + (b_αβ - a_αβ) := by ring
      _ ≥ x_αβ + ((0:ℕ) : αβ) := by simp; gcongr;
      _ = x_αβ := by ring
      _ ≥ ((0:ℕ) : αβ) := by assumption
  exact hdst_dn.mpr $ hy_gt_zero_gt_coercion.mpr hy_gt_zero

macro "litnum_bound_derivation_finish"
  ">" ">"
  hsrc:term:1024
  hsrc_dn:term:1024
  hdst_dn:term:1024
  hsrc_nf_and_dst_nf_equivalence:term:1024
  hx_sub_a_sub_coercion:term:1024
  hy_sub_b_sub_coercion:term:1024
  hx_gt_zero_gt_coercion:term:1024
  hy_gt_zero_gt_coercion:term:1024
  : tactic => `(tactic| exact litnum_bound_derivation_finish_gt_gt $hsrc $hsrc_dn $hdst_dn (by norm_num) $hsrc_nf_and_dst_nf_equivalence $hx_sub_a_sub_coercion $hy_sub_b_sub_coercion $hx_gt_zero_gt_coercion $hy_gt_zero_gt_coercion)

macro "litnum_bound_derivation_finish"
  ">" "≥"
  hsrc:term:1024
  hsrc_dn:term:1024
  hdst_dn:term:1024
  hsrc_nf_and_dst_nf_equivalence:term:1024
  hx_sub_a_sub_coercion:term:1024
  hy_sub_b_sub_coercion:term:1024
  hx_gt_zero_gt_coercion:term:1024
  hy_ge_zero_ge_coercion:term:1024
  : tactic => `(tactic| exact litnum_bound_derivation_finish_gt_ge $hsrc $hsrc_dn $hdst_dn (by norm_num) $hsrc_nf_and_dst_nf_equivalence $hx_sub_a_sub_coercion $hy_sub_b_sub_coercion $hx_gt_zero_gt_coercion $hy_ge_zero_ge_coercion)

macro "litnum_bound_derivation_finish"
  "≥" ">"
  hsrc:term:1024
  hsrc_dn:term:1024
  hdst_dn:term:1024
  hsrc_nf_and_dst_nf_equivalence:term:1024
  hx_sub_a_sub_coercion:term:1024
  hy_sub_b_sub_coercion:term:1024
  hx_ge_zero_ge_coercion:term:1024
  hy_gt_zero_gt_coercion:term:1024
  : tactic => `(tactic| exact litnum_bound_derivation_finish_ge_gt $hsrc $hsrc_dn $hdst_dn (by norm_num) $hsrc_nf_and_dst_nf_equivalence $hx_sub_a_sub_coercion $hy_sub_b_sub_coercion $hx_ge_zero_ge_coercion $hy_gt_zero_gt_coercion)

macro "litnum_bound_derivation_finish"
  "≥" "≥"
  hsrc:term:1024
  hsrc_dn:term:1024
  hdst_dn:term:1024
  hsrc_nf_and_dst_nf_equivalence:term:1024
  hx_sub_a_sub_coercion:term:1024
  hy_sub_b_sub_coercion:term:1024
  hx_ge_zero_ge_coercion:term:1024
  hy_ge_zero_ge_coercion:term:1024
  : tactic => `(tactic| exact litnum_bound_derivation_finish_ge_ge $hsrc $hsrc_dn $hdst_dn (by norm_num) $hsrc_nf_and_dst_nf_equivalence $hx_sub_a_sub_coercion $hy_sub_b_sub_coercion $hx_ge_zero_ge_coercion $hy_ge_zero_ge_coercion)

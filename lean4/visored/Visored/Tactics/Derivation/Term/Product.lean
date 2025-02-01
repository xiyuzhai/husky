import Mathlib

macro "term_derivation_power_one": tactic => `(tactic| simp)
macro "term_derivation_one_mul": tactic => `(tactic| simp)
macro "term_derivation_mul_one": tactic => `(tactic| simp)
macro "term_derivation_div_literal": tactic => `(tactic| simp)

theorem term_derivation_mul_eq {α β γ} {a term_a : α} {b term_b:β} {a1 b1 term_a1 term_b1 term: γ}
  [Field γ]
  (ha0: a = term_a)
  (hb0: b = term_b)
  (hab: term_a1 * term_b1 = term)
  (a_coercion: a = term_a -> a1 = term_a1)
  (b_coercion: b = term_b -> b1 = term_b1)
  : a1 * b1 = term := by
  have ha : a1 = term_a1 := a_coercion ha0
  have hb : b1 = term_b1 := b_coercion hb0
  rw [ha, hb]
  exact hab

macro "term_derivation_mul_eq"
  a_nf:term:1024
  b_nf:term:1024
  d:term:1024
  a_coercion:term:1024
  b_coercion:term:1024
  : tactic => `(tactic| exact term_derivation_mul_eq $a_nf $b_nf $d $a_coercion $b_coercion)

theorem term_derivation_div_eq {α β γ} {a term_a : α} {b term_b:β} {a1 b1 term_a1 term_b1 term: γ}
  [Field γ]
  (ha0: a = term_a)
  (hb0: b = term_b)
  (a_coercion: a = term_a -> a1 = term_a1)
  (b_coercion: b = term_b -> b1 = term_b1)
  (hab: term_a1 / term_b1 = term)
  : a1 / b1 = term := by
  have ha : a1 = term_a1 := a_coercion ha0
  have hb : b1 = term_b1 := b_coercion hb0
  rw [ha, hb]
  exact hab

macro "term_derivation_div_eq"
  a_nf:term:1024
  b_nf:term:1024
  a_coercion:term:1024
  b_coercion:term:1024
  d:term:1024
  : tactic => `(tactic| exact term_derivation_div_eq $a_nf $b_nf $a_coercion $b_coercion $d)

macro "term_derivation_literal_mul_literal" : tactic => `(tactic| norm_num)

macro "term_derivation_neg_atom" : tactic => `(tactic| simp)

macro "term_derivation_neg_product" : tactic => `(tactic| simp)

macro "term_derivation_neg_eq" : tactic => `(tactic| simp)

theorem term_derivation_mul_product
  {αβ αβγ}
  {a_αβ b_αβ ab_term: αβ}
  {a_αβγ b_αβγ ab_term_αβγ c_αβγ abc_term bc_αβγ a_αβ_mul_b_αβ_αβγ : αβγ}
  [CommRing αβ]
  [CommRing αβγ]
  (hab: a_αβ * b_αβ = ab_term)
  (habc: ab_term_αβγ * c_αβγ = abc_term)
  (hab_eq_coercion: a_αβ * b_αβ = ab_term -> a_αβ_mul_b_αβ_αβγ = ab_term_αβγ)
  (hab_mul_coercion: a_αβ_mul_b_αβ_αβγ = a_αβγ * b_αβγ)
  (hbc_mul_coercion: bc_αβγ = b_αβγ * c_αβγ)
  : a_αβγ * bc_αβγ = abc_term := by
  rw [hbc_mul_coercion]
  have h: a_αβγ * b_αβγ * c_αβγ = a_αβγ * (b_αβγ * c_αβγ) := by ring
  rw [← h]
  have hab_coercion: a_αβ * b_αβ = ab_term -> a_αβγ * b_αβγ = ab_term_αβγ := by
    intro h
    have h: a_αβ_mul_b_αβ_αβγ = ab_term_αβγ := hab_eq_coercion h
    rw [← hab_mul_coercion]
    exact h
  rw [hab_coercion hab]
  exact habc

/-- derive `a * (b * c) => term` from `a * b => ab_term` and `ab_term * c => term` -/
macro "term_derivation_mul_product"
  hab:term:1024
  habc:term:1024
  hab_eq_coercion:term:1024
  hab_mul_coercion:term:1024
  hbc_mul_coercion:term:1024
  : tactic =>
  `(tactic| exact term_derivation_mul_product $hab $habc $hab_eq_coercion $hab_mul_coercion $hbc_mul_coercion)

theorem term_derivation_literal_mul_sum
  {π αβ βγ αγ αβγ}
  {p term0_π term_π : π}
  {a_αβ b_αβ ab_term : αβ}
  {a_αγ c_αγ ac_term : αγ}
  {b_αβγ c_αβγ b_add_c_αβγ term0 term : αβγ}
  {a_αβγ ac_term_αβγ ab_term_αβγ sum_of_b_and_c_pow_one_αβγ : αβγ}
  [CommRing π]
  [CommRing αβ]
  [CommRing βγ]
  [CommRing αγ]
  [CommRing αβγ]
  (hp0 : p = term0_π)
  (hterm0_mul_coercion : term0 = a_αβγ * sum_of_b_and_c_pow_one_αβγ)
  (hab_nf : a_αβ * b_αβ = ab_term)
  (hac_nf : a_αγ * c_αγ = ac_term)
  (habc_nf : ab_term_αβγ + ac_term_αβγ = term)
  (hpow_coercion : sum_of_b_and_c_pow_one_αβγ = b_add_c_αβγ ^ (1:ℕ))
  (hbc_coercion : b_add_c_αβγ = b_αβγ + c_αβγ)
  (hπ_coercion : term0 = term -> term0_π = term_π)
  (hab_coercion : a_αβ * b_αβ = ab_term -> a_αβγ * b_αβγ = ab_term_αβγ)
  (hac_coercion : a_αγ * c_αγ = ac_term -> a_αβγ * c_αβγ = ac_term_αβγ)
  : p = term_π := by
  have h: term0 = term := by
    rw[hterm0_mul_coercion]
    rw[hpow_coercion]
    rw[hbc_coercion]
    ring_nf
    rw[hab_coercion hab_nf]
    rw[hac_coercion hac_nf]
    exact habc_nf
  have h: term0_π = term_π := hπ_coercion h
  rw[← h]
  exact hp0

/-- derive `p => term` from `p => a * (b + c)^1` `a * b => ab_term` and `a * c => ac_term` and `ab_term + ac_term => term` -/
macro "term_derivation_literal_mul_sum" : tactic => `(tactic| simp)

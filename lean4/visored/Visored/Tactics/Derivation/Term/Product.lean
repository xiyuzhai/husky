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

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

theorem term_derivation_mul_product {α} {a b c ab_term term: α} [CommRing α]
  (hab: a * b = ab_term)
  (hc: ab_term * c = term)
  : a * (b * c) = term := by
  have h: a * b * c = term := by
    rw [hab]
    rw [hc]
  have h2: a * (b * c) = a * b * c := by
    ring
  rw [h2]
  exact h

/-- derive `a * (b * c) => term` from `a * b => ab_term` and `ab_term * c => term` -/
macro "term_derivation_mul_product" hab:term:1024 hc:term:1024 : tactic => `(tactic| exact term_derivation_mul_product $hab $hc)

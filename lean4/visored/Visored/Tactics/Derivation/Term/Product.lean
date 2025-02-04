import Mathlib

macro "term_derivation_power_one": tactic => `(tactic| simp)
macro "term_derivation_one_mul": tactic => `(tactic| simp)
macro "term_derivation_mul_one": tactic => `(tactic| simp)

theorem term_derivation_div_literal {α} {a b b_inv term : α} [Field α]
  (h: a * b_inv = term)
  (hb: b⁻¹ = b_inv) : a / b = term := by
  rw [← h]
  rw [← hb]
  ring

/-- derive `a / b => term` from `a * b⁻¹ => term` if `b` is a literal -/
macro "term_derivation_div_literal" h:term:1024 : tactic => `(tactic| exact term_derivation_div_literal $h (by norm_num))

theorem term_derivation_mul_eq {α β γ} {a term_a : α} {b term_b:β} {a1 b1 term_a1 term_b1 term: γ}
  [Field γ]
  (ha0: a = term_a)
  (hb0: b = term_b)
  (hab: term_a1 * term_b1 = term)
  (a_coercion: a = term_a ↔ a1 = term_a1)
  (b_coercion: b = term_b ↔ b1 = term_b1)
  : a1 * b1 = term := by
  have ha : a1 = term_a1 := a_coercion.mp ha0
  have hb : b1 = term_b1 := b_coercion.mp hb0
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
  (a_coercion: a = term_a ↔ a1 = term_a1)
  (b_coercion: b = term_b ↔ b1 = term_b1)
  (hab: term_a1 / term_b1 = term)
  : a1 / b1 = term := by
  have ha : a1 = term_a1 := a_coercion.mp ha0
  have hb : b1 = term_b1 := b_coercion.mp hb0
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

theorem term_derivation_neg_product
  {α}
  {a c neg_c : α}
  [CommRing α]
  (hc: -c = neg_c)
  : -(c * a) = neg_c *  a := by
  rw [← hc]
  simp

/-- derive `-(c * a) => (-c) * a` if `c` is a literal -/
macro "term_derivation_neg_product" : tactic => `(tactic| exact term_derivation_neg_product (by norm_num))

theorem term_derivation_neg_eq
  {α}
  {a term a_term : α}
  [Neg α]
  (ha: a = a_term)
  (hneg_a_term: -a_term = term)
  : -a = term := by
  rw [ha]
  exact hneg_a_term

/-- derive `-a => term` from `a => a_term` and `-a_term => term` -/
macro "term_derivation_neg_eq" ha:term:1024 hneg_a_term:term:1024 : tactic
  => `(tactic| exact term_derivation_neg_eq $ha $hneg_a_term)

theorem term_derivation_mul_product
  {αβ αβγ}
  {a_αβ b_αβ ab_term: αβ}
  {a_αβγ b_αβγ ab_term_αβγ c_αβγ abc_term bc_αβγ a_αβ_mul_b_αβ_αβγ : αβγ}
  [HMul αβ αβ αβ]
  [Semigroup αβγ]
  (hab: a_αβ * b_αβ = ab_term)
  (habc: ab_term_αβγ * c_αβγ = abc_term)
  (hab_eq_coercion: a_αβ * b_αβ = ab_term ↔ a_αβ_mul_b_αβ_αβγ = ab_term_αβγ)
  (hab_mul_coercion: a_αβ_mul_b_αβ_αβγ = a_αβγ * b_αβγ)
  (hbc_mul_coercion: bc_αβγ = b_αβγ * c_αβγ)
  : a_αβγ * bc_αβγ = abc_term := by
  rw [hbc_mul_coercion]
  have h: a_αβγ * b_αβγ * c_αβγ = a_αβγ * (b_αβγ * c_αβγ) := by apply mul_assoc
  rw [← h]
  have hab_coercion: a_αβ * b_αβ = ab_term → a_αβγ * b_αβγ = ab_term_αβγ := by
    intro h
    have h: a_αβ_mul_b_αβ_αβγ = ab_term_αβγ := hab_eq_coercion.mp h
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
  {π αβ αγ αβγ}
  {p term0_π term_π : π}
  {a_αβ b_αβ ab_term : αβ}
  {a_αγ c_αγ ac_term : αγ}
  {a_αβγ a_αβ_αβγ a_αγ_αβγ b_αβγ b_αβ_αβγ b_βγ_αβγ c_αβγ c_αγ_αβγ c_βγ_αβγ b_add_c_αβγ a_αβ_mul_b_αβ_αβγ a_αγ_mul_c_αγ_αβγ term ac_term_αβγ ab_term_αβγ sum_of_b_and_c_pow_one_αβγ : αβγ}
  [Mul αβ]
  [Mul αγ]
  [Semiring αβγ]
  (hp0 : p = term0_π)
  (hab_nf : a_αβ * b_αβ = ab_term)
  (hac_nf : a_αγ * c_αγ = ac_term)
  (habc_nf : ab_term_αβγ + ac_term_αβγ = term)
  (hpow_coercion : sum_of_b_and_c_pow_one_αβγ = b_add_c_αβγ ^ (1:ℕ))
  (hbc_coercion : b_add_c_αβγ = b_βγ_αβγ + c_βγ_αβγ)
  (hab_eq_coercion : a_αβ * b_αβ = ab_term ↔ a_αβ_mul_b_αβ_αβγ = ab_term_αβγ)
  (hab_mul_coercion : a_αβ_mul_b_αβ_αβγ = a_αβ_αβγ * b_αβ_αβγ)
  (hac_eq_coercion : a_αγ * c_αγ = ac_term ↔ a_αγ_mul_c_αγ_αβγ = ac_term_αβγ)
  (hac_mul_coercion : a_αγ_mul_c_αγ_αβγ = a_αγ_αβγ * c_αγ_αβγ)
  (ha_αβ_αβγ_coercion_triangle: a_αβ_αβγ = a_αβγ)
  (ha_αγ_αβγ_coercion_triangle: a_αγ_αβγ = a_αβγ)
  (hb_αβ_αβγ_coercion_triangle: b_αβ_αβγ = b_αβγ)
  (hb_βγ_αβγ_coercion_triangle: b_βγ_αβγ = b_αβγ)
  (hc_αγ_αβγ_coercion_triangle: c_αγ_αβγ = c_αβγ)
  (hc_βγ_αβγ_coercion_triangle: c_βγ_αβγ = c_αβγ)
  (hπ_coercion : a_αβγ * sum_of_b_and_c_pow_one_αβγ = term ↔ term0_π = term_π)
  : p = term_π := by
  have h: a_αβγ * sum_of_b_and_c_pow_one_αβγ = term := by
    rw[hpow_coercion]
    rw[hbc_coercion]
    ring_nf
    rw[hb_βγ_αβγ_coercion_triangle]
    rw[← hb_αβ_αβγ_coercion_triangle]
    rw[hc_βγ_αβγ_coercion_triangle]
    rw[← hc_αγ_αβγ_coercion_triangle]
    have hab_coercion : a_αβ * b_αβ = ab_term → a_αβ_αβγ * b_αβ_αβγ = ab_term_αβγ := by
      intro h
      have h: a_αβ_mul_b_αβ_αβγ = ab_term_αβγ := hab_eq_coercion.mp h
      rw[← hab_mul_coercion]
      exact h
    have hab_nf_coerced : a_αβ_αβγ * b_αβ_αβγ = ab_term_αβγ := hab_coercion hab_nf
    have hab_nf_coerced : a_αβγ * b_αβγ = ab_term_αβγ := by
      rw[← ha_αβ_αβγ_coercion_triangle]
      rw[← hb_αβ_αβγ_coercion_triangle]
      exact hab_nf_coerced
    have hac_coercion : a_αγ * c_αγ = ac_term → a_αγ_αβγ * c_αγ_αβγ = ac_term_αβγ := by
      intro h
      have h: a_αγ_mul_c_αγ_αβγ = ac_term_αβγ := hac_eq_coercion.mp h
      rw[← hac_mul_coercion]
      exact h
    have hac_nf_coerced : a_αγ_αβγ * c_αγ_αβγ = ac_term_αβγ := hac_coercion hac_nf
    have hac_nf_coerced : a_αβγ * c_αβγ = ac_term_αβγ := by
      rw[← ha_αγ_αβγ_coercion_triangle]
      rw[← hc_αγ_αβγ_coercion_triangle]
      exact hac_nf_coerced
    simp
    rw [left_distrib]
    rw [hb_αβ_αβγ_coercion_triangle]
    rw [hc_αγ_αβγ_coercion_triangle]
    rw [hab_nf_coerced]
    rw [hac_nf_coerced]
    exact habc_nf
  have h: term0_π = term_π := hπ_coercion.mp h
  rw[← h]
  exact hp0

/-- derive `p => term` from `p => a * (b + c)^1` `a * b => ab_term` and `a * c => ac_term` and `ab_term + ac_term => term` -/
macro "term_derivation_literal_mul_sum"
  hp0:term:1024
  hab_nf:term:1024
  hac_nf:term:1024
  habc_nf:term:1024
  hβγ_αβγ_pow_coercion:term:1024
  hbc_coercion:term:1024
  hαβ_αβγ_eq_coercion:term:1024
  hαβ_αβγ_mul_coercion:term:1024
  hαγ_αβγ_eq_coercion:term:1024
  hαγ_αβγ_mul_coercion:term:1024
  ha_αβ_αβγ_coercion_triangle:term:1024
  ha_αγ_αβγ_coercion_triangle:term:1024
  hb_αβ_αβγ_coercion_triangle:term:1024
  hb_βγ_αβγ_coercion_triangle:term:1024
  hc_αγ_αβγ_coercion_triangle:term:1024
  hc_βγ_αβγ_coercion_triangle:term:1024
  hπ_coercion:term:1024
  : tactic => `(tactic| exact term_derivation_literal_mul_sum $hp0 $hab_nf $hac_nf $habc_nf $hβγ_αβγ_pow_coercion $hbc_coercion $hαβ_αβγ_eq_coercion $hαβ_αβγ_mul_coercion $hαγ_αβγ_eq_coercion $hαγ_αβγ_mul_coercion $ha_αβ_αβγ_coercion_triangle $ha_αγ_αβγ_coercion_triangle $hb_αβ_αβγ_coercion_triangle $hb_βγ_αβγ_coercion_triangle $hc_αγ_αβγ_coercion_triangle $hc_βγ_αβγ_coercion_triangle $hπ_coercion)

theorem term_derivation_simple_product_mul_literal
  {αγδ}
  {c_mul_a_αγδ d_αγδ e_mul_a_αγδ c_αγ_αγδ a_αγ_αγδ e_αγδ e_αε_αγδ a_αε_αγδ a_αγδ : αγδ}
  [CommRing αγδ]
  (hc_mul_d_eqs_e: c_αγ_αγδ * d_αγδ = e_αγδ)
  (hc_mul_a_mul_coercion: c_mul_a_αγδ = c_αγ_αγδ * a_αγ_αγδ)
  (he_mul_a_mul_coercion: e_mul_a_αγδ = e_αε_αγδ * a_αε_αγδ)
  (ha_αε_αγδ_coercion_triangle : a_αε_αγδ = a_αγδ)
  (ha_αγ_αγδ_coercion_triangle : a_αγ_αγδ = a_αγδ)
  (he_αε_αγδ_coercion_triangle : e_αε_αγδ = e_αγδ)
  : c_mul_a_αγδ * d_αγδ = e_mul_a_αγδ := by
  rw [hc_mul_a_mul_coercion]
  have h : c_αγ_αγδ * a_αγ_αγδ * d_αγδ = (c_αγ_αγδ * d_αγδ) * a_αγ_αγδ := by ring
  rw [h]
  rw [he_mul_a_mul_coercion]
  rw [ha_αε_αγδ_coercion_triangle]
  rw [ha_αγ_αγδ_coercion_triangle]
  rw [he_αε_αγδ_coercion_triangle]
  rw [hc_mul_d_eqs_e]

/--
derive `(c * a) * d => e * a` if `c`, `d` and `e` are literals and `e` is equal to `c * d`
-/
macro "term_derivation_simple_product_mul_literal"
  hc_mul_a_mul_coercion:term:1024
  he_mul_a_mul_coercion:term:1024
  ha_αε_αγδ_coercion_triangle:term:1024
  ha_αγ_αγδ_coercion_triangle:term:1024
  he_αε_αγδ_coercion_triangle:term:1024
  : tactic => `(tactic| exact term_derivation_simple_product_mul_literal (by norm_num) $hc_mul_a_mul_coercion $he_mul_a_mul_coercion $ha_αε_αγδ_coercion_triangle $ha_αγ_αγδ_coercion_triangle $he_αε_αγδ_coercion_triangle)

macro "term_derivation_atom_mul_atom_less" : tactic => `(tactic| fail "not implemented")

macro "term_derivation_atom_mul_atom_equal" : tactic => `(tactic| fail "not implemented")

macro "term_derivation_atom_mul_atom_greater" : tactic => `(tactic| fail "not implemented")

macro "term_derivation_sqrt" : tactic => `(tactic| fail "not implemented")

macro "term_derivation_non_reduced_power" : tactic => `(tactic| fail "not implemented")

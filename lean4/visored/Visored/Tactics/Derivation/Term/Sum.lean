import Mathlib

theorem term_derivation_add_assoc {α} {a b c b_add_c a_add_b: α} [CommRing α]
  (hbc: b + c = b_add_c)
  (hab: a + b = a_add_b)
  : a + b_add_c = a_add_b + c := by
  rw [← hbc, ← hab]
  ring

theorem term_derivation_add_atom {α} {a b term: α} [CommRing α] (h: a + (1:ℕ) * b^1 = term) : a + b = term := by
  rw [←h]
  ring

/-- derive `a + b => term` from `a + 1 * b^1 => term` if `b` is an atom
-/
macro "term_derivation_add_atom" d:term : tactic => `(tactic| (exact term_derivation_add_atom $d))

example (x: ℝ) (d18: (-1 : ℝ) + ((1:ℕ) : ℝ) * x ^ 1 = (-1 : ℝ) + ((1:ℕ) : ℝ) * x ^ 1)
  : (-1 : ℝ) + x = (-1 : ℝ) + ((1:ℕ) : ℝ) * x ^ 1 := by
  term_derivation_add_atom d18

theorem term_derivation_atom_add_non_zero_literal {α} {a c: α} [CommRing α] : a + c = c + ((1 :ℕ) : α) * a^1 := by
  ring

/-- derive `a + c => c + 1 * a^1` if `a` is an atom and `c` is a litnum -/
macro "term_derivation_atom_add_non_zero_literal" : tactic => `(tactic| (exact term_derivation_atom_add_non_zero_literal))

example (x: ℝ) : x + 2 = 2 + ((1 :ℕ) : ℝ) * x^1 := by
  term_derivation_atom_add_non_zero_literal

theorem term_derivation_add_eq {α β γ} {a term_a :α} {b term_b:β} {a1 b1 term_a1 term_b1 term: γ}
  [CommRing γ]
  (ha0: a = term_a)
  (hb0: b = term_b)
  (a_coercion: a = term_a -> a1 = term_a1)
  (b_coercion: b = term_b -> b1 = term_b1)
  (hab: term_a1 + term_b1 = term)
  : a1 + b1 = term := by
  have ha : a1 = term_a1 := a_coercion ha0
  have hb : b1 = term_b1 := b_coercion hb0
  rw [ha, hb]
  exact hab

/-- derive `a + b => term` from `a => term_a`, `b => term_b` and `term_a + term_b => term`
-/
macro "term_derivation_add_eq" ha0:term:1024 hb0:term:1024 ca:term:1024 cb:term:1024 hab:term:1024 : tactic =>
  `(tactic| exact term_derivation_add_eq $ha0 $hb0 $ca $cb $hab)

theorem term_derivation_sub_eqs_add_neg {α} {a b' neg_b' term: α} [CommRing α] (h: a + neg_b' = term) (h2: neg_b' = -b' ) : a - b' = term := by
  rw [←h]
  rw [h2]
  ring

/-- derive `a - b => term` from `a + (-b) => term`
-/
macro "term_derivation_sub_eqs_add_neg" h_add_neg:term:1024 b_coercion:term:1024 : tactic => `(tactic| exact term_derivation_sub_eqs_add_neg $h_add_neg $b_coercion)

/-- derive `a + 0 => a` -/
macro "term_derivation_nf_add_zero": tactic => `(tactic| simp)

macro "term_derivation_literal_add_literal": tactic => `(tactic| norm_num)

macro "term_derivation_zero_add": tactic => `(tactic| simp)

theorem term_derivation_sum_add_literal
    {αγ αβγ}
    {a_αγ c_αγ ac_term : αγ}
    {a_αβγ b_αβγ ac_term_αβγ term a_add_b_αβγ a_add_c_αβγ c_αβγ a_αβ_αβγ a_αγ_αβγ c_αγ_αβγ b_αβ_αβγ: αβγ}
    [CommRing αγ] [CommRing αβγ]
    (hac : a_αγ + c_αγ = ac_term)
    (hacb : ac_term_αβγ + b_αβγ = term)
    (ha_add_b_αβγ_add_coercion : a_add_b_αβγ = a_αβ_αβγ + b_αβ_αβγ)
    (ha_αβ_αβγ_coercion_triangle : a_αβ_αβγ = a_αβγ)
    (hb_αβ_αβγ_coercion_triangle : b_αβ_αβγ = b_αβγ)
    (hac_eq_coercion : a_αγ + c_αγ = ac_term -> a_add_c_αβγ = ac_term_αβγ)
    (hac_αβγ_add_coercion : a_add_c_αβγ = a_αγ_αβγ + c_αγ_αβγ)
    (ha_αγ_αβγ_coercion_triangle : a_αγ_αβγ = a_αβγ)
    (hc_αγ_αβγ_coercion_triangle : c_αγ_αβγ = c_αβγ)
    : a_add_b_αβγ + c_αβγ = term := by
  rw [ha_add_b_αβγ_add_coercion]
  rw [ha_αβ_αβγ_coercion_triangle]
  rw [hb_αβ_αβγ_coercion_triangle]
  rw [add_comm]
  rw [← add_assoc]
  nth_rw 2 [add_comm]
  have h : a_add_c_αβγ = ac_term_αβγ := hac_eq_coercion hac
  have h : a_αβγ + c_αβγ = ac_term_αβγ := by
    rw [← ha_αγ_αβγ_coercion_triangle]
    rw [← hc_αγ_αβγ_coercion_triangle]
    rw [← hac_αβγ_add_coercion]
    exact h
  rw [h]
  exact hacb

/--
derive `a + b + c => term` from `a + c => ac_term` and `ac_term + b => term`
-/
macro "term_derivation_sum_add_literal"
  hac:term:1024
  hacb:term:1024
  ha_add_b_αβγ_add_coercion:term:1024
  ha_αβ_αβγ_coercion_triangle:term:1024
  hb_αβ_αβγ_coercion_triangle:term:1024
  hac_eq_coercion:term:1024
  ha_add_c_αβγ_add_coercion:term:1024
  ha_αγ_αβγ_coercion_triangle:term:1024
  hc_αγ_αβγ_coercion_triangle:term:1024
  : tactic => `(tactic| exact term_derivation_sum_add_literal $hac $hacb $ha_add_b_αβγ_add_coercion $ha_αβ_αβγ_coercion_triangle $hb_αβ_αβγ_coercion_triangle $hac_eq_coercion $ha_add_c_αβγ_add_coercion $ha_αγ_αβγ_coercion_triangle $hc_αγ_αβγ_coercion_triangle)

theorem term_derivation_product_add_literal {α} {p c: α} [CommRing α] : p + c = c + p := by
  ring

macro "term_derivation_product_add_literal": tactic => `(tactic| exact term_derivation_product_add_literal)

theorem term_derivation_base_mul_literal {α} {a c: α} [CommRing α] : a * c = c * a^1 := by
  ring

macro "term_derivation_base_mul_literal": tactic => `(tactic| exact term_derivation_base_mul_literal)

theorem term_derivation_one_mul_power_one {α} {a: α} [CommRing α] : ((1:ℕ) : α) * a^(1:ℕ) = a := by
  ring

macro "term_derivation_one_mul_power_one": tactic => `(tactic| exact term_derivation_one_mul_power_one)

theorem term_derivation_non_one_literal_mul_atom {α} {a c: α} [CommRing α] : c * a = c * a^(1:ℕ) := by
  ring

macro "term_derivation_non_one_literal_mul_atom": tactic => `(tactic| exact term_derivation_non_one_literal_mul_atom)

theorem term_derivation_product_add_product_less
  {αβ}
  {a_αβ b_αβ zero_add_a_αβ : αβ}
  [CommRing αβ]
  (hzero_add_a_add_coercion: zero_add_a_αβ = ((0:ℕ):αβ) + a_αβ)
  : a_αβ + b_αβ = zero_add_a_αβ + b_αβ := by
  rw [hzero_add_a_add_coercion]
  ring

/--
derive `a + b => 0 + a + b` if `a` and `b` are products and the stem of `a` is less than the stem of `b`
-/
macro "term_derivation_product_add_product_less" hzero_add_a_add_coercion:term:1024 : tactic => `(tactic| exact term_derivation_product_add_product_less $hzero_add_a_add_coercion)

theorem term_derivation_product_add_product_greater
  {αβ}
  {a_αβ b_αβ zero_add_b_αβ : αβ}
  [CommRing αβ]
  (hzero_add_b_add_coercion: zero_add_b_αβ = ((0:ℕ):αβ) + b_αβ)
  : a_αβ + b_αβ = zero_add_b_αβ + a_αβ := by
  rw [hzero_add_b_add_coercion]
  ring

/--
derive `a + b => 0 + b + a` if `a` and `b` are products and the stem of `a` is greater than the stem of `b`
-/
macro "term_derivation_product_add_product_greater" hzero_add_b_add_coercion:term:1024 : tactic => `(tactic| exact term_derivation_product_add_product_greater $hzero_add_b_add_coercion)

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

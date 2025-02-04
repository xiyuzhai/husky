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
  [Add γ]
  (ha0: a = term_a)
  (hb0: b = term_b)
  (a_coercion: a = term_a ↔ a1 = term_a1)
  (b_coercion: b = term_b ↔ b1 = term_b1)
  (hab: term_a1 + term_b1 = term)
  : a1 + b1 = term := by
  have ha : a1 = term_a1 := a_coercion.mp ha0
  have hb : b1 = term_b1 := b_coercion.mp hb0
  rw [ha, hb]
  exact hab

/-- derive `a + b => term` from `a => term_a`, `b => term_b` and `term_a + term_b => term`
-/
macro "term_derivation_add_eq" ha0:term:1024 hb0:term:1024 ca:term:1024 cb:term:1024 hab:term:1024 : tactic =>
  `(tactic| exact term_derivation_add_eq $ha0 $hb0 $ca $cb $hab)

theorem term_derivation_sub_eqs_add_neg {α} {a b' neg_b' term: α} [AddCommGroup α] (h: a + neg_b' = term) (h2: neg_b' = -b' ) : a - b' = term := by
  rw [←h]
  rw [h2]
  rw [← sub_eq_add_neg]

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
    [Add αγ] [AddCommSemigroup αβγ]
    (hac : a_αγ + c_αγ = ac_term)
    (hacb : ac_term_αβγ + b_αβγ = term)
    (ha_add_b_αβγ_add_coercion : a_add_b_αβγ = a_αβ_αβγ + b_αβ_αβγ)
    (ha_αβ_αβγ_coercion_triangle : a_αβ_αβγ = a_αβγ)
    (hb_αβ_αβγ_coercion_triangle : b_αβ_αβγ = b_αβγ)
    (hac_eq_coercion : a_αγ + c_αγ = ac_term ↔ a_add_c_αβγ = ac_term_αβγ)
    (hac_αβγ_add_coercion : a_add_c_αβγ = a_αγ_αβγ + c_αγ_αβγ)
    (ha_αγ_αβγ_coercion_triangle : a_αγ_αβγ = a_αβγ)
    (hc_αγ_αβγ_coercion_triangle : c_αγ_αβγ = c_αβγ)
    : a_add_b_αβγ + c_αβγ = term := by
  rw [ha_add_b_αβγ_add_coercion]
  rw [ha_αβ_αβγ_coercion_triangle]
  rw [hb_αβ_αβγ_coercion_triangle]
  rw [add_comm]
  have h : c_αβγ + a_αβγ + b_αβγ = c_αβγ + (a_αβγ + b_αβγ) := (add_assoc c_αβγ  a_αβγ  b_αβγ)
  have h :  c_αβγ + (a_αβγ + b_αβγ) = c_αβγ + a_αβγ + b_αβγ := by
    rw [← (add_assoc c_αβγ  a_αβγ  b_αβγ)]
  rw [← add_assoc]
  nth_rw 2 [add_comm]
  have h : a_add_c_αβγ = ac_term_αβγ := hac_eq_coercion.mp hac
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

theorem term_derivation_product_add_literal {α} {p c: α} [AddCommSemigroup α] : p + c = c + p := add_comm _ _

macro "term_derivation_product_add_literal": tactic => `(tactic| exact term_derivation_product_add_literal)

theorem term_derivation_base_mul_literal {α} {a c: α} [CommSemiring α] : a * c = c * a^1 := by
  ring

macro "term_derivation_base_mul_literal": tactic => `(tactic| exact term_derivation_base_mul_literal)

theorem term_derivation_one_mul_power_one {α} {a: α} [CommSemiring α] : ((1:ℕ) : α) * a^(1:ℕ) = a := by
  ring

macro "term_derivation_one_mul_power_one": tactic => `(tactic| exact term_derivation_one_mul_power_one)

theorem term_derivation_non_one_literal_mul_atom {α} {a c: α} [CommSemiring α] : c * a = c * a^(1:ℕ) := by
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

theorem term_derivation_atom_add_product_less
  {αβ}
  {one_α_αβ a_αβ a_pow_one_αβ b_αβ zero_add_one_mul_a_pow_one_αβ one_mul_a_pow_one_αβ : αβ}
  [CommSemiring αβ]
  (hzero_add_one_mul_a_pow_one_αβ_mul_coercion: zero_add_one_mul_a_pow_one_αβ = ((0:ℕ):αβ) + one_mul_a_pow_one_αβ)
  (hone_mul_a_pow_one_αβ_mul_coercion: one_mul_a_pow_one_αβ = one_α_αβ * a_pow_one_αβ)
  (hone_α_αβ_coercion_triangle: one_α_αβ = ((1:ℕ):αβ))
  (ha_pow_one_αβ_pow_coercion: a_pow_one_αβ = (a_αβ)^(1:ℕ))
  : a_αβ + b_αβ = zero_add_one_mul_a_pow_one_αβ + b_αβ := by
  rw [hzero_add_one_mul_a_pow_one_αβ_mul_coercion]
  rw [hone_mul_a_pow_one_αβ_mul_coercion]
  rw [hone_α_αβ_coercion_triangle]
  rw [ha_pow_one_αβ_pow_coercion]
  ring

/-- derive `a + b => 0 + 1 * a^1 + b` if `a` is an atom and `b` is a product with higher stem -/
macro "term_derivation_atom_add_product_less"
  hzero_add_one_mul_a_pow_one_αβ_mul_coercion:term:1024
  hone_mul_a_pow_one_αβ_mul_coercion:term:1024
  hone_α_αβ_coercion_triangle:term:1024
  ha_pow_one_αβ_pow_coercion:term:1024
  : tactic
  => `(tactic| exact term_derivation_atom_add_product_less $hzero_add_one_mul_a_pow_one_αβ_mul_coercion $hone_mul_a_pow_one_αβ_mul_coercion $hone_α_αβ_coercion_triangle $ha_pow_one_αβ_pow_coercion)

theorem term_derivation_sum_add_product_greater
    {αγ αβγ}
    {a_αγ c_αγ ac_term : αγ}
    {a_αβγ b_αβγ ac_term_αβγ term a_add_b_αβγ a_add_c_αβγ c_αβγ c_αγ_αβγ a_αβ_αβγ a_αγ_αβγ b_αβ_αβγ: αβγ}
    [Add αγ] [AddCommSemigroup αβγ]
    (hac : a_αγ + c_αγ = ac_term)
    (hacb : ac_term_αβγ + b_αβγ = term)
    (ha_add_b_αβγ_add_coercion : a_add_b_αβγ = a_αβ_αβγ + b_αβ_αβγ)
    (ha_αβ_αβγ_coercion_triangle : a_αβ_αβγ = a_αβγ)
    (hb_αβ_αβγ_coercion_triangle : b_αβ_αβγ = b_αβγ)
    (hac_eq_coercion : a_αγ + c_αγ = ac_term ↔ a_add_c_αβγ = ac_term_αβγ)
    (hac_αβγ_add_coercion : a_add_c_αβγ = a_αγ_αβγ + c_αγ_αβγ)
    (ha_αγ_αβγ_coercion_triangle : a_αγ_αβγ = a_αβγ)
    (hc_αγ_αβγ_coercion_triangle : c_αγ_αβγ = c_αβγ)
    : a_add_b_αβγ + c_αβγ = term := by
  rw [ha_add_b_αβγ_add_coercion]
  rw [ha_αβ_αβγ_coercion_triangle]
  rw [hb_αβ_αβγ_coercion_triangle]
  have h : a_add_c_αβγ = ac_term_αβγ := hac_eq_coercion.mp hac
  have h : a_αβγ + c_αβγ = ac_term_αβγ := by
    rw [← ha_αγ_αβγ_coercion_triangle]
    rw [← hc_αγ_αβγ_coercion_triangle]
    rw [← hac_αβγ_add_coercion]
    exact h
  rw [add_comm]
  rw [← add_assoc]
  nth_rw 2 [add_comm]
  rw [h]
  exact hacb

/-- derive `a + b + c => term` from `a + c => term_ac` and `term_ac + b => term` -/
macro "term_derivation_sum_add_product_greater"
  hac:term:1024
  hacb:term:1024
  ha_add_b_αβγ_add_coercion:term:1024
  ha_αβ_αβγ_coercion_triangle:term:1024
  hb_αβ_αβγ_coercion_triangle:term:1024
  hac_eq_coercion:term:1024
  ha_add_c_αβγ_add_coercion:term:1024
  ha_αγ_αβγ_coercion_triangle:term:1024
  hc_αγ_αβγ_coercion_triangle:term:1024
  : tactic => `(tactic| exact term_derivation_sum_add_product_greater $hac $hacb $ha_add_b_αβγ_add_coercion $ha_αβ_αβγ_coercion_triangle $hb_αβ_αβγ_coercion_triangle $hac_eq_coercion $ha_add_c_αβγ_add_coercion $ha_αγ_αβγ_coercion_triangle $hc_αγ_αβγ_coercion_triangle)

theorem term_derivation_neg_sum
  {α β αβ}
  {a neg_a_term : α}
  {b neg_b_term : β}
  {a_αβ b_αβ neg_a_αβ neg_b_αβ neg_a_term_αβ neg_b_term_αβ neg_a_term_add_neg_b_term_αβ: αβ}
  [Neg α] [Neg β] [CommRing αβ]
  (h_neg_a: -a = neg_a_term)
  (h_neg_b: -b = neg_b_term)
  (ha_eq_coercion: -a = neg_a_term ↔ neg_a_αβ = neg_a_term_αβ)
  (hb_eq_coercion: -b = neg_b_term ↔ neg_b_αβ = neg_b_term_αβ)
  (ha_neg_coercion: neg_a_αβ = -a_αβ)
  (hb_neg_coercion: neg_b_αβ = -b_αβ)
  (hneg_a_term_add_neg_b_term_αβ_add_coercion: neg_a_term_add_neg_b_term_αβ = neg_a_term_αβ + neg_b_term_αβ)
  : -(a_αβ + b_αβ) = neg_a_term_add_neg_b_term_αβ := by
  rw [neg_add]
  rw [← ha_neg_coercion]
  rw [← hb_neg_coercion]
  rw [hneg_a_term_add_neg_b_term_αβ_add_coercion]
  rw [← ha_eq_coercion.mp h_neg_a]
  rw [← hb_eq_coercion.mp h_neg_b]

/-- derive `-(a + b) => neg_a_term + neg_b_term` from `-a => neg_a_term` and `-b => neg_b_term` -/
macro "term_derivation_neg_sum"
  h_neg_a:term:1024
  h_neg_b:term:1024
  ha_eq_coercion:term:1024
  hb_eq_coercion:term:1024
  ha_neg_coercion:term:1024
  hb_neg_coercion:term:1024
  hneg_a_term_add_neg_b_term_αβ_add_coercion:term:1024
  : tactic => `(tactic| exact term_derivation_neg_sum $h_neg_a $h_neg_b $ha_eq_coercion $hb_eq_coercion $ha_neg_coercion $hb_neg_coercion $hneg_a_term_add_neg_b_term_αβ_add_coercion)

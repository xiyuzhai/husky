import Mathlib

-- triangles

theorem nat_nat_nat_coercion_triangle {a: ℕ} : ((a : ℕ) : ℕ) = (a : ℕ) := by simp
theorem nat_nat_int_coercion_triangle {a: ℕ} : ((a : ℕ) : ℤ) = (a : ℤ) := by simp
theorem nat_nat_rat_coercion_triangle {a: ℕ} : ((a : ℕ) : ℚ) = (a : ℚ) := by simp
theorem nat_nat_real_coercion_triangle {a: ℕ} : ((a : ℕ) : ℝ) = (a : ℝ) := by simp
theorem nat_nat_complex_coercion_triangle {a: ℕ} : ((a : ℕ) : ℂ) = (a : ℂ) := by simp

theorem nat_int_int_coercion_triangle {a: ℕ} : ((a : ℤ) : ℤ) = (a : ℤ) := by simp
theorem nat_int_rat_coercion_triangle {a: ℕ} : ((a : ℤ) : ℚ) = (a : ℚ) := by simp
theorem nat_int_real_coercion_triangle {a: ℕ} : ((a : ℤ) : ℝ) = (a : ℝ) := by simp
theorem nat_int_complex_coercion_triangle {a: ℕ} : ((a : ℤ) : ℂ) = (a : ℂ) := by simp

theorem nat_rat_rat_coercion_triangle {a: ℕ} : ((a : ℚ) : ℚ) = (a : ℚ) := by simp
theorem nat_rat_real_coercion_triangle {a: ℕ} : ((a : ℚ) : ℝ) = (a : ℝ) := by simp
theorem nat_rat_complex_coercion_triangle {a: ℕ} : ((a : ℚ) : ℂ) = (a : ℂ) := by simp

theorem nat_real_real_coercion_triangle {a: ℕ} : ((a : ℝ) : ℝ) = (a : ℝ) := by simp
theorem nat_real_complex_coercion_triangle {a: ℕ} : ((a : ℝ) : ℂ) = (a : ℂ) := by simp

theorem nat_complex_complex_coercion_triangle {a: ℕ} : ((a : ℂ) : ℂ) = (a : ℂ) := by simp

theorem int_int_int_coercion_triangle {a: ℤ} : ((a : ℤ) : ℤ) = (a : ℤ) := by simp
theorem int_int_rat_coercion_triangle {a: ℤ} : ((a : ℤ) : ℚ) = (a : ℚ) := by simp
theorem int_int_real_coercion_triangle {a: ℤ} : ((a : ℤ) : ℝ) = (a : ℝ) := by simp
theorem int_int_complex_coercion_triangle {a: ℤ} : ((a : ℤ) : ℂ) = (a : ℂ) := by simp

theorem int_rat_rat_coercion_triangle {a: ℤ} : ((a : ℚ) : ℚ) = (a : ℚ) := by simp
theorem int_rat_real_coercion_triangle {a: ℤ} : ((a : ℚ) : ℝ) = (a : ℝ) := by simp
theorem int_rat_complex_coercion_triangle {a: ℤ} : ((a : ℚ) : ℂ) = (a : ℂ) := by simp

theorem int_real_real_coercion_triangle {a: ℤ} : ((a : ℝ) : ℝ) = (a : ℝ) := by simp
theorem int_real_complex_coercion_triangle {a: ℤ} : ((a : ℝ) : ℂ) = (a : ℂ) := by simp

theorem int_complex_complex_coercion_triangle {a: ℤ} : ((a : ℂ) : ℂ) = (a : ℂ) := by simp

theorem rat_rat_rat_coercion_triangle {a: ℚ} : ((a : ℚ) : ℚ) = (a : ℚ) := by simp
theorem rat_rat_real_coercion_triangle {a: ℚ} : ((a : ℚ) : ℝ) = (a : ℝ) := by simp
theorem rat_rat_complex_coercion_triangle {a: ℚ} : ((a : ℚ) : ℂ) = (a : ℂ) := by simp

theorem rat_real_real_coercion_triangle {a: ℚ} : ((a : ℝ) : ℝ) = (a : ℝ) := by simp
theorem rat_real_complex_coercion_triangle {a: ℚ} : ((a : ℝ) : ℂ) = (a : ℂ) := by simp

theorem rat_complex_complex_coercion_triangle {a: ℚ} : ((a : ℂ) : ℂ) = (a : ℂ) := by simp

theorem real_real_real_coercion_triangle {a: ℝ} : ((a : ℝ) : ℝ) = (a : ℝ) := by simp
theorem real_real_complex_coercion_triangle {a: ℝ} : ((a : ℝ) : ℂ) = (a : ℂ) := by simp

theorem real_complex_complex_coercion_triangle {a: ℝ} : ((a : ℂ) : ℂ) = (a : ℂ) := by simp

theorem complex_complex_complex_coercion_triangle {a: ℂ} : ((a : ℂ) : ℂ) = (a : ℂ) := by simp

-- Equality coercions

theorem eq_identity_coercion {α} {a b : α} : a = b -> a = b := by
  intro h
  exact h

theorem eq_nat_to_int_coercion {a b : ℕ} : a = b -> (a : ℤ) = (b : ℤ) := by
  intro h
  rw [h]

theorem eq_nat_to_rat_coercion {a b : ℕ} : a = b -> (a : ℚ) = (b : ℚ) := by
  intro h
  rw [h]

theorem eq_nat_to_real_coercion {a b : ℕ} : a = b -> (a : ℝ) = (b : ℝ) := by
  intro h
  rw [h]

theorem eq_nat_to_complex_coercion {a b : ℕ} : a = b -> (a : ℂ) = (b : ℂ) := by
  intro h
  rw [h]

theorem eq_int_to_rat_coercion {a b : ℤ} : a = b -> (a : ℚ) = (b : ℚ) := by
  intro h
  rw [h]

theorem eq_int_to_real_coercion {a b : ℤ} : a = b -> (a : ℝ) = (b : ℝ) := by
  intro h
  rw [h]

theorem eq_int_to_complex_coercion {a b : ℤ} : a = b -> (a : ℂ) = (b : ℂ) := by
  intro h
  rw [h]

theorem eq_rat_to_real_coercion {a b : ℚ} : a = b -> (a : ℝ) = (b : ℝ) := by
  intro h
  rw [h]

theorem eq_rat_to_complex_coercion {a b : ℚ} : a = b -> (a : ℂ) = (b : ℂ) := by
  intro h
  rw [h]

theorem eq_real_to_complex_coercion {a b : ℝ} : a = b -> (a : ℂ) = (b : ℂ) := by
  intro h
  rw [h]

-- Negation coercions

theorem neg_identity_coercion {α} {a : α} [Neg α] : (-a) = (-a) := by
  rfl

theorem neg_nat_to_int_coercion {a : ℕ} : (-(a : ℤ)) = (-(a : ℤ) : ℤ) := by simp

theorem neg_nat_to_rat_coercion {a : ℕ} : ((-(a : ℤ) : ℤ) : ℚ) = -(a : ℚ) := by simp

theorem neg_nat_to_real_coercion {a : ℕ} : ((-(a : ℤ) : ℤ) : ℝ) = -(a : ℝ) := by simp

theorem neg_nat_to_complex_coercion {a : ℕ} : ((-(a : ℤ) : ℤ) : ℂ) = -(a : ℂ) := by simp

theorem neg_int_to_rat_coercion {a : ℤ} : ((-a: ℤ) : ℚ) = -(a : ℚ) := by simp

theorem neg_int_to_real_coercion {a : ℤ} : ((-a: ℤ) : ℝ) = -(a : ℝ) := by simp

theorem neg_int_to_complex_coercion {a : ℤ} : ((-a: ℤ) : ℂ) = -(a : ℂ) := by simp

theorem neg_rat_to_real_coercion {a : ℚ} : ((-a: ℚ) : ℝ) = -(a : ℝ) := by simp

theorem neg_rat_to_complex_coercion {a : ℚ} : ((-a: ℚ) : ℂ) = -(a : ℂ) := by simp

theorem neg_real_to_complex_coercion {a : ℝ} : ((-a: ℝ) : ℂ) = -(a : ℂ) := by simp

-- Addition coercions

theorem comm_ring_add_identity_coercion {α} {a b : α} [CommRing α] : a + b = a + b := by
  rfl

theorem comm_ring_add_nat_to_int_coercion {a b : ℕ} : (a + b : ℤ) = (a : ℤ) + (b : ℤ) := by ring

theorem comm_ring_add_nat_to_rat_coercion {a b : ℕ} : (a + b : ℚ) = (a : ℚ) + (b : ℚ) := by ring

theorem comm_ring_add_nat_to_real_coercion {a b : ℕ} : (a + b : ℝ) = (a : ℝ) + (b : ℝ) := by ring

theorem comm_ring_add_nat_to_complex_coercion {a b : ℕ} : (a + b : ℂ) = (a : ℂ) + (b : ℂ) := by ring

theorem comm_ring_add_int_to_rat_coercion {a b : ℤ} : (a + b : ℚ) = (a : ℚ) + (b : ℚ) := by ring

theorem comm_ring_add_int_to_real_coercion {a b : ℤ} : (a + b : ℝ) = (a : ℝ) + (b : ℝ) := by ring

theorem comm_ring_add_int_to_complex_coercion {a b : ℤ} : (a + b : ℂ) = (a : ℂ) + (b : ℂ) := by ring

theorem comm_ring_add_rat_to_real_coercion {a b : ℚ} : (a + b : ℝ) = (a : ℝ) + (b : ℝ) := by ring

theorem comm_ring_add_rat_to_complex_coercion {a b : ℚ} : (a + b : ℂ) = (a : ℂ) + (b : ℂ) := by ring

theorem comm_ring_add_real_to_complex_coercion {a b : ℝ} : (a + b : ℂ) = (a : ℂ) + (b : ℂ) := by ring

-- Multiplication coercions

theorem comm_ring_mul_identity_coercion {α} {a b : α} [CommRing α] : a * b = a * b := by
  rfl

theorem comm_ring_mul_nat_to_int_coercion {a b : ℕ} : ((a * b: ℕ) : ℤ) = (a : ℤ) * (b : ℤ) := by simp

theorem comm_ring_mul_nat_to_rat_coercion {a b : ℕ} : ((a * b : ℕ) : ℚ) = (a : ℚ) * (b : ℚ) := by simp

theorem comm_ring_mul_nat_to_real_coercion {a b : ℕ} : ((a * b : ℕ) : ℝ) = (a : ℝ) * (b : ℝ) := by simp

theorem comm_ring_mul_nat_to_complex_coercion {a b : ℕ} : ((a * b : ℕ) : ℂ) = (a : ℂ) * (b : ℂ) := by simp

theorem comm_ring_mul_int_to_rat_coercion {a b : ℤ} : ((a * b : ℤ) : ℚ) = (a : ℚ) * (b : ℚ) := by simp

theorem comm_ring_mul_int_to_real_coercion {a b : ℤ} : ((a * b : ℤ) : ℝ) = (a : ℝ) * (b : ℝ) := by simp

theorem comm_ring_mul_int_to_complex_coercion {a b : ℤ} : ((a * b : ℤ) : ℂ) = (a : ℂ) * (b : ℂ) := by simp

theorem comm_ring_mul_rat_to_real_coercion {a b : ℚ} : ((a * b : ℚ) : ℝ) = (a : ℝ) * (b : ℝ) := by simp

theorem comm_ring_mul_rat_to_complex_coercion {a b : ℚ} : ((a * b : ℚ) : ℂ) = (a : ℂ) * (b : ℂ) := by simp

theorem comm_ring_mul_real_to_complex_coercion {a b : ℝ} : ((a * b : ℝ) : ℂ) = (a : ℂ) * (b : ℂ) := by simp

-- Commutative field coercions

theorem comm_field_div_identity_coercion {α} {a b : α} [Field α] : (a / b) = (a / b) := by
  rfl

theorem comm_field_div_nat_to_rat_coercion {a b : ℕ} : (a : ℚ) / (b : ℚ) = (a / b : ℚ) := by
  rfl

theorem comm_field_div_nat_to_real_coercion {a b : ℕ} : (a : ℝ) / (b : ℝ) = (a / b : ℝ) := by
  rfl

theorem comm_field_div_nat_to_complex_coercion {a b : ℕ} : (a : ℂ) / (b : ℂ) = (a / b : ℂ) := by
  rfl

theorem comm_field_div_int_to_rat_coercion {a b : ℤ} : (a : ℚ) / (b : ℚ) = (a / b : ℚ) := by
  rfl

theorem comm_field_div_int_to_real_coercion {a b : ℤ} : (a : ℝ) / (b : ℝ) = (a / b : ℝ) := by
  rfl

theorem comm_field_div_int_to_complex_coercion {a b : ℤ} : (a : ℂ) / (b : ℂ) = (a / b : ℂ) := by
  rfl

theorem comm_field_div_rat_to_real_coercion {a b : ℚ} : (a : ℝ) / (b : ℝ) = (a / b : ℝ) := by
  rfl

theorem comm_field_div_rat_to_complex_coercion {a b : ℚ} : (a : ℂ) / (b : ℂ) = (a / b : ℂ) := by
  rfl

theorem comm_field_div_real_to_complex_coercion {a b : ℝ} : (a : ℂ) / (b : ℂ) = (a / b : ℂ) := by
  rfl

-- pow

theorem real_pow_nat_to_real_pow_nat_coercion {a : ℝ} {i : ℕ} : (a ^ i : ℝ) = ((a : ℝ) ^ (i : ℕ) : ℝ) := by simp

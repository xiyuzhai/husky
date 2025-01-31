import Mathlib

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

theorem eq_int_to_real_coercion {a b : ℤ} : a = b -> (a : ℝ) = (b : ℝ) := by
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

theorem add_nat_to_int_coercion {a b : ℕ} : (a + b : ℤ) = (a : ℤ) + (b : ℤ) := by ring

theorem add_nat_to_rat_coercion {a b : ℕ} : (a + b : ℚ) = (a : ℚ) + (b : ℚ) := by ring

theorem add_nat_to_real_coercion {a b : ℕ} : (a + b : ℝ) = (a : ℝ) + (b : ℝ) := by ring

theorem add_nat_to_complex_coercion {a b : ℕ} : (a + b : ℂ) = (a : ℂ) + (b : ℂ) := by ring

theorem add_int_to_rat_coercion {a b : ℤ} : (a + b : ℚ) = (a : ℚ) + (b : ℚ) := by ring

theorem add_int_to_real_coercion {a b : ℤ} : (a + b : ℝ) = (a : ℝ) + (b : ℝ) := by ring

theorem add_int_to_complex_coercion {a b : ℤ} : (a + b : ℂ) = (a : ℂ) + (b : ℂ) := by ring

theorem add_rat_to_real_coercion {a b : ℚ} : (a + b : ℝ) = (a : ℝ) + (b : ℝ) := by ring

theorem add_rat_to_complex_coercion {a b : ℚ} : (a + b : ℂ) = (a : ℂ) + (b : ℂ) := by ring

theorem add_real_to_complex_coercion {a b : ℝ} : (a + b : ℂ) = (a : ℂ) + (b : ℂ) := by ring

-- Multiplication coercions

theorem mul_nat_to_int_coercion {a b : ℕ} : (a * b : ℤ) = (a : ℤ) * (b : ℤ) := by ring

theorem mul_nat_to_rat_coercion {a b : ℕ} : (a * b : ℚ) = (a : ℚ) * (b : ℚ) := by ring

theorem mul_nat_to_real_coercion {a b : ℕ} : (a * b : ℝ) = (a : ℝ) * (b : ℝ) := by ring

theorem mul_nat_to_complex_coercion {a b : ℕ} : (a * b : ℂ) = (a : ℂ) * (b : ℂ) := by ring

theorem mul_int_to_rat_coercion {a b : ℤ} : (a * b : ℚ) = (a : ℚ) * (b : ℚ) := by ring

theorem mul_int_to_real_coercion {a b : ℤ} : (a * b : ℝ) = (a : ℝ) * (b : ℝ) := by ring

theorem mul_int_to_complex_coercion {a b : ℤ} : (a * b : ℂ) = (a : ℂ) * (b : ℂ) := by ring

theorem mul_rat_to_real_coercion {a b : ℚ} : (a * b : ℝ) = (a : ℝ) * (b : ℝ) := by ring

theorem mul_rat_to_complex_coercion {a b : ℚ} : (a * b : ℂ) = (a : ℂ) * (b : ℂ) := by ring

theorem mul_real_to_complex_coercion {a b : ℝ} : (a * b : ℂ) = (a : ℂ) * (b : ℂ) := by ring

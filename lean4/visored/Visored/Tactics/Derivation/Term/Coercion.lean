import Mathlib

-- Equality coercions

theorem eq_identity_coercion {α} {a : α} : a = a -> a = a := by
  simp

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

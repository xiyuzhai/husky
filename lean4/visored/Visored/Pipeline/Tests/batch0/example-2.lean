import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h (x : ℝ) (h1 : x ≥ ((0:ℕ) : ℝ)) (y : ℝ) (h2 : y ≥ ((0:ℕ) : ℝ)) : ((x + y : ℝ) / ((2:ℕ) : ℝ) : ℝ) ≥ √ (x * y : ℝ) := by
  have h3 : ((√ x - √ y : ℝ) ^ (2:ℕ) : ℝ) = (((√ x ^ (2:ℕ) : ℝ) - ((((2:ℕ) : ℝ) * √ x : ℝ) * √ y : ℝ) : ℝ) + (√ y ^ (2:ℕ) : ℝ) : ℝ) := by obvious
  have h4 : (((√ x ^ (2:ℕ) : ℝ) - ((((2:ℕ) : ℝ) * √ x : ℝ) * √ y : ℝ) : ℝ) + (√ y ^ (2:ℕ) : ℝ) : ℝ) = ((x - (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) : ℝ) + y : ℝ) := by obvious
  have h5 : ((x - (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) : ℝ) + y : ℝ) ≥ ((0:ℕ) : ℝ) := by obvious
  have h6 : ((√ x - √ y : ℝ) ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    simp
    apply sq_nonneg
  have h7 : (x + y : ℝ) ≥ (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d2 : x = x := by term_derivation_reflection
    have d3 : y = y := by term_derivation_reflection
    have d4 : (x * y : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_atom_less
    have d5 : (x * y : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_identity_coercion eq_identity_coercion
    have d6 : √ (x * y : ℝ) = (((1:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_sqrt
    have d7 : ((2:ℕ) * (1:ℕ) : ℕ) = (2:ℕ) := by term_derivation_mul_one
    have d8 : (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_reflection
    have d9 : (((2:ℕ) : ℝ) * (((1:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_mul_product d7 d8 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d10 : (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_mul_eq d1 d6 d9 eq_nat_to_real_coercion eq_identity_coercion
    have d11 : (-(((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_neg_product
    have d12 : (-(((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_neg_eq d10 d11
    have d13 : (x + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product_less comm_ring_add_identity_coercion comm_ring_mul_identity_coercion nat_real_real_coercion_triangle real_pow_nat_to_real_pow_nat_coercion
    have d14 : (x + (-(((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d12 eq_identity_coercion eq_identity_coercion d13
    have d15 : (x - (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_identity_coercion
    have d16 : y = y := by term_derivation_reflection
    have d17 : ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d18 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_product_greater
    have d20 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) + y : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d19
    have d21 : ((x - (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) : ℝ) + y : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_identity_coercion d20
    have d22 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d26 : (((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d27 : y = y := by term_derivation_reflection
    have d28 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d29 : (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d30 : (x + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product_less comm_ring_add_identity_coercion comm_ring_mul_identity_coercion nat_real_real_coercion_triangle real_pow_nat_to_real_pow_nat_coercion
    have d31 : (x + y : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d30
    have d32 : ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d26 d29 eq_identity_coercion eq_identity_coercion d31
    have d33 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d34 : x = x := by term_derivation_reflection
    have d35 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d36 : y = y := by term_derivation_reflection
    have d37 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d38 : (x * y : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_atom_less
    have d39 : ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_eq d35 d37 d38 eq_identity_coercion eq_identity_coercion
    have d40 : (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_one_mul
    have d41 : ((1:ℚ)/2:ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_reflection
    have d42 : ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) = (((1:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_non_reduced_power
    have d43 : ((-2:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_mul_one
    have d44 : (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_reflection
    have d45 : (((-2:ℤ) : ℝ) * (((1:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_mul_product d43 d44 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d46 : (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_mul_eq d33 d42 d45 eq_int_to_real_coercion eq_identity_coercion
    have d47 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d48 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d32 d46 eq_identity_coercion eq_identity_coercion d47
    have d49 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d50 : ((((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d51 : ((((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d48 d49 eq_identity_coercion eq_int_to_real_coercion d50
    have d52 : ((((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d51 neg_nat_to_real_coercion
    have d53 : ((x - (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) : ℝ) + y : ℝ) ≥ ((0:ℕ) : ℝ) ↔ (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d54 : x = x := by term_derivation_reflection
    have d55 : y = y := by term_derivation_reflection
    have d56 : (x + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product_less comm_ring_add_identity_coercion comm_ring_mul_identity_coercion nat_real_real_coercion_triangle real_pow_nat_to_real_pow_nat_coercion
    have d57 : (x + y : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d56
    have d58 : (x + y : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d54 d55 eq_identity_coercion eq_identity_coercion d57
    have d59 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d60 : x = x := by term_derivation_reflection
    have d61 : y = y := by term_derivation_reflection
    have d62 : (x * y : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_atom_less
    have d63 : (x * y : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_eq d60 d61 d62 eq_identity_coercion eq_identity_coercion
    have d64 : √ (x * y : ℝ) = (((1:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_sqrt
    have d65 : ((2:ℕ) * (1:ℕ) : ℕ) = (2:ℕ) := by term_derivation_mul_one
    have d66 : (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_reflection
    have d67 : (((2:ℕ) : ℝ) * (((1:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_mul_product d65 d66 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d68 : (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_mul_eq d59 d64 d67 eq_nat_to_real_coercion eq_identity_coercion
    have d69 : x = x := by term_derivation_reflection
    have d70 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d71 : (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d72 : (((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d73 : y = y := by term_derivation_reflection
    have d74 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d75 : (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d76 : (x + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product_less comm_ring_add_identity_coercion comm_ring_mul_identity_coercion nat_real_real_coercion_triangle real_pow_nat_to_real_pow_nat_coercion
    have d77 : (x + y : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d76
    have d78 : ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d72 d75 eq_identity_coercion eq_identity_coercion d77
    have d79 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d80 : x = x := by term_derivation_reflection
    have d81 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d82 : y = y := by term_derivation_reflection
    have d83 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d84 : (x * y : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_atom_less
    have d85 : ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_eq d81 d83 d84 eq_identity_coercion eq_identity_coercion
    have d86 : (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_one_mul
    have d87 : ((1:ℚ)/2:ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_reflection
    have d88 : ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) = (((1:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_non_reduced_power
    have d89 : ((2:ℕ) * (1:ℕ) : ℕ) = (2:ℕ) := by term_derivation_mul_one
    have d90 : (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_reflection
    have d91 : (((2:ℕ) : ℝ) * (((1:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_mul_product d89 d90 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d92 : (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) = (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_mul_eq d79 d88 d91 eq_nat_to_real_coercion eq_identity_coercion
    have d93 : (-(((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_neg_product
    have d94 : (-(((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) := by term_derivation_neg_eq d92 d93
    have d95 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d96 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (-(((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d78 d94 eq_identity_coercion eq_identity_coercion d95
    have d97 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) - (((2:ℕ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) = (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d96 neg_identity_coercion
    have d98 : (x + y : ℝ) ≥ (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) ↔ (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℤ) : ℝ) * ((((1:ℕ) : ℝ) * ((x ^ (1:ℕ) : ℝ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (((1:ℚ)/2:ℚ)) : ℝ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d99 : (x + y : ℝ) ≥ (((2:ℕ) : ℝ) * √ (x * y : ℝ) : ℝ) := by term_derivation_non_trivial_hypothesis_equivalence h5 d53 d98
    assumption
  have h8 : ((x + y : ℝ) / ((2:ℕ) : ℝ) : ℝ) ≥ √ (x * y : ℝ) := by obvious
  obvious

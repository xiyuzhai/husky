import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h (a b : ℝ) (h1 : a > ((0:ℕ) : ℝ)) (h2 : b > ((0:ℕ) : ℝ)) : ((a / b : ℝ) + (b / a : ℝ) : ℝ) ≥ ((2:ℕ) : ℝ) := by
  have h1 : a > ((0:ℕ) : ℝ) := by old_main_hypothesis
  have h2 : b > ((0:ℕ) : ℝ) := by old_main_hypothesis
  first
  | have h3 : ((√ (a / b : ℝ) - √ (b / a : ℝ) : ℝ) ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    ((√ (a / b : ℝ) - √ (b / a : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((√ (a / b : ℝ) ^ (2:ℕ) : ℝ) - ((((2:ℕ) : ℝ) * √ (a / b : ℝ) : ℝ) * √ (b / a : ℝ) : ℝ) : ℝ) + (√ (b / a : ℝ) ^ (2:ℕ) : ℝ) : ℝ) := by obvious
    _ = (((a / b : ℝ) - ((2:ℕ) : ℝ) : ℝ) + (b / a : ℝ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  | have h4 : (((a / b : ℝ) - ((2:ℕ) : ℝ) : ℝ) + (b / a : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    (((a / b : ℝ) - ((2:ℕ) : ℝ) : ℝ) + (b / a : ℝ) : ℝ) = (((√ (a / b : ℝ) ^ (2:ℕ) : ℝ) - ((((2:ℕ) : ℝ) * √ (a / b : ℝ) : ℝ) * √ (b / a : ℝ) : ℝ) : ℝ) + (√ (b / a : ℝ) ^ (2:ℕ) : ℝ) : ℝ) := by obvious
    _ = ((√ (a / b : ℝ) - √ (b / a : ℝ) : ℝ) ^ (2:ℕ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  have h5 : (((a / b : ℝ) - ((2:ℕ) : ℝ) : ℝ) + (b / a : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by obvious
  have h6 : ((a / b : ℝ) + (b / a : ℝ) : ℝ) ≥ ((2:ℕ) : ℝ) := by
    have d : a = a := by term_derivation_reflection
    have d1 : b = b := by term_derivation_reflection
    have d2 : (a * (b ^ (-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_exponential_greater real_pow_nat_to_real_pow_nat_coercion
    have d3 : (a / b : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_atom d2
    have d4 : (a / b : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d d1 eq_identity_coercion eq_identity_coercion d3
    have d5 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d6 : ((((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d7 : ((a / b : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d6
    have d8 : ((a / b : ℝ) - ((2:ℕ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d7 neg_nat_to_real_coercion
    have d9 : b = b := by term_derivation_reflection
    have d10 : a = a := by term_derivation_reflection
    have d11 : (b * (a ^ (-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_exponential_less real_pow_nat_to_real_pow_nat_coercion
    have d12 : (b / a : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_atom d11
    have d13 : (b / a : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_identity_coercion d12
    have d14 : ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d15 : (((a / b : ℝ) - ((2:ℕ) : ℝ) : ℝ) + (b / a : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d8 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d17 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d18 : b = b := by term_derivation_reflection
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : (b ^ (-1:ℤ) : ℝ) = (((1:ℕ) : ℝ) * (b ^ (-1:ℤ) : ℝ) : ℝ) := by term_derivation_non_reduced_power d18 d19
    have d21 : a = a := by term_derivation_reflection
    have d22 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d23 : ((((1:ℕ) : ℝ) * (b ^ (-1:ℤ) : ℝ) : ℝ) * a : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_base_less
    have d24 : ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_eq d20 d22 d23 eq_identity_coercion eq_identity_coercion
    have d25 : (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_one_mul
    have d26 : (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d27 : (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d25 eq_int_to_real_coercion eq_identity_coercion d26
    have d28 : b = b := by term_derivation_reflection
    have d29 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d30 : a = a := by term_derivation_reflection
    have d31 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d32 : (a ^ (-1:ℤ) : ℝ) = (((1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) := by term_derivation_non_reduced_power d30 d31
    have d33 : (b * ((1:ℕ) : ℝ) : ℝ) = b := by term_derivation_mul_one
    have d34 : (b * (a ^ (-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_exponential_less real_pow_nat_to_real_pow_nat_coercion
    have d35 : (b * (((1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_product d33 d34 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d36 : ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_eq d29 d32 d35 eq_identity_coercion eq_identity_coercion
    have d37 : (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_one_mul
    have d38 : ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d27 d37 eq_identity_coercion eq_identity_coercion d38
    have d40 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d41 : (((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d42 : (((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d39 d40 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d42 neg_nat_to_real_coercion
    have d44 : (((a / b : ℝ) - ((2:ℕ) : ℝ) : ℝ) + (b / a : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) ↔ ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison ≥ d15 d16 d43 eq_identity_coercion eq_nat_to_real_coercion
    have d45 : a = a := by term_derivation_reflection
    have d46 : b = b := by term_derivation_reflection
    have d47 : (a * (b ^ (-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_exponential_greater real_pow_nat_to_real_pow_nat_coercion
    have d48 : (a / b : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_atom d47
    have d49 : (a / b : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d45 d46 eq_identity_coercion eq_identity_coercion d48
    have d50 : b = b := by term_derivation_reflection
    have d51 : a = a := by term_derivation_reflection
    have d52 : (b * (a ^ (-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_exponential_less real_pow_nat_to_real_pow_nat_coercion
    have d53 : (b / a : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_atom d52
    have d54 : (b / a : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d50 d51 eq_identity_coercion eq_identity_coercion d53
    have d55 : ((((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d56 : ((a / b : ℝ) + (b / a : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d49 d54 eq_identity_coercion eq_identity_coercion d55
    have d57 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d58 : b = b := by term_derivation_reflection
    have d59 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d60 : (b ^ (-1:ℤ) : ℝ) = (((1:ℕ) : ℝ) * (b ^ (-1:ℤ) : ℝ) : ℝ) := by term_derivation_non_reduced_power d58 d59
    have d61 : a = a := by term_derivation_reflection
    have d62 : (a ^ (1:ℕ) : ℝ) = a := by term_derivation_power_one
    have d63 : ((((1:ℕ) : ℝ) * (b ^ (-1:ℤ) : ℝ) : ℝ) * a : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_base_less
    have d64 : ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_eq d60 d62 d63 eq_identity_coercion eq_identity_coercion
    have d65 : (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_one_mul
    have d66 : (((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d67 : b = b := by term_derivation_reflection
    have d68 : (b ^ (1:ℕ) : ℝ) = b := by term_derivation_power_one
    have d69 : a = a := by term_derivation_reflection
    have d70 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d71 : (a ^ (-1:ℤ) : ℝ) = (((1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) := by term_derivation_non_reduced_power d69 d70
    have d72 : (b * ((1:ℕ) : ℝ) : ℝ) = b := by term_derivation_mul_one
    have d73 : (b * (a ^ (-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_mul_exponential_less real_pow_nat_to_real_pow_nat_coercion
    have d74 : (b * (((1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_product d72 d73 eq_identity_coercion comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion
    have d75 : ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_eq d68 d71 d74 eq_identity_coercion eq_identity_coercion
    have d76 : (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) := by term_derivation_one_mul
    have d77 : ((((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d78 : ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) = ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d66 d76 eq_identity_coercion eq_identity_coercion d77
    have d79 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d80 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d81 : (((0:ℕ) : ℤ) + (-2:ℤ) : ℤ) = (-2:ℤ) := by term_derivation_zero_add
    have d82 : (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d83 : ((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = (((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d81 d82 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d84 : ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d85 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d83 d84 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d86 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d78 d79 eq_identity_coercion eq_int_to_real_coercion d85
    have d87 : (((((0:ℕ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d86 neg_nat_to_real_coercion
    have d88 : ((a / b : ℝ) + (b / a : ℝ) : ℝ) ≥ ((2:ℕ) : ℝ) ↔ ((((-2:ℤ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (-1:ℤ) : ℝ) * (a ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) + (((1:ℕ) : ℝ) * ((b ^ (1:ℕ) : ℝ) * (a ^ (-1:ℤ) : ℝ) : ℝ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison ≥ d56 d57 d87 eq_identity_coercion eq_nat_to_real_coercion
    have d89 : ((a / b : ℝ) + (b / a : ℝ) : ℝ) ≥ ((2:ℕ) : ℝ) := by term_derivation_non_trivial_hypothesis_equivalence h5 d44 d88
    assumption
  obvious

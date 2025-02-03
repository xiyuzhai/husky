import Mathlib
import Visored.Obvious
import Visored.Tactics

set_option maxHeartbeats 20000000000

def h (x : ℝ) (h1 : x > ((0:ℕ) : ℝ)) : (x + (((1:ℕ) : ℝ) / x : ℝ) : ℝ) ≥ ((2:ℕ) : ℝ) := by
  have h1 : x > ((0:ℕ) : ℝ) := by old_main_hypothesis
  first
  | have h2 : ((x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    ((x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  | have h3 : (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by calc
    (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((x - ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) := by obvious
    _ ≥ ((0:ℕ) : ℝ) := by obvious
  have h4 : (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by obvious
  have h5 : ((x ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((2:ℕ) * x : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d2 : (x ^ (2:ℕ) : ℝ) = ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) := by term_derivation_non_reduced_power
    have d3 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d4 : x = x := by term_derivation_reflection
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d6 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d3 d4 d5 eq_nat_to_real_coercion eq_identity_coercion
    have d7 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d8 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d6 d7
    have d9 : (((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d10 : ((x ^ (2:ℕ) : ℝ) + (-((2:ℕ) * x : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d8 eq_identity_coercion eq_identity_coercion d9
    have d11 : ((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) = (((0:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_identity_coercion
    have d12 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d13 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d14 : ((0:ℕ) + (1:ℕ) : ℕ) = (1:ℕ) := by term_derivation_zero_add
    have d15 : ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d16 : (((0:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d14 d15 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_nat_to_real_coercion comm_ring_add_nat_to_real_coercion nat_nat_real_coercion_triangle nat_nat_real_coercion_triangle
    have d17 : (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d18 : ((((0:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d16 d17 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle nat_real_real_coercion_triangle
    have d19 : (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_nat_to_real_coercion d18
    have d20 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d21 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d22 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((-2:ℤ) * x : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d26 : ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d22 d24 d25 eq_int_to_real_coercion eq_identity_coercion
    have d27 : ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d28 : ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d21 d26 eq_nat_to_real_coercion eq_identity_coercion d27
    have d29 : x = x := by term_derivation_reflection
    have d30 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d31 : (x ^ (2:ℕ) : ℝ) = ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) := by term_derivation_non_reduced_power
    have d32 : ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) = ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) := by term_derivation_one_mul
    have d33 : (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d34 : (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d32 eq_identity_coercion eq_identity_coercion d33
    have d35 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d36 : ((((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d37 : ((((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d34 d35 eq_identity_coercion eq_int_to_real_coercion d36
    have d38 : ((((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d37 neg_nat_to_real_coercion
    have d39 : (((x ^ (2:ℕ) : ℝ) - ((2:ℕ) * x : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) ↔ (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d40 : x = x := by term_derivation_reflection
    have d41 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d42 : (x ^ (2:ℕ) : ℝ) = ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) := by term_derivation_non_reduced_power
    have d43 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d44 : (((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d45 : ((x ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_nat_to_real_coercion d44
    have d46 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d47 : x = x := by term_derivation_reflection
    have d48 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d46 d47 d48 eq_nat_to_real_coercion eq_identity_coercion
    have d50 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d51 : x = x := by term_derivation_reflection
    have d52 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d53 : (x ^ (2:ℕ) : ℝ) = ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) := by term_derivation_non_reduced_power
    have d54 : ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) = ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) := by term_derivation_one_mul
    have d55 : ((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d56 : ((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d50 d54 eq_nat_to_real_coercion eq_identity_coercion d55
    have d57 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d58 : x = x := by term_derivation_reflection
    have d59 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d60 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d61 : ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d57 d59 d60 eq_nat_to_real_coercion eq_identity_coercion
    have d62 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d63 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d61 d62
    have d64 : ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d65 : (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d66 : (((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_product_greater
    have d67 : (((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d56 d63 eq_identity_coercion eq_identity_coercion d66
    have d68 : (((1:ℕ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) - ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d67 neg_identity_coercion
    have d69 : ((x ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((2:ℕ) * x : ℝ) ↔ (((1:ℕ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d70 : ((x ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ≥ ((2:ℕ) * x : ℝ) := by term_derivation_non_trivial_hypothesis_equivalence h4 d39 d69
    assumption
  have h1 : x > ((0:ℕ) : ℝ) := by old_main_hypothesis
  have h6 : (x + (((1:ℕ) : ℝ) / x : ℝ) : ℝ) ≥ ((2:ℕ) : ℝ) := by obvious
  obvious

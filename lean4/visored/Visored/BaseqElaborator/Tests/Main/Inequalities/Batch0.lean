import Mathlib
import Visored.Tactics

namespace Example1
def h := by
  have h1 : (0:ℕ) = (0:ℕ) := by term_trivial
  exact ()
end Example1

namespace Example2
def h := by
  have h1 : ((1:ℕ) + (1:ℕ) : ℕ) = (2:ℕ) := by term_trivial
  exact ()
end Example2

namespace Example3
def h := by
  have h1 : ((1:ℕ) * (1:ℕ) : ℕ) = (1:ℕ) := by term_trivial
  exact ()
end Example3

namespace Example4
def h := by
  have h1 : ((1:ℕ) * (1:ℕ) : ℕ) = (1:ℕ) := by term_trivial
  exact ()
end Example4

namespace Example5
def h := by
  have h1 : ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) * ((2:ℕ) : ℚ) : ℚ) = ((1:ℕ) : ℚ) := by term_trivial
  exact ()
end Example5

namespace Example6
def h := by
  have h1 : (0:ℕ) < (1:ℕ) := by term_trivial
  exact ()
end Example6

namespace Example7
def h := by
  have h1 : (0:ℕ) ≠ (1:ℕ) := by term_trivial
  exact ()
end Example7

namespace Example8
def h (x : ℝ) := by
  have h1 : x = x := by term_trivial
  exact ()
end Example8

namespace Example9
def h (x : ℝ) := by
  have h1 : (x - x : ℝ) = ((0:ℕ) : ℝ) := by term_trivial
  exact ()
end Example9

namespace Example10
def h (x : ℝ) := by
  have h1 : (x + x : ℝ) = ((2:ℕ) * x : ℝ) := by term_trivial
  exact ()
end Example10

namespace Example11
def h (x : ℝ) := by
  have h1 : (x ^ (2:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    simp
    apply sq_nonneg
  exact ()
end Example11

namespace Example12
def h (x : ℝ) (h1 : x ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (x - ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : x ≥ ((1:ℕ) : ℝ) ↔ ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d8 : x = x := by term_derivation_reflection
    have d9 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d10 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d11 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d10
    have d12 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d11 neg_nat_to_real_coercion
    have d13 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d14 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d15 : x = x := by term_derivation_reflection
    have d16 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d17 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d18 : ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : ((-1:ℤ) + x : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d18
    have d20 : ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d14 d17 eq_int_to_real_coercion eq_identity_coercion d19
    have d21 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d22 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d23 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (x - ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) ↔ ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d26 : (x - ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_non_trivial_hypothesis_equivalence h1 d7 d25
    assumption
  exact ()
end Example12

namespace Example13
def h (x : ℝ) := by
  have h1 : ((2:ℕ) * ((1:ℕ) + x : ℝ) : ℝ) = ((2:ℕ) + ((2:ℕ) * x : ℝ) : ℝ) := by term_trivial
  exact ()
end Example13

namespace Example14
def h (x : ℝ) := by
  have h1 : (((1:ℕ) + x : ℝ) * x : ℝ) = (x + (x ^ (2:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example14

namespace Example15
def h (x : ℝ) := by
  have h1 : (((1:ℕ) + x : ℝ) * ((1:ℕ) + x : ℝ) : ℝ) = (((1:ℕ) + ((2:ℕ) * x : ℝ) : ℝ) + (x ^ (2:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example15

namespace Example16
def h (x y : ℝ) := by
  have h1 : (((1:ℕ) + x : ℝ) * ((1:ℕ) + y : ℝ) : ℝ) = ((((1:ℕ) + x : ℝ) + y : ℝ) + (x * y : ℝ) : ℝ) := by comm_ring
  exact ()
end Example16

namespace Example17
def h (x y : ℝ) := by
  have h1 : ((x + y : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ (2:ℕ) : ℝ) + (((2:ℕ) * x : ℝ) * y : ℝ) : ℝ) + (y ^ (2:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example17

namespace Example18
def h (x y : ℝ) := by
  have h1 : ((x + y : ℝ) ^ (3:ℕ) : ℝ) = ((((x ^ (3:ℕ) : ℝ) + (((3:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) * y : ℝ) : ℝ) + (((3:ℕ) * x : ℝ) * (y ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (y ^ (3:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example18

namespace Example19
def h (x y : ℝ) := by
  have h1 : ((x + y : ℝ) ^ (4:ℕ) : ℝ) = (((((x ^ (4:ℕ) : ℝ) + (((4:ℕ) * (x ^ (3:ℕ) : ℝ) : ℝ) * y : ℝ) : ℝ) + (((6:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) * (y ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (((4:ℕ) * x : ℝ) * (y ^ (3:ℕ) : ℝ) : ℝ) : ℝ) + (y ^ (4:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example19

namespace Example20
def h (x y : ℝ) := by
  have h1 : ((x + y : ℝ) ^ (5:ℕ) : ℝ) = ((((((x ^ (5:ℕ) : ℝ) + (((5:ℕ) * (x ^ (4:ℕ) : ℝ) : ℝ) * y : ℝ) : ℝ) + (((10:ℕ) * (x ^ (3:ℕ) : ℝ) : ℝ) * (y ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (((10:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) * (y ^ (3:ℕ) : ℝ) : ℝ) : ℝ) + (((5:ℕ) * x : ℝ) * (y ^ (4:ℕ) : ℝ) : ℝ) : ℝ) + (y ^ (5:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example20

namespace Example21
def h (x y : ℝ) := by
  have h1 : ((x + y : ℝ) ^ (6:ℕ) : ℝ) = (((((((x ^ (6:ℕ) : ℝ) + (((6:ℕ) * (x ^ (5:ℕ) : ℝ) : ℝ) * y : ℝ) : ℝ) + (((15:ℕ) * (x ^ (4:ℕ) : ℝ) : ℝ) * (y ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (((20:ℕ) * (x ^ (3:ℕ) : ℝ) : ℝ) * (y ^ (3:ℕ) : ℝ) : ℝ) : ℝ) + (((15:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) * (y ^ (4:ℕ) : ℝ) : ℝ) : ℝ) + (((6:ℕ) * x : ℝ) * (y ^ (5:ℕ) : ℝ) : ℝ) : ℝ) + (y ^ (6:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example21

namespace Example22
def h (x y : ℝ) := by
  have h1 : ((x + y : ℝ) ^ (7:ℕ) : ℝ) = ((((((((x ^ (7:ℕ) : ℝ) + (((7:ℕ) * (x ^ (6:ℕ) : ℝ) : ℝ) * y : ℝ) : ℝ) + (((21:ℕ) * (x ^ (5:ℕ) : ℝ) : ℝ) * (y ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (((35:ℕ) * (x ^ (4:ℕ) : ℝ) : ℝ) * (y ^ (3:ℕ) : ℝ) : ℝ) : ℝ) + (((35:ℕ) * (x ^ (3:ℕ) : ℝ) : ℝ) * (y ^ (4:ℕ) : ℝ) : ℝ) : ℝ) + (((21:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) * (y ^ (5:ℕ) : ℝ) : ℝ) : ℝ) + (((7:ℕ) * x : ℝ) * (y ^ (6:ℕ) : ℝ) : ℝ) : ℝ) + (y ^ (7:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example22

namespace Example23
def h (x y : ℝ) := by
  have h1 : ((x + y : ℝ) ^ (8:ℕ) : ℝ) = (((((((((x ^ (8:ℕ) : ℝ) + (((8:ℕ) * (x ^ (7:ℕ) : ℝ) : ℝ) * y : ℝ) : ℝ) + (((28:ℕ) * (x ^ (6:ℕ) : ℝ) : ℝ) * (y ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (((56:ℕ) * (x ^ (5:ℕ) : ℝ) : ℝ) * (y ^ (3:ℕ) : ℝ) : ℝ) : ℝ) + (((70:ℕ) * (x ^ (4:ℕ) : ℝ) : ℝ) * (y ^ (4:ℕ) : ℝ) : ℝ) : ℝ) + (((56:ℕ) * (x ^ (3:ℕ) : ℝ) : ℝ) * (y ^ (5:ℕ) : ℝ) : ℝ) : ℝ) + (((28:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) * (y ^ (6:ℕ) : ℝ) : ℝ) : ℝ) + (((8:ℕ) * x : ℝ) * (y ^ (7:ℕ) : ℝ) : ℝ) : ℝ) + (y ^ (8:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example23

namespace Example24
def h (x y : ℝ) := by
  have h1 : ((x + y : ℝ) ^ (9:ℕ) : ℝ) = ((((((((((x ^ (9:ℕ) : ℝ) + (((9:ℕ) * (x ^ (8:ℕ) : ℝ) : ℝ) * y : ℝ) : ℝ) + (((36:ℕ) * (x ^ (7:ℕ) : ℝ) : ℝ) * (y ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (((84:ℕ) * (x ^ (6:ℕ) : ℝ) : ℝ) * (y ^ (3:ℕ) : ℝ) : ℝ) : ℝ) + (((126:ℕ) * (x ^ (5:ℕ) : ℝ) : ℝ) * (y ^ (4:ℕ) : ℝ) : ℝ) : ℝ) + (((126:ℕ) * (x ^ (4:ℕ) : ℝ) : ℝ) * (y ^ (5:ℕ) : ℝ) : ℝ) : ℝ) + (((84:ℕ) * (x ^ (3:ℕ) : ℝ) : ℝ) * (y ^ (6:ℕ) : ℝ) : ℝ) : ℝ) + (((36:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) * (y ^ (7:ℕ) : ℝ) : ℝ) : ℝ) + (((9:ℕ) * x : ℝ) * (y ^ (8:ℕ) : ℝ) : ℝ) : ℝ) + (y ^ (9:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example24

namespace Example25
def h (x : ℝ) := by
  have h1 : (((x ^ (2:ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ (4:ℕ) : ℝ) + ((2:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example25

namespace Example26
def h (x y : ℝ) := by
  have h1 : (((x ^ (2:ℕ) : ℝ) + (y ^ (2:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ (4:ℕ) : ℝ) + (((2:ℕ) * (x ^ (2:ℕ) : ℝ) : ℝ) * (y ^ (2:ℕ) : ℝ) : ℝ) : ℝ) + (y ^ (4:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example26

namespace Example27
def h (x : ℝ) (n : ℕ) := by
  have h1 : (((x ^ n : ℝ) + ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ ((2:ℕ) * n : ℕ) : ℝ) + ((2:ℕ) * (x ^ n : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example27

namespace Example28
def h (x y : ℝ) (n : ℕ) := by
  have h1 : (((x ^ n : ℝ) + (y ^ n : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ ((2:ℕ) * n : ℕ) : ℝ) + (((2:ℕ) * (x ^ n : ℝ) : ℝ) * (y ^ n : ℝ) : ℝ) : ℝ) + (y ^ ((2:ℕ) * n : ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example28

namespace Example29
def h (x : ℝ) (n : ℕ) := by
  have h1 : (((x ^ (n ^ (2:ℕ) : ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ ((2:ℕ) * (n ^ (2:ℕ) : ℕ) : ℕ) : ℝ) + ((2:ℕ) * (x ^ (n ^ (2:ℕ) : ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example29

namespace Example30
def h (x : ℝ) (n : ℕ) := by
  have h1 : (((x ^ ((2:ℕ) * n : ℕ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) ^ (2:ℕ) : ℝ) = (((x ^ ((4:ℕ) * n : ℕ) : ℝ) + ((2:ℕ) * (x ^ ((2:ℕ) * n : ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) := by comm_ring
  exact ()
end Example30

namespace Example31
def h := by
  have h1 : (1000340282366920938463463374607431768211456:ℕ) = (1000340282366920938463463374607431768211456:ℕ) := by term_trivial
  exact ()
end Example31

namespace Example32
def h (x y : ℝ) := by
  have h1 : (x + y : ℝ) = (y + x : ℝ) := by term_trivial
  exact ()
end Example32

namespace Example33
def h (x : ℝ) (h1 : x = ((1:ℕ) : ℝ)) := by
  have h1 : x = ((1:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example33

namespace Example34
def h := by
  let x := (1:ℕ)
  have h1 : x = (1:ℕ) := by let_assigned
  have h1 : x = (1:ℕ) := by old_main_hypothesis
  exact ()
end Example34

namespace Example35
def h := by
  let x := (1:ℕ)
  have h1 : x = (1:ℕ) := by let_assigned
  have h2 : x > (0:ℕ) := by litnum_reduce
  exact ()
end Example35

namespace Example36
def h := by
  let x := (1:ℕ)
  have h1 : x = (1:ℕ) := by let_assigned
  let y := (1:ℕ)
  have h2 : y = (1:ℕ) := by let_assigned
  let z := (2:ℕ)
  have h3 : z = (2:ℕ) := by let_assigned
  have h4 : (x + y : ℕ) = z := by litnum_reduce
  exact ()
end Example36

namespace Example37
def h (x : ℝ) (h1 : x > ((0:ℕ) : ℝ)) := by
  have h1 : x > ((0:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example37

namespace Example38
def h (x : ℝ) (h1 : x > ((1:ℕ) : ℝ)) := by
  have h2 : x > ((0:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d7 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d6
    have d8 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_nat_to_real_coercion d7
    have d9 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d10 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d11 : x = x := by term_derivation_reflection
    have d12 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d13 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d14 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d10 d14 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d16 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d16 neg_int_to_real_coercion
    have d18 : x = x := by term_derivation_reflection
    have d19 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d20 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d21 : (x + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d18 d19 eq_identity_coercion eq_int_to_real_coercion d20
    have d22 : (x - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d21 neg_nat_to_real_coercion
    have d23 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d24 : (x * ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_mul_one
    have d25 : (x / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_literal d24
    have d26 : ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_eq d22 d23 eq_identity_coercion eq_nat_to_real_coercion d25
    have d27 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d28 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d29 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d17 d30
    have d32 : x > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example38

namespace Example39
def h (x : ℝ) (h1 : x > ((1:ℕ) : ℝ)) := by
  have h2 : x ≥ ((1:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d7 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d6
    have d8 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_nat_to_real_coercion d7
    have d9 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d10 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d11 : x = x := by term_derivation_reflection
    have d12 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d13 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d14 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d10 d14 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d16 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d16 neg_int_to_real_coercion
    have d18 : x = x := by term_derivation_reflection
    have d19 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d20 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d21 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d18 d19 eq_identity_coercion eq_int_to_real_coercion d20
    have d22 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d21 neg_nat_to_real_coercion
    have d23 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d24 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d25 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d24
    have d26 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d22 d23 eq_identity_coercion eq_nat_to_real_coercion d25
    have d27 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d28 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d29 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d17 d30
    have d32 : x ≥ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example39

namespace Example40
def h (x : ℝ) (h1 : x ≥ ((1:ℕ) : ℝ)) := by
  have h2 : x ≥ ((0:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d7 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d6
    have d8 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_nat_to_real_coercion d7
    have d9 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d10 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d11 : x = x := by term_derivation_reflection
    have d12 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d13 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d14 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d10 d14 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d16 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d16 neg_int_to_real_coercion
    have d18 : x = x := by term_derivation_reflection
    have d19 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d20 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d21 : (x + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d18 d19 eq_identity_coercion eq_int_to_real_coercion d20
    have d22 : (x - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d21 neg_nat_to_real_coercion
    have d23 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d24 : (x * ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_mul_one
    have d25 : (x / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_literal d24
    have d26 : ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_eq d22 d23 eq_identity_coercion eq_nat_to_real_coercion d25
    have d27 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d28 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d29 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d17 d30
    have d32 : x ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example40

namespace Example41
def h (x : ℝ) (h1 : x ≥ ((1:ℕ) : ℝ)) := by
  have h2 : x > ((0:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d7 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d6
    have d8 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_nat_to_real_coercion d7
    have d9 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d10 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d11 : x = x := by term_derivation_reflection
    have d12 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d13 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d14 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d10 d14 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d16 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d16 neg_int_to_real_coercion
    have d18 : x = x := by term_derivation_reflection
    have d19 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d20 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d21 : (x + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d18 d19 eq_identity_coercion eq_int_to_real_coercion d20
    have d22 : (x - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d21 neg_nat_to_real_coercion
    have d23 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d24 : (x * ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_mul_one
    have d25 : (x / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_literal d24
    have d26 : ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_eq d22 d23 eq_identity_coercion eq_nat_to_real_coercion d25
    have d27 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d28 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d29 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d17 d30
    have d32 : x > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example41

namespace Example42
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((1:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d9 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d10 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d11 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d13 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d12
    have d14 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d16 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d21 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d17 d19 d20 eq_int_to_real_coercion eq_identity_coercion
    have d22 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d23 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d16 d22 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d24 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d14 d15 eq_identity_coercion eq_int_to_real_coercion d23
    have d25 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d24 neg_nat_to_real_coercion
    have d26 : x = x := by term_derivation_reflection
    have d27 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d28 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d29 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d32 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d33 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d35 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d32 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d25 d44
    have d46 : x ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example42

namespace Example43
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x < ((2:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d9 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d10 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d11 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d13 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d12
    have d14 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d16 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d21 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d17 d19 d20 eq_int_to_real_coercion eq_identity_coercion
    have d22 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d23 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d16 d22 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d24 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d14 d15 eq_identity_coercion eq_int_to_real_coercion d23
    have d25 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d24 neg_nat_to_real_coercion
    have d26 : x = x := by term_derivation_reflection
    have d27 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d28 : (x + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d29 : (x + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (x - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d32 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d33 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d35 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d32 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d25 d44
    have d46 : x < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example43

namespace Example44
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((2:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d9 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d10 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d11 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d13 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d12
    have d14 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d16 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d21 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d17 d19 d20 eq_int_to_real_coercion eq_identity_coercion
    have d22 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d23 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d16 d22 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d24 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d14 d15 eq_identity_coercion eq_int_to_real_coercion d23
    have d25 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d24 neg_nat_to_real_coercion
    have d26 : x = x := by term_derivation_reflection
    have d27 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d28 : (x + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d29 : (x + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (x - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d32 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d33 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d35 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d32 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d25 d44
    have d46 : x ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example44

namespace Example45
def h (x : ℝ) (h1 : x ≤ ((1:ℕ) : ℝ)) := by
  have h2 : x < ((2:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d9 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d10 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d11 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d13 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d12
    have d14 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d16 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d21 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d17 d19 d20 eq_int_to_real_coercion eq_identity_coercion
    have d22 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d23 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d16 d22 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d24 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d14 d15 eq_identity_coercion eq_int_to_real_coercion d23
    have d25 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d24 neg_nat_to_real_coercion
    have d26 : x = x := by term_derivation_reflection
    have d27 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d28 : (x + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d29 : (x + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (x - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d32 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d33 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d35 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d32 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d25 d44
    have d46 : x < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example45

namespace Example46
def h (x : ℝ) (h1 : x ≤ ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((2:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d3 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d9 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d10 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d11 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d13 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d12
    have d14 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d16 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d21 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d17 d19 d20 eq_int_to_real_coercion eq_identity_coercion
    have d22 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d23 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d16 d22 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d24 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d14 d15 eq_identity_coercion eq_int_to_real_coercion d23
    have d25 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d24 neg_nat_to_real_coercion
    have d26 : x = x := by term_derivation_reflection
    have d27 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d28 : (x + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d29 : (x + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d28
    have d30 : (x - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_nat_to_real_coercion
    have d31 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d32 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d33 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d35 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d32 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d25 d44
    have d46 : x ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example46

namespace Example47
def h (x : ℝ) (h1 : (- x : ℝ) > ((0:ℕ) : ℝ)) := by
  have h1 : (- x : ℝ) > ((0:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example47

namespace Example48
def h (x : ℝ) (h1 : (- x : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d7 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d6
    have d8 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_nat_to_real_coercion d7
    have d9 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d10 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d11 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d12 : x = x := by term_derivation_reflection
    have d13 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d14 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d11 d13 d14 eq_int_to_real_coercion eq_identity_coercion
    have d16 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d17 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d10 d16 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d18 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d18 neg_int_to_real_coercion
    have d20 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d21 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d22 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d23 : ((- x : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d26 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d27 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d26
    have d28 : (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d27
    have d29 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d30 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d31 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d19 d32
    have d34 : (- x : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example48

namespace Example49
def h (x : ℝ) (h1 : (- x : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≥ ((1:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d7 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d6
    have d8 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_nat_to_real_coercion d7
    have d9 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d10 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d11 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d12 : x = x := by term_derivation_reflection
    have d13 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d14 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d11 d13 d14 eq_int_to_real_coercion eq_identity_coercion
    have d16 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d17 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d10 d16 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d18 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d18 neg_int_to_real_coercion
    have d20 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d21 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d22 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d23 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d26 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d27 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d26
    have d28 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d27
    have d29 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d30 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d31 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d19 d32
    have d34 : (- x : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example49

namespace Example50
def h (x : ℝ) (h1 : (- x : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d7 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d6
    have d8 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_nat_to_real_coercion d7
    have d9 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d10 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d11 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d12 : x = x := by term_derivation_reflection
    have d13 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d14 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d11 d13 d14 eq_int_to_real_coercion eq_identity_coercion
    have d16 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d17 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d10 d16 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d18 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d18 neg_int_to_real_coercion
    have d20 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d21 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d22 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d23 : ((- x : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d26 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d27 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d26
    have d28 : (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d27
    have d29 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d30 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d31 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d19 d32
    have d34 : (- x : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example50

namespace Example51
def h (x : ℝ) (h1 : (- x : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d7 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d6
    have d8 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_nat_to_real_coercion d7
    have d9 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d10 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d11 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d12 : x = x := by term_derivation_reflection
    have d13 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d14 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d11 d13 d14 eq_int_to_real_coercion eq_identity_coercion
    have d16 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d17 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d10 d16 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d18 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d18 neg_int_to_real_coercion
    have d20 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d21 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d22 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d23 : ((- x : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d26 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d27 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d26
    have d28 : (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d27
    have d29 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d30 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d31 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d19 d32
    have d34 : (- x : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example51

namespace Example52
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d9 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d10 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d11
    have d13 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d12 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d14 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d13
    have d15 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d21 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d22 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d17 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d26 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d27 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d28 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_int_to_real_coercion d27
    have d29 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d28 neg_nat_to_real_coercion
    have d30 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d31 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d32 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d33 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d35 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d33 d34 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d36 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d36
    have d38 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d31 d32 d35 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d29 d30 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d24 d44
    have d46 : (- x : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example52

namespace Example53
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d9 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d10 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d11
    have d13 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d12 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d14 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d13
    have d15 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d21 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d22 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d17 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d26 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d27 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d28 : ((- x : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_int_to_real_coercion d27
    have d29 : ((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d28 neg_nat_to_real_coercion
    have d30 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d31 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d32 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d33 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d35 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d33 d34 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d36 : ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : ((2:ℕ) + x : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d36
    have d38 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d31 d32 d35 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d29 d30 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d24 d44
    have d46 : (- x : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example53

namespace Example54
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d9 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d10 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d11
    have d13 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d12 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d14 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d13
    have d15 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d21 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d22 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d17 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d26 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d27 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d28 : ((- x : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_int_to_real_coercion d27
    have d29 : ((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d28 neg_nat_to_real_coercion
    have d30 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d31 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d32 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d33 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d35 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d33 d34 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d36 : ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : ((2:ℕ) + x : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d36
    have d38 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d31 d32 d35 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d29 d30 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d24 d44
    have d46 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example54

namespace Example55
def h (x : ℝ) (h1 : (- x : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d9 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d10 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d11
    have d13 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d12 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d14 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d13
    have d15 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d21 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d22 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d17 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d26 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d27 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d28 : ((- x : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_int_to_real_coercion d27
    have d29 : ((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d28 neg_nat_to_real_coercion
    have d30 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d31 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d32 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d33 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d35 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d33 d34 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d36 : ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : ((2:ℕ) + x : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d36
    have d38 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d31 d32 d35 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d29 d30 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d24 d44
    have d46 : (- x : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example55

namespace Example56
def h (x : ℝ) (h1 : (- x : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d1 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d2 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d3 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d d1 eq_identity_coercion eq_int_to_real_coercion d2
    have d4 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d3 neg_nat_to_real_coercion
    have d5 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d6 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d7 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d8 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d9 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d10 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d8 d9 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d11 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d11
    have d13 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d6 d7 d10 d12 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d14 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d13
    have d15 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d4 d5 eq_identity_coercion eq_int_to_real_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d18 : x = x := by term_derivation_reflection
    have d19 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d21 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d22 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d17 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d26 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d27 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d28 : ((- x : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_int_to_real_coercion d27
    have d29 : ((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d28 neg_nat_to_real_coercion
    have d30 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d31 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d32 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d33 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d34 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d35 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d33 d34 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d36 : ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : ((2:ℕ) + x : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d36
    have d38 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d31 d32 d35 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d29 d30 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : (((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d24 d44
    have d46 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example56

namespace Example57
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ)) := by
  have h1 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example57

namespace Example58
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d14 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d15 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d16 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d17
    have d19 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_nat_to_real_coercion d18
    have d20 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d21 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d22 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d26 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d22 d24 d25 eq_int_to_real_coercion eq_identity_coercion
    have d27 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d28 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d21 d27 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d19 d20 eq_identity_coercion eq_rat_to_real_coercion d28
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_rat_to_real_coercion
    have d31 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d32 : x = x := by term_derivation_reflection
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d31 d32 d33 eq_nat_to_real_coercion eq_identity_coercion
    have d35 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d36 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d37 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d38 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d36 d37 eq_identity_coercion eq_int_to_real_coercion d38
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d39 neg_nat_to_real_coercion
    have d41 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d42 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal
    have d43 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d42
    have d44 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d40 d41 eq_identity_coercion eq_nat_to_real_coercion d43
    have d45 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d46 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d47 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d44 d45 eq_identity_coercion eq_int_to_real_coercion d46
    have d48 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d47 neg_nat_to_real_coercion
    have d49 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d30 d48
    have d50 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example58

namespace Example59
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d14 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d15 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d16 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d17
    have d19 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_nat_to_real_coercion d18
    have d20 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d21 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d22 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d26 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d22 d24 d25 eq_int_to_real_coercion eq_identity_coercion
    have d27 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d28 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d21 d27 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d19 d20 eq_identity_coercion eq_rat_to_real_coercion d28
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_rat_to_real_coercion
    have d31 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d32 : x = x := by term_derivation_reflection
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d31 d32 d33 eq_nat_to_real_coercion eq_identity_coercion
    have d35 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d36 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d37 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d38 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d36 d37 eq_identity_coercion eq_int_to_real_coercion d38
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d39 neg_nat_to_real_coercion
    have d41 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d42 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d43 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d44 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d45 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d46 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d44 d45 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d47 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d48 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d42 d43 d46 d47 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d49 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d48
    have d50 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d40 d41 eq_identity_coercion eq_nat_to_real_coercion d49
    have d51 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d52 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d53 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d50 d51 eq_identity_coercion eq_int_to_real_coercion d52
    have d54 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_nat_to_real_coercion
    have d55 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d30 d54
    have d56 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example59

namespace Example60
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d14 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d15 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d16 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d17
    have d19 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_nat_to_real_coercion d18
    have d20 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d21 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d22 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d26 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d22 d24 d25 eq_int_to_real_coercion eq_identity_coercion
    have d27 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d28 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d21 d27 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d19 d20 eq_identity_coercion eq_rat_to_real_coercion d28
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_rat_to_real_coercion
    have d31 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d32 : x = x := by term_derivation_reflection
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d31 d32 d33 eq_nat_to_real_coercion eq_identity_coercion
    have d35 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d36 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d37 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d38 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d36 d37 eq_identity_coercion eq_int_to_real_coercion d38
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d39 neg_nat_to_real_coercion
    have d41 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d42 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal
    have d43 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d42
    have d44 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d40 d41 eq_identity_coercion eq_nat_to_real_coercion d43
    have d45 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d46 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d47 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d44 d45 eq_identity_coercion eq_int_to_real_coercion d46
    have d48 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d47 neg_nat_to_real_coercion
    have d49 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d30 d48
    have d50 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example60

namespace Example61
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d14 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d15 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d16 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d17
    have d19 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_nat_to_real_coercion d18
    have d20 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d21 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d22 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d26 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d22 d24 d25 eq_int_to_real_coercion eq_identity_coercion
    have d27 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d28 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d21 d27 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d19 d20 eq_identity_coercion eq_rat_to_real_coercion d28
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d29 neg_rat_to_real_coercion
    have d31 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d32 : x = x := by term_derivation_reflection
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d31 d32 d33 eq_nat_to_real_coercion eq_identity_coercion
    have d35 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d36 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d37 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d38 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d36 d37 eq_identity_coercion eq_int_to_real_coercion d38
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d39 neg_nat_to_real_coercion
    have d41 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d42 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal
    have d43 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d42
    have d44 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d40 d41 eq_identity_coercion eq_nat_to_real_coercion d43
    have d45 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d46 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d47 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d44 d45 eq_identity_coercion eq_int_to_real_coercion d46
    have d48 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d47 neg_nat_to_real_coercion
    have d49 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d30 d48
    have d50 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example61

namespace Example62
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d14 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d16
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d17 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d18
    have d20 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d22 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d26 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d27 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d22 d26 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d28 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_rat_to_real_coercion d27
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d28 neg_rat_to_real_coercion
    have d30 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d31 : x = x := by term_derivation_reflection
    have d32 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d30 d31 d32 eq_nat_to_real_coercion eq_identity_coercion
    have d34 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d35 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d36 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d37 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d38 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d35 d36 eq_identity_coercion eq_int_to_real_coercion d37
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d38 neg_nat_to_real_coercion
    have d40 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d41 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d42 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d43 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d44 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d43 d44 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d46 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d47 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d46
    have d48 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d41 d42 d45 d47 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d49 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d48
    have d50 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d39 d40 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d52 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d53 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d50 d51 eq_identity_coercion eq_int_to_real_coercion d52
    have d54 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_nat_to_real_coercion
    have d55 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d29 d54
    have d56 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example62

namespace Example63
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d14 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d16
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d17 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d18
    have d20 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d22 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d26 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d27 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d22 d26 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d28 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_rat_to_real_coercion d27
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d28 neg_rat_to_real_coercion
    have d30 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d31 : x = x := by term_derivation_reflection
    have d32 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d30 d31 d32 eq_nat_to_real_coercion eq_identity_coercion
    have d34 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d35 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d36 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d37 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d38 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d35 d36 eq_identity_coercion eq_int_to_real_coercion d37
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d38 neg_nat_to_real_coercion
    have d40 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d41 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d42 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d43 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d44 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d43 d44 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d46 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d47 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d46
    have d48 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d41 d42 d45 d47 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d49 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d48
    have d50 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d39 d40 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d52 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d53 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d50 d51 eq_identity_coercion eq_int_to_real_coercion d52
    have d54 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_nat_to_real_coercion
    have d55 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d29 d54
    have d56 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example63

namespace Example64
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d14 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d16
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d17 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d18
    have d20 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d22 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d26 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d27 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d22 d26 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d28 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_rat_to_real_coercion d27
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d28 neg_rat_to_real_coercion
    have d30 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d31 : x = x := by term_derivation_reflection
    have d32 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d30 d31 d32 eq_nat_to_real_coercion eq_identity_coercion
    have d34 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d35 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d36 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d37 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d38 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d35 d36 eq_identity_coercion eq_int_to_real_coercion d37
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d38 neg_nat_to_real_coercion
    have d40 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d41 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d42 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d43 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d44 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d43 d44 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d46 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d47 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d46
    have d48 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d41 d42 d45 d47 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d49 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d48
    have d50 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d39 d40 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d52 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d53 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d50 d51 eq_identity_coercion eq_int_to_real_coercion d52
    have d54 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_nat_to_real_coercion
    have d55 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d29 d54
    have d56 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example64

namespace Example65
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d14 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d16
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d17 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d18
    have d20 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d22 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d26 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d27 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d22 d26 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d28 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_rat_to_real_coercion d27
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d28 neg_rat_to_real_coercion
    have d30 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d31 : x = x := by term_derivation_reflection
    have d32 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d30 d31 d32 eq_nat_to_real_coercion eq_identity_coercion
    have d34 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d35 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d36 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d37 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d38 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d35 d36 eq_identity_coercion eq_int_to_real_coercion d37
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d38 neg_nat_to_real_coercion
    have d40 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d41 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d42 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d43 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d44 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d43 d44 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d46 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d47 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d46
    have d48 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d41 d42 d45 d47 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d49 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d48
    have d50 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d39 d40 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d52 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d53 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d50 d51 eq_identity_coercion eq_int_to_real_coercion d52
    have d54 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_nat_to_real_coercion
    have d55 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d29 d54
    have d56 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example65

namespace Example66
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : x = x := by term_derivation_reflection
    have d2 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d3 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d d1 d2 eq_nat_to_real_coercion eq_identity_coercion
    have d4 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d5 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d6 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d7 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d8 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d5 d6 eq_identity_coercion eq_int_to_real_coercion d7
    have d9 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d8 neg_nat_to_real_coercion
    have d10 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d11 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d12 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d13 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d14 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d13 d14 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d16 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d16
    have d18 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d11 d12 d15 d17 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d18
    have d20 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d22 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d23 : x = x := by term_derivation_reflection
    have d24 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d25 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d26 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d27 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d22 d26 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d28 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_rat_to_real_coercion d27
    have d29 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d28 neg_rat_to_real_coercion
    have d30 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d31 : x = x := by term_derivation_reflection
    have d32 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d33 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d30 d31 d32 eq_nat_to_real_coercion eq_identity_coercion
    have d34 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d35 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d36 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d37 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d38 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d35 d36 eq_identity_coercion eq_int_to_real_coercion d37
    have d39 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d38 neg_nat_to_real_coercion
    have d40 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d41 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d42 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d43 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d44 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d43 d44 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d46 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d47 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d46
    have d48 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d41 d42 d45 d47 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d49 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d48
    have d50 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d39 d40 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d52 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d53 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d50 d51 eq_identity_coercion eq_int_to_real_coercion d52
    have d54 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_nat_to_real_coercion
    have d55 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d29 d54
    have d56 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example66

namespace Example67
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ)) := by
  have h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example67

namespace Example68
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d18 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d20 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d21
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d22
    have d24 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d25 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d26 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d26 d28 d29 eq_int_to_real_coercion eq_identity_coercion
    have d31 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d32 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d25 d31 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d23 d24 eq_identity_coercion eq_rat_to_real_coercion d32
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d33 neg_rat_to_real_coercion
    have d35 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d36 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d37 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d37
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d35 d36 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d38
    have d40 : x = x := by term_derivation_reflection
    have d41 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d42 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d39 d40 d41 eq_rat_to_real_coercion eq_identity_coercion
    have d43 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d44 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d45 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d46 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d44 d45 eq_identity_coercion eq_int_to_real_coercion d46
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d47 neg_nat_to_real_coercion
    have d49 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d50 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal
    have d51 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d48 d49 eq_identity_coercion eq_rat_to_real_coercion d51
    have d53 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d54 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d55 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_int_to_real_coercion d54
    have d56 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d55 neg_nat_to_real_coercion
    have d57 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d34 d56
    have d58 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example68

namespace Example69
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d18 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d20 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d21
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d22
    have d24 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d25 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d26 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d26 d28 d29 eq_int_to_real_coercion eq_identity_coercion
    have d31 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d32 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d25 d31 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d23 d24 eq_identity_coercion eq_rat_to_real_coercion d32
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d33 neg_rat_to_real_coercion
    have d35 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d36 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d37 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d37
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d35 d36 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d38
    have d40 : x = x := by term_derivation_reflection
    have d41 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d42 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d39 d40 d41 eq_rat_to_real_coercion eq_identity_coercion
    have d43 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d44 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d45 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d46 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d44 d45 eq_identity_coercion eq_int_to_real_coercion d46
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d47 neg_nat_to_real_coercion
    have d49 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d50 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d51 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d52 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d53 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d54 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d52 d53 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d55 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d56 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d50 d51 d54 d55 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d57 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d56
    have d58 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d48 d49 eq_identity_coercion eq_rat_to_real_coercion d57
    have d59 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d60 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d61 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d58 d59 eq_identity_coercion eq_int_to_real_coercion d60
    have d62 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d61 neg_nat_to_real_coercion
    have d63 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d34 d62
    have d64 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example69

namespace Example70
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d18 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d20 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d21
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d22
    have d24 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d25 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d26 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d26 d28 d29 eq_int_to_real_coercion eq_identity_coercion
    have d31 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d32 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d25 d31 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d23 d24 eq_identity_coercion eq_rat_to_real_coercion d32
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d33 neg_rat_to_real_coercion
    have d35 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d36 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d37 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d37
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d35 d36 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d38
    have d40 : x = x := by term_derivation_reflection
    have d41 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d42 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d39 d40 d41 eq_rat_to_real_coercion eq_identity_coercion
    have d43 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d44 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d45 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d46 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d44 d45 eq_identity_coercion eq_int_to_real_coercion d46
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d47 neg_nat_to_real_coercion
    have d49 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d50 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal
    have d51 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d48 d49 eq_identity_coercion eq_rat_to_real_coercion d51
    have d53 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d54 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d55 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_int_to_real_coercion d54
    have d56 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d55 neg_nat_to_real_coercion
    have d57 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d34 d56
    have d58 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example70

namespace Example71
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d18 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d20 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d21
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d22
    have d24 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d25 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d26 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d26 d28 d29 eq_int_to_real_coercion eq_identity_coercion
    have d31 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d32 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d25 d31 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d23 d24 eq_identity_coercion eq_rat_to_real_coercion d32
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d33 neg_rat_to_real_coercion
    have d35 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d36 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d37 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d37
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d35 d36 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d38
    have d40 : x = x := by term_derivation_reflection
    have d41 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d42 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d39 d40 d41 eq_rat_to_real_coercion eq_identity_coercion
    have d43 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d44 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d45 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d46 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d44 d45 eq_identity_coercion eq_int_to_real_coercion d46
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d47 neg_nat_to_real_coercion
    have d49 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d50 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal
    have d51 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d48 d49 eq_identity_coercion eq_rat_to_real_coercion d51
    have d53 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d54 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d55 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_int_to_real_coercion d54
    have d56 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d55 neg_nat_to_real_coercion
    have d57 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d34 d56
    have d58 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example71

namespace Example72
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d18 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d20
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d21 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d23
    have d25 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d26 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d30 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d31 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d26 d30 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d32 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d31
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d32 neg_rat_to_real_coercion
    have d34 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d35 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d36 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d37 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d36
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d34 d35 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d37
    have d39 : x = x := by term_derivation_reflection
    have d40 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d41 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d38 d39 d40 eq_rat_to_real_coercion eq_identity_coercion
    have d42 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d43 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d44 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d45 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d46 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_int_to_real_coercion d45
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d46 neg_nat_to_real_coercion
    have d48 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d49 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d50 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d51 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d52 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d51 d52 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d54 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d55 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d54
    have d56 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d49 d50 d53 d55 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d57 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d56
    have d58 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d47 d48 eq_identity_coercion eq_rat_to_real_coercion d57
    have d59 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d60 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d61 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d58 d59 eq_identity_coercion eq_int_to_real_coercion d60
    have d62 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d61 neg_nat_to_real_coercion
    have d63 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d33 d62
    have d64 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example72

namespace Example73
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d18 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d20
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d21 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d23
    have d25 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d26 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d30 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d31 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d26 d30 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d32 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d31
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d32 neg_rat_to_real_coercion
    have d34 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d35 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d36 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d37 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d36
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d34 d35 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d37
    have d39 : x = x := by term_derivation_reflection
    have d40 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d41 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d38 d39 d40 eq_rat_to_real_coercion eq_identity_coercion
    have d42 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d43 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d44 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d45 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d46 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_int_to_real_coercion d45
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d46 neg_nat_to_real_coercion
    have d48 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d49 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d50 : (((-3:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d51 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d52 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d51 d52 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d54 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d55 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d54
    have d56 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d49 d50 d53 d55 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d57 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d56
    have d58 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d47 d48 eq_identity_coercion eq_rat_to_real_coercion d57
    have d59 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d60 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d61 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d58 d59 eq_identity_coercion eq_int_to_real_coercion d60
    have d62 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d61 neg_nat_to_real_coercion
    have d63 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d33 d62
    have d64 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example73

namespace Example74
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d18 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d20
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d21 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d23
    have d25 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d26 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d30 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d31 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d26 d30 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d32 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d31
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d32 neg_rat_to_real_coercion
    have d34 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d35 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d36 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d37 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d36
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d34 d35 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d37
    have d39 : x = x := by term_derivation_reflection
    have d40 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d41 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d38 d39 d40 eq_rat_to_real_coercion eq_identity_coercion
    have d42 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d43 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d44 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d45 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d46 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_int_to_real_coercion d45
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d46 neg_nat_to_real_coercion
    have d48 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d49 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d50 : (((-3:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d51 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d52 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d51 d52 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d54 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d55 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d54
    have d56 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d49 d50 d53 d55 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d57 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d56
    have d58 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d47 d48 eq_identity_coercion eq_rat_to_real_coercion d57
    have d59 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d60 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d61 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d58 d59 eq_identity_coercion eq_int_to_real_coercion d60
    have d62 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d61 neg_nat_to_real_coercion
    have d63 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d33 d62
    have d64 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example74

namespace Example75
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d18 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d20
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d21 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d23
    have d25 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d26 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d30 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d31 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d26 d30 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d32 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d31
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d32 neg_rat_to_real_coercion
    have d34 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d35 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d36 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d37 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d36
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d34 d35 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d37
    have d39 : x = x := by term_derivation_reflection
    have d40 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d41 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d38 d39 d40 eq_rat_to_real_coercion eq_identity_coercion
    have d42 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d43 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d44 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d45 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d46 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_int_to_real_coercion d45
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d46 neg_nat_to_real_coercion
    have d48 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d49 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d50 : (((-3:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d51 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d52 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d51 d52 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d54 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d55 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d54
    have d56 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d49 d50 d53 d55 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d57 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d56
    have d58 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d47 d48 eq_identity_coercion eq_rat_to_real_coercion d57
    have d59 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d60 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d61 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d58 d59 eq_identity_coercion eq_int_to_real_coercion d60
    have d62 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d61 neg_nat_to_real_coercion
    have d63 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d33 d62
    have d64 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example75

namespace Example76
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d11 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d12 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d10 eq_identity_coercion eq_int_to_real_coercion d11
    have d13 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d12 neg_nat_to_real_coercion
    have d14 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d15 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d16 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d17 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d18 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d17 d18 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d20 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d20
    have d22 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d15 d16 d19 d21 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d13 d14 eq_identity_coercion eq_rat_to_real_coercion d23
    have d25 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d26 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d27 : x = x := by term_derivation_reflection
    have d28 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d29 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d30 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d31 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d26 d30 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d32 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d31
    have d33 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d32 neg_rat_to_real_coercion
    have d34 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d35 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d36 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d37 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d36
    have d38 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d34 d35 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d37
    have d39 : x = x := by term_derivation_reflection
    have d40 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d41 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d38 d39 d40 eq_rat_to_real_coercion eq_identity_coercion
    have d42 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d43 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d44 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d45 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d46 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_int_to_real_coercion d45
    have d47 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d46 neg_nat_to_real_coercion
    have d48 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d49 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d50 : (((-3:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d51 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d52 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d51 d52 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d54 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d55 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d54
    have d56 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d49 d50 d53 d55 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d57 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d56
    have d58 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d47 d48 eq_identity_coercion eq_rat_to_real_coercion d57
    have d59 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d60 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d61 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d58 d59 eq_identity_coercion eq_int_to_real_coercion d60
    have d62 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d61 neg_nat_to_real_coercion
    have d63 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d33 d62
    have d64 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example76

namespace Example77
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((0:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d17 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d18 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d18 neg_nat_to_real_coercion
    have d20 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d21 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d22 : (((3:ℚ)/2:ℚ) * ((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d23 : (((3:ℚ)/2:ℚ) * ((0:ℕ) : ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d24 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d25 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d26 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d24 d25 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d27 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d28 : x = x := by term_derivation_reflection
    have d29 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d30 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d31 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d27 d29 d30 eq_int_to_real_coercion eq_identity_coercion
    have d32 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d33 : (((3:ℚ)/2:ℚ) * ((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d22 d23 d26 d32 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle nat_rat_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d34 : (((3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d35 : ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : (((3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d38 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d21 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d19 d20 eq_identity_coercion eq_rat_to_real_coercion d39
    have d41 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d42 : ((((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d43 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_int_to_real_coercion d42
    have d44 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d43 neg_nat_to_real_coercion
    have d45 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d46 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d47 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d48 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d47
    have d49 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d45 d46 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d48
    have d50 : x = x := by term_derivation_reflection
    have d51 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d52 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d49 d50 d51 eq_rat_to_real_coercion eq_identity_coercion
    have d53 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d54 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d55 : y = y := by term_derivation_reflection
    have d56 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d57 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d56
    have d58 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d54 d55 eq_identity_coercion eq_identity_coercion d57
    have d59 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d60 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d61 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d58 d59 eq_identity_coercion eq_int_to_real_coercion d60
    have d62 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d61 neg_nat_to_real_coercion
    have d63 : ((1:ℚ)/3:ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d64 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((3:ℕ) : ℝ) : ℝ) = ((3:ℕ) * ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d65 : ((3:ℕ) * ((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d66 : ((3:ℕ) * (0:ℕ) : ℕ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d67 : ((3:ℕ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d68 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d69 : ((3:ℕ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d67 d68 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d70 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d71 : x = x := by term_derivation_reflection
    have d72 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d73 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d74 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d70 d72 d73 eq_int_to_real_coercion eq_identity_coercion
    have d75 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d76 : ((3:ℕ) * ((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d65 d66 d69 d75 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion nat_nat_real_coercion_triangle nat_real_real_coercion_triangle nat_nat_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d77 : ((3:ℕ) * (1:ℕ) : ℕ) = (3:ℕ) := by term_derivation_mul_one
    have d78 : ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d79 : ((3:ℕ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d77 d78 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d80 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d81 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((3:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d64 d76 d79 d80 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion nat_real_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d82 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d81
    have d83 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d62 d63 eq_identity_coercion eq_rat_to_real_coercion d82
    have d84 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d85 : ((((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d86 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d83 d84 eq_identity_coercion eq_int_to_real_coercion d85
    have d87 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d86 neg_nat_to_real_coercion
    have d88 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d44 d87
    have d89 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example77

namespace Example78
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d30 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d31 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d32 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d34 : (((3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d35 : ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : (((3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d39
    have d41 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d42 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d43 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d44 : x = x := by term_derivation_reflection
    have d45 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d46 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d47 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d43 d45 d46 eq_int_to_real_coercion eq_identity_coercion
    have d48 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d49 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d42 d48 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d50 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d51 : (((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d49 d50 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_rat_to_real_coercion d51
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d52 neg_rat_to_real_coercion
    have d54 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d55 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d56 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d56
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d54 d55 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d57
    have d59 : x = x := by term_derivation_reflection
    have d60 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d61 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d58 d59 d60 eq_rat_to_real_coercion eq_identity_coercion
    have d62 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d63 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d64 : y = y := by term_derivation_reflection
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d65
    have d67 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d63 d64 eq_identity_coercion eq_identity_coercion d66
    have d68 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d69 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d70 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d67 d68 eq_identity_coercion eq_int_to_real_coercion d69
    have d71 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d70 neg_nat_to_real_coercion
    have d72 : ((1:ℚ)/3:ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d73 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((3:ℕ) : ℝ) : ℝ) = ((3:ℕ) * ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d74 : ((3:ℕ) * ((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d75 : ((3:ℕ) * (0:ℕ) : ℕ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d76 : ((3:ℕ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d77 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d78 : ((3:ℕ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d76 d77 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d79 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d80 : x = x := by term_derivation_reflection
    have d81 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d82 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d83 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d79 d81 d82 eq_int_to_real_coercion eq_identity_coercion
    have d84 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d85 : ((3:ℕ) * ((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d74 d75 d78 d84 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion nat_nat_real_coercion_triangle nat_real_real_coercion_triangle nat_nat_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d86 : ((3:ℕ) * (1:ℕ) : ℕ) = (3:ℕ) := by term_derivation_mul_one
    have d87 : ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d88 : ((3:ℕ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d86 d87 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d89 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d90 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((3:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d73 d85 d88 d89 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion nat_real_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d91 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d90
    have d92 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d71 d72 eq_identity_coercion eq_rat_to_real_coercion d91
    have d93 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d94 : ((((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d95 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d92 d93 eq_identity_coercion eq_int_to_real_coercion d94
    have d96 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d95 neg_nat_to_real_coercion
    have d97 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d53 d96
    have d98 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example78

namespace Example79
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d30 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul_power_one
    have d31 : (((1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((-1:ℚ)/2:ℚ) + y : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d32
    have d34 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d33 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d35 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d36 : (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d35 d36 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d34 d37 d38 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d40 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d39
    have d41 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d40
    have d42 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d43 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d44 : y = y := by term_derivation_reflection
    have d45 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d46 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d47 : ((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_zero_add
    have d48 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = y := by term_derivation_sum_add_literal d43 d47 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d49 : (y + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d50 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d48 d49 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d51 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d41 d42 eq_identity_coercion eq_rat_to_real_coercion d50
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d51 neg_rat_to_real_coercion
    have d53 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d54 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d55 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d56 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d55
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d53 d54 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d56
    have d58 : x = x := by term_derivation_reflection
    have d59 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d60 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d57 d58 d59 eq_rat_to_real_coercion eq_identity_coercion
    have d61 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d62 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d63 : y = y := by term_derivation_reflection
    have d64 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d64
    have d66 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d62 d63 eq_identity_coercion eq_identity_coercion d65
    have d67 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d68 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d69 : ((1:ℕ) * (((1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d70 : (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_div_literal d69
    have d71 : (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_div_eq d67 d68 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d70
    have d72 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d73 : (-(((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_eq
    have d74 : ((-1:ℚ)/2:ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_reflection
    have d75 : ((0:ℕ) + ((-1:ℚ)/2:ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_zero_add
    have d76 : (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d77 : (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d75 d76 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion nat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d78 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d79 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d77 d78 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d80 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-(((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d66 d73 eq_identity_coercion eq_rat_to_real_coercion d79
    have d81 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d80 neg_rat_to_real_coercion
    have d82 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d83 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d84 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d83
    have d85 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d81 d82 eq_identity_coercion eq_nat_to_real_coercion d84
    have d86 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d87 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d88 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d85 d86 eq_identity_coercion eq_int_to_real_coercion d87
    have d89 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d88 neg_nat_to_real_coercion
    have d90 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d52 d89
    have d91 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example79

namespace Example80
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d30 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul_power_one
    have d31 : (((1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((-1:ℚ)/2:ℚ) + y : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d32
    have d34 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d33 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d35 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d36 : (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d35 d36 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d34 d37 d38 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d40 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d39
    have d41 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d40
    have d42 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d43 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d44 : y = y := by term_derivation_reflection
    have d45 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d46 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d47 : ((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_zero_add
    have d48 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = y := by term_derivation_sum_add_literal d43 d47 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d49 : (y + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d50 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d48 d49 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d51 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d41 d42 eq_identity_coercion eq_rat_to_real_coercion d50
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d51 neg_rat_to_real_coercion
    have d53 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d54 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d55 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d56 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d55
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d53 d54 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d56
    have d58 : x = x := by term_derivation_reflection
    have d59 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d60 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d57 d58 d59 eq_rat_to_real_coercion eq_identity_coercion
    have d61 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d62 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d63 : y = y := by term_derivation_reflection
    have d64 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d64
    have d66 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d62 d63 eq_identity_coercion eq_identity_coercion d65
    have d67 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d68 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d69 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d66 d67 eq_identity_coercion eq_int_to_real_coercion d68
    have d70 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d69 neg_nat_to_real_coercion
    have d71 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d72 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d73 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d72
    have d74 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d70 d71 eq_identity_coercion eq_nat_to_real_coercion d73
    have d75 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d76 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d77 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d74 d75 eq_identity_coercion eq_int_to_real_coercion d76
    have d78 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d77 neg_nat_to_real_coercion
    have d79 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d52 d78
    have d80 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example80

namespace Example81
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d30 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul_power_one
    have d31 : (((1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((-1:ℚ)/2:ℚ) + y : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d32
    have d34 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d33 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d35 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d36 : (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d35 d36 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d34 d37 d38 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d40 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d39
    have d41 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d40
    have d42 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d43 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d44 : y = y := by term_derivation_reflection
    have d45 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d46 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d47 : ((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_zero_add
    have d48 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = y := by term_derivation_sum_add_literal d43 d47 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d49 : (y + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d50 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d48 d49 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d51 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d41 d42 eq_identity_coercion eq_rat_to_real_coercion d50
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d51 neg_rat_to_real_coercion
    have d53 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d54 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d55 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d56 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d55
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d53 d54 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d56
    have d58 : x = x := by term_derivation_reflection
    have d59 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d60 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d57 d58 d59 eq_rat_to_real_coercion eq_identity_coercion
    have d61 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d62 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d63 : y = y := by term_derivation_reflection
    have d64 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d64
    have d66 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d62 d63 eq_identity_coercion eq_identity_coercion d65
    have d67 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d68 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d69 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d66 d67 eq_identity_coercion eq_int_to_real_coercion d68
    have d70 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d69 neg_nat_to_real_coercion
    have d71 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d72 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d73 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d72
    have d74 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d70 d71 eq_identity_coercion eq_nat_to_real_coercion d73
    have d75 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d76 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d77 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d74 d75 eq_identity_coercion eq_int_to_real_coercion d76
    have d78 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d77 neg_nat_to_real_coercion
    have d79 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d52 d78
    have d80 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example81

namespace Example82
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d30 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d31 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d32
    have d34 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d33 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d35 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-3:ℤ) := by term_derivation_literal_mul_literal
    have d36 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d35 d36 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d34 d37 d38 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d40 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d39
    have d41 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d40
    have d42 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d43 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d44 : x = x := by term_derivation_reflection
    have d45 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d46 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d47 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d48 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d43 d47 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d49 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d50 : (((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d48 d49 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d51 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d41 d42 eq_identity_coercion eq_rat_to_real_coercion d50
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d51 neg_rat_to_real_coercion
    have d53 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d54 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d55 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d56 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d55
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d53 d54 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d56
    have d58 : x = x := by term_derivation_reflection
    have d59 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d60 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d57 d58 d59 eq_rat_to_real_coercion eq_identity_coercion
    have d61 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d62 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d63 : y = y := by term_derivation_reflection
    have d64 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d64
    have d66 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d62 d63 eq_identity_coercion eq_identity_coercion d65
    have d67 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d68 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d69 : ((1:ℕ) * (((1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d70 : (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_div_literal d69
    have d71 : (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_div_eq d67 d68 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d70
    have d72 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d73 : (-(((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_eq
    have d74 : ((-1:ℚ)/2:ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_reflection
    have d75 : ((0:ℕ) + ((-1:ℚ)/2:ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_zero_add
    have d76 : (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d77 : (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d75 d76 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion nat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d78 : ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d79 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d77 d78 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d80 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-(((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d66 d73 eq_identity_coercion eq_rat_to_real_coercion d79
    have d81 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d80 neg_rat_to_real_coercion
    have d82 : ((-1:ℚ)/3:ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d83 : (((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = ((-3:ℤ) * (((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d84 : ((-3:ℤ) * (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d85 : ((-3:ℤ) * (((-1:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d86 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d87 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d88 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d86 d87 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d89 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d89
    have d91 : ((-3:ℤ) * (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d84 d85 d88 d90 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_rat_real_coercion_triangle int_real_real_coercion_triangle rat_rat_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d92 : ((-3:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_mul_one
    have d93 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d94 : ((-3:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d92 d93 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d95 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d96 : (((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d83 d91 d94 d95 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d97 : (((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d96
    have d98 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d81 d82 eq_identity_coercion eq_rat_to_real_coercion d97
    have d99 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d100 : (((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d101 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d98 d99 eq_identity_coercion eq_int_to_real_coercion d100
    have d102 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d101 neg_nat_to_real_coercion
    have d103 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d52 d102
    have d104 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example82

namespace Example83
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d30 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d31 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d32
    have d34 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d33 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d35 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-3:ℤ) := by term_derivation_literal_mul_literal
    have d36 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d35 d36 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d34 d37 d38 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d40 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d39
    have d41 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d40
    have d42 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d43 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d44 : x = x := by term_derivation_reflection
    have d45 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d46 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d47 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d48 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d43 d47 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d49 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d50 : (((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d48 d49 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d51 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d41 d42 eq_identity_coercion eq_rat_to_real_coercion d50
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d51 neg_rat_to_real_coercion
    have d53 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d54 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d55 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d56 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d55
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d53 d54 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d56
    have d58 : x = x := by term_derivation_reflection
    have d59 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d60 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d57 d58 d59 eq_rat_to_real_coercion eq_identity_coercion
    have d61 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d62 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d63 : y = y := by term_derivation_reflection
    have d64 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d64
    have d66 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d62 d63 eq_identity_coercion eq_identity_coercion d65
    have d67 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d68 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d69 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d70 : ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d71 : (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d69 d70 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d72 : (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d73 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d71 d72 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d74 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d66 d67 eq_identity_coercion eq_int_to_real_coercion d73
    have d75 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d74 neg_nat_to_real_coercion
    have d76 : ((-1:ℚ)/3:ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d77 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = ((-3:ℤ) * ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d78 : ((-3:ℤ) * ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d79 : ((-3:ℤ) * (-1:ℤ) : ℤ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d80 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d81 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d82 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d80 d81 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d83 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d84 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d83
    have d85 : ((-3:ℤ) * ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d78 d79 d82 d84 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d86 : ((-3:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_mul_one
    have d87 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d88 : ((-3:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d86 d87 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d89 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d77 d85 d88 d89 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d91 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d90
    have d92 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d75 d76 eq_identity_coercion eq_rat_to_real_coercion d91
    have d93 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d94 : ((((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d95 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d92 d93 eq_identity_coercion eq_int_to_real_coercion d94
    have d96 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d95 neg_nat_to_real_coercion
    have d97 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d52 d96
    have d98 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example83

namespace Example84
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((-1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d30 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d31 : (((-1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d32 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d34 : (((-1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d35 : (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : (((-1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d42 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d43 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d44 : y = y := by term_derivation_reflection
    have d45 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d46 : ((-1:ℤ) * y : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d47 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d43 d45 d46 eq_int_to_real_coercion eq_identity_coercion
    have d48 : ((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d49 : ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d42 d48 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d50 : (((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d51 : (((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d49 d50 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_rat_to_real_coercion d51
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d52 neg_rat_to_real_coercion
    have d54 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d55 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d56 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d56
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d54 d55 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d57
    have d59 : x = x := by term_derivation_reflection
    have d60 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d61 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d58 d59 d60 eq_rat_to_real_coercion eq_identity_coercion
    have d62 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d63 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d64 : y = y := by term_derivation_reflection
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d65
    have d67 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d63 d64 eq_identity_coercion eq_identity_coercion d66
    have d68 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d69 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d70 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d71 : ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d72 : (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d70 d71 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d73 : (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d74 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d72 d73 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d75 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d67 d68 eq_identity_coercion eq_int_to_real_coercion d74
    have d76 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d75 neg_nat_to_real_coercion
    have d77 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d78 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d79 : ((-1:ℤ) * ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d80 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d81 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d82 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d83 : ((-1:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d81 d82 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d84 : ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d85 : ((-1:ℤ) * ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d79 d80 d83 d84 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d86 : ((-1:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d87 : (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d88 : ((-1:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d86 d87 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d89 : (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d78 d85 d88 d89 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d91 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d90
    have d92 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d76 d77 eq_identity_coercion eq_int_to_real_coercion d91
    have d93 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d94 : ((((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d95 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d92 d93 eq_identity_coercion eq_int_to_real_coercion d94
    have d96 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d95 neg_nat_to_real_coercion
    have d97 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d53 d96
    have d98 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example84

namespace Example85
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((-1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d30 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d31 : (((-1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d32 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d34 : (((-1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d35 : (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d36 : (((-1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d34 d35 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d37 : ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d33 d36 d37 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d39 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d38
    have d40 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d42 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d43 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d44 : y = y := by term_derivation_reflection
    have d45 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d46 : ((-1:ℤ) * y : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d47 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d43 d45 d46 eq_int_to_real_coercion eq_identity_coercion
    have d48 : ((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d49 : ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d42 d48 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d50 : (((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d51 : (((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d49 d50 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d40 d41 eq_identity_coercion eq_rat_to_real_coercion d51
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d52 neg_rat_to_real_coercion
    have d54 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d55 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d56 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d56
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d54 d55 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d57
    have d59 : x = x := by term_derivation_reflection
    have d60 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d61 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d58 d59 d60 eq_rat_to_real_coercion eq_identity_coercion
    have d62 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d63 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d64 : y = y := by term_derivation_reflection
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d65
    have d67 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d63 d64 eq_identity_coercion eq_identity_coercion d66
    have d68 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d69 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d70 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d71 : ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d72 : (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d70 d71 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d73 : (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d74 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d72 d73 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d75 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d67 d68 eq_identity_coercion eq_int_to_real_coercion d74
    have d76 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d75 neg_nat_to_real_coercion
    have d77 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d78 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d79 : ((-1:ℤ) * ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d80 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d81 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d82 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d83 : ((-1:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d81 d82 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d84 : ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d85 : ((-1:ℤ) * ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d79 d80 d83 d84 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d86 : ((-1:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d87 : (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d88 : ((-1:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d86 d87 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d89 : (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d78 d85 d88 d89 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d91 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d90
    have d92 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d76 d77 eq_identity_coercion eq_int_to_real_coercion d91
    have d93 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d94 : ((((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d95 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d92 d93 eq_identity_coercion eq_int_to_real_coercion d94
    have d96 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d95 neg_nat_to_real_coercion
    have d97 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d53 d96
    have d98 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example85

namespace Example86
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d1 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d2 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d3 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d2
    have d4 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d d1 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d3
    have d5 : x = x := by term_derivation_reflection
    have d6 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d7 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d4 d5 d6 eq_rat_to_real_coercion eq_identity_coercion
    have d8 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d9 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d10 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d11 : y = y := by term_derivation_reflection
    have d12 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d13 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d10 d11 d12 eq_nat_to_real_coercion eq_identity_coercion
    have d14 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d9 d13 eq_identity_coercion eq_identity_coercion d14
    have d16 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d17 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d18 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d19 : ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d20 : (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d19 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d21 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d23 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d15 d16 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d26 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d27 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d29 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d30 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d31 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d29 d30 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d32 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d32
    have d34 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d27 d28 d31 d33 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d35 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-3:ℤ) := by term_derivation_literal_mul_literal
    have d36 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d37 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d35 d36 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d26 d34 d37 d38 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d40 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d39
    have d41 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_rat_to_real_coercion d40
    have d42 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d43 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d44 : x = x := by term_derivation_reflection
    have d45 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d46 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d47 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d48 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d43 d47 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d49 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d50 : (((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d48 d49 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d51 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d41 d42 eq_identity_coercion eq_rat_to_real_coercion d50
    have d52 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d51 neg_rat_to_real_coercion
    have d53 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d54 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d55 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d56 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d55
    have d57 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d53 d54 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d56
    have d58 : x = x := by term_derivation_reflection
    have d59 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d60 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d57 d58 d59 eq_rat_to_real_coercion eq_identity_coercion
    have d61 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d62 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq
    have d63 : y = y := by term_derivation_reflection
    have d64 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less
    have d65 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d64
    have d66 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d62 d63 eq_identity_coercion eq_identity_coercion d65
    have d67 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d68 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d69 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d70 : ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d71 : (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d69 d70 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d72 : (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d73 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d71 d72 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d74 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d66 d67 eq_identity_coercion eq_int_to_real_coercion d73
    have d75 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d74 neg_nat_to_real_coercion
    have d76 : ((-1:ℚ)/3:ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d77 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = ((-3:ℤ) * ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d78 : ((-3:ℤ) * ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d79 : ((-3:ℤ) * (-1:ℤ) : ℤ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d80 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d81 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d82 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d80 d81 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d83 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d84 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d83
    have d85 : ((-3:ℤ) * ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d78 d79 d82 d84 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d86 : ((-3:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_mul_one
    have d87 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d88 : ((-3:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d86 d87 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d89 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d77 d85 d88 d89 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d91 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d90
    have d92 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d75 d76 eq_identity_coercion eq_rat_to_real_coercion d91
    have d93 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d94 : ((((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d95 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d92 d93 eq_identity_coercion eq_int_to_real_coercion d94
    have d96 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d95 neg_nat_to_real_coercion
    have d97 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d52 d96
    have d98 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish
    assumption
  exact ()
end Example86

namespace Example87
def h := by
  have h1 : (0:ℕ) < (2:ℕ) := by calc
    (0:ℕ) < (1:ℕ) := by obvious
    _ < (2:ℕ) := by obvious
  exact ()
end Example87

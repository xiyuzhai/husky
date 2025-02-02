
import Mathlib
import Visored.Tactics

set_option maxHeartbeats 1000000000
set_option diagnostics true
set_option diagnostics.threshold 1000000000

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
    have d : x > ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : x > ((0:ℕ) : ℝ) ↔ ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d9 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d8
    have d10 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_nat_to_real_coercion d9
    have d11 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d12 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d13 : x = x := by term_derivation_reflection
    have d14 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d15 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d16 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d17 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d12 d16 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d18 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d10 d11 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d18 neg_int_to_real_coercion
    have d20 : x = x := by term_derivation_reflection
    have d21 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d22 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d23 : (x + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (x - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d26 : (x * ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_mul_one
    have d27 : (x / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_literal d26
    have d28 : ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d27
    have d29 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d30 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d31 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d19 d32
    have d34 : x > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d33 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example38

namespace Example39
def h (x : ℝ) (h1 : x > ((1:ℕ) : ℝ)) := by
  have h2 : x ≥ ((1:ℕ) : ℝ) := by
    have d : x > ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : x ≥ ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d9 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d8
    have d10 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_nat_to_real_coercion d9
    have d11 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d12 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d13 : x = x := by term_derivation_reflection
    have d14 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d15 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d16 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d17 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d12 d16 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d18 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d10 d11 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d18 neg_int_to_real_coercion
    have d20 : x = x := by term_derivation_reflection
    have d21 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d22 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d23 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d26 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d27 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d26
    have d28 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d27
    have d29 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d30 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d31 : x = x := by term_derivation_reflection
    have d32 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d33 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d34 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d35 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d30 d34 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d36 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d35
    have d37 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d36 neg_int_to_real_coercion
    have d38 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d19 d37
    have d39 : x ≥ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d38 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example39

namespace Example40
def h (x : ℝ) (h1 : x ≥ ((1:ℕ) : ℝ)) := by
  have h2 : x ≥ ((0:ℕ) : ℝ) := by
    have d : x ≥ ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : x ≥ ((0:ℕ) : ℝ) ↔ ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d9 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d8
    have d10 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_nat_to_real_coercion d9
    have d11 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d12 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d13 : x = x := by term_derivation_reflection
    have d14 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d15 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d16 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d17 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d12 d16 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d18 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d10 d11 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d18 neg_int_to_real_coercion
    have d20 : x = x := by term_derivation_reflection
    have d21 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d22 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d23 : (x + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (x - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d26 : (x * ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_mul_one
    have d27 : (x / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_literal d26
    have d28 : ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d27
    have d29 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d30 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d31 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d19 d32
    have d34 : x ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d33 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example40

namespace Example41
def h (x : ℝ) (h1 : x ≥ ((1:ℕ) : ℝ)) := by
  have h2 : x > ((0:ℕ) : ℝ) := by
    have d : x ≥ ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : x > ((0:ℕ) : ℝ) ↔ ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d9 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d8
    have d10 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_nat_to_real_coercion d9
    have d11 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d12 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d13 : x = x := by term_derivation_reflection
    have d14 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d15 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d16 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d17 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d12 d16 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d18 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d10 d11 eq_identity_coercion eq_int_to_real_coercion d17
    have d19 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d18 neg_int_to_real_coercion
    have d20 : x = x := by term_derivation_reflection
    have d21 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d22 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d23 : (x + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_int_to_real_coercion d22
    have d24 : (x - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d26 : (x * ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_mul_one
    have d27 : (x / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_literal d26
    have d28 : ((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_div_eq d24 d25 eq_identity_coercion eq_nat_to_real_coercion d27
    have d29 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d30 : (x + ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_nf_add_zero
    have d31 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = (((x - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d19 d32
    have d34 : x > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d33 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example41

namespace Example42
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((1:ℕ) : ℝ) := by
    have d : x < ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : x ≤ ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d11 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d13 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d14
    have d16 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d18 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d23 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d19 d21 d22 eq_int_to_real_coercion eq_identity_coercion
    have d24 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d25 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d24 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d26 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d16 d17 eq_identity_coercion eq_int_to_real_coercion d25
    have d27 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d26 neg_nat_to_real_coercion
    have d28 : x = x := by term_derivation_reflection
    have d29 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d30 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d31 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d34 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d35 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d37 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d40 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d34 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d32 d33 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d44 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d45 d47 d48 eq_int_to_real_coercion eq_identity_coercion
    have d50 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d51 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d44 d50 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d52 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d52 neg_nat_to_real_coercion
    have d54 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d27 d53
    have d55 : x ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d54 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example42

namespace Example43
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x < ((2:ℕ) : ℝ) := by
    have d : x < ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : x < ((2:ℕ) : ℝ) ↔ ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d11 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d13 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d14
    have d16 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d18 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d23 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d19 d21 d22 eq_int_to_real_coercion eq_identity_coercion
    have d24 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d25 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d24 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d26 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d16 d17 eq_identity_coercion eq_int_to_real_coercion d25
    have d27 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d26 neg_nat_to_real_coercion
    have d28 : x = x := by term_derivation_reflection
    have d29 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d30 : (x + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d31 : (x + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : (x - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d34 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d35 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d37 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d40 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d34 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d32 d33 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d44 : ((2:ℕ) + (-2:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d45 d47 d48 eq_int_to_real_coercion eq_identity_coercion
    have d50 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d51 : (((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d44 d50 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d52 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d52 neg_nat_to_real_coercion
    have d54 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d27 d53
    have d55 : x < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d54 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example43

namespace Example44
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((2:ℕ) : ℝ) := by
    have d : x < ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : x ≤ ((2:ℕ) : ℝ) ↔ ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d11 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d13 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d14
    have d16 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d18 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d23 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d19 d21 d22 eq_int_to_real_coercion eq_identity_coercion
    have d24 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d25 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d24 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d26 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d16 d17 eq_identity_coercion eq_int_to_real_coercion d25
    have d27 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d26 neg_nat_to_real_coercion
    have d28 : x = x := by term_derivation_reflection
    have d29 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d30 : (x + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d31 : (x + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : (x - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d34 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d35 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d37 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d40 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d34 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d32 d33 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d44 : ((2:ℕ) + (-2:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d45 d47 d48 eq_int_to_real_coercion eq_identity_coercion
    have d50 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d51 : (((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d44 d50 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d52 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d52 neg_nat_to_real_coercion
    have d54 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d27 d53
    have d55 : x ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d54 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example44

namespace Example45
def h (x : ℝ) (h1 : x ≤ ((1:ℕ) : ℝ)) := by
  have h2 : x < ((2:ℕ) : ℝ) := by
    have d : x ≤ ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : x < ((2:ℕ) : ℝ) ↔ ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d11 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d13 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d14
    have d16 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d18 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d23 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d19 d21 d22 eq_int_to_real_coercion eq_identity_coercion
    have d24 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d25 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d24 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d26 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d16 d17 eq_identity_coercion eq_int_to_real_coercion d25
    have d27 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d26 neg_nat_to_real_coercion
    have d28 : x = x := by term_derivation_reflection
    have d29 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d30 : (x + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d31 : (x + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : (x - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d34 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d35 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d37 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d40 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d34 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d32 d33 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d44 : ((2:ℕ) + (-2:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d45 d47 d48 eq_int_to_real_coercion eq_identity_coercion
    have d50 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d51 : (((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d44 d50 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d52 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d52 neg_nat_to_real_coercion
    have d54 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d27 d53
    have d55 : x < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d54 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example45

namespace Example46
def h (x : ℝ) (h1 : x ≤ ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((2:ℕ) : ℝ) := by
    have d : x ≤ ((1:ℕ) : ℝ) ↔ ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : x ≤ ((2:ℕ) : ℝ) ↔ ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (x + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d5 : (x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : (x - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d11 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d12 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d13 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d15 : (((-1:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d14
    have d16 : ((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d15
    have d17 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d18 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d23 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d19 d21 d22 eq_int_to_real_coercion eq_identity_coercion
    have d24 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d25 : (((1:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d18 d24 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d26 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d16 d17 eq_identity_coercion eq_int_to_real_coercion d25
    have d27 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d26 neg_nat_to_real_coercion
    have d28 : x = x := by term_derivation_reflection
    have d29 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d30 : (x + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_non_zero_literal
    have d31 : (x + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d28 d29 eq_identity_coercion eq_int_to_real_coercion d30
    have d32 : (x - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_nat_to_real_coercion
    have d33 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d34 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d35 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d37 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : ((-1:ℤ) * ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d40 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d34 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-2:ℤ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d32 d33 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d44 : ((2:ℕ) + (-2:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d45 d47 d48 eq_int_to_real_coercion eq_identity_coercion
    have d50 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d51 : (((2:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d44 d50 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d52 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d52 neg_nat_to_real_coercion
    have d54 : (((x - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((x - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d27 d53
    have d55 : x ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d54 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
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
    have d : (- x : ℝ) > ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : (- x : ℝ) > ((0:ℕ) : ℝ) ↔ (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d9 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d8
    have d10 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_nat_to_real_coercion d9
    have d11 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d12 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d13 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d14 : x = x := by term_derivation_reflection
    have d15 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d16 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d17 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d13 d15 d16 eq_int_to_real_coercion eq_identity_coercion
    have d18 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d19 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d12 d18 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d20 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d10 d11 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d20 neg_int_to_real_coercion
    have d22 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d23 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d24 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d25 : ((- x : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d28 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d29 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d28
    have d30 : (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_nat_to_real_coercion d29
    have d31 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d32 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d33 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d32
    have d34 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d33 neg_nat_to_real_coercion
    have d35 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d21 d34
    have d36 : (- x : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d35 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example48

namespace Example49
def h (x : ℝ) (h1 : (- x : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≥ ((1:ℕ) : ℝ) := by
    have d : (- x : ℝ) > ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : (- x : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d9 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d8
    have d10 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_nat_to_real_coercion d9
    have d11 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d12 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d13 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d14 : x = x := by term_derivation_reflection
    have d15 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d16 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d17 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d13 d15 d16 eq_int_to_real_coercion eq_identity_coercion
    have d18 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d19 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d12 d18 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d20 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d10 d11 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d20 neg_int_to_real_coercion
    have d22 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d23 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d24 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d25 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d28 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d29 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d28
    have d30 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_nat_to_real_coercion d29
    have d31 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d32 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d33 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d34 : x = x := by term_derivation_reflection
    have d35 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d36 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d37 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d33 d35 d36 eq_int_to_real_coercion eq_identity_coercion
    have d38 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d39 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d32 d38 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d40 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d40 neg_int_to_real_coercion
    have d42 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d21 d41
    have d43 : (- x : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d42 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example49

namespace Example50
def h (x : ℝ) (h1 : (- x : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : (- x : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : (- x : ℝ) ≥ ((0:ℕ) : ℝ) ↔ (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d9 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d8
    have d10 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_nat_to_real_coercion d9
    have d11 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d12 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d13 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d14 : x = x := by term_derivation_reflection
    have d15 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d16 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d17 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d13 d15 d16 eq_int_to_real_coercion eq_identity_coercion
    have d18 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d19 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d12 d18 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d20 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d10 d11 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d20 neg_int_to_real_coercion
    have d22 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d23 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d24 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d25 : ((- x : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d28 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d29 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d28
    have d30 : (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_nat_to_real_coercion d29
    have d31 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d32 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d33 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d32
    have d34 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d33 neg_nat_to_real_coercion
    have d35 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d21 d34
    have d36 : (- x : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d35 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example50

namespace Example51
def h (x : ℝ) (h1 : (- x : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (- x : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : (- x : ℝ) > ((0:ℕ) : ℝ) ↔ (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d9 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d8
    have d10 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_nat_to_real_coercion d9
    have d11 : (-(-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_neg_literal
    have d12 : ((-1:ℤ) + ((1:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d13 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d14 : x = x := by term_derivation_reflection
    have d15 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d16 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d17 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d13 d15 d16 eq_int_to_real_coercion eq_identity_coercion
    have d18 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d19 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d12 d18 comm_ring_add_identity_coercion int_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion int_int_real_coercion_triangle nat_int_real_coercion_triangle
    have d20 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(-1:ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d10 d11 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d20 neg_int_to_real_coercion
    have d22 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d23 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d24 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d25 : ((- x : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d28 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d29 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d28
    have d30 : (((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_nat_to_real_coercion d29
    have d31 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d32 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d33 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d30 d31 eq_identity_coercion eq_int_to_real_coercion d32
    have d34 : ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d33 neg_nat_to_real_coercion
    have d35 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((-1:ℤ) : ℝ) : ℝ) = ((((- x : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d21 d34
    have d36 : (- x : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d35 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example51

namespace Example52
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : (- x : ℝ) < ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (- x : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d11 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d12 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d13
    have d15 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d14 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d16 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d15
    have d17 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d23 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d24 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d19 d23 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d25 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d28 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d29 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d30 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d27 d28 eq_identity_coercion eq_int_to_real_coercion d29
    have d31 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d30 neg_nat_to_real_coercion
    have d32 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d33 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d34 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d35 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d37 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d35 d36 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d38
    have d40 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d33 d34 d37 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d31 d32 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d44 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : x = x := by term_derivation_reflection
    have d46 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d47 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d48 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d49 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d44 d48 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d50 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d50 neg_nat_to_real_coercion
    have d52 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d26 d51
    have d53 : (- x : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d52 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example52

namespace Example53
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (- x : ℝ) < ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (- x : ℝ) < ((2:ℕ) : ℝ) ↔ (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d11 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d12 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d13
    have d15 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d14 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d16 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d15
    have d17 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d23 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d24 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d19 d23 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d25 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d28 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d29 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d30 : ((- x : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d27 d28 eq_identity_coercion eq_int_to_real_coercion d29
    have d31 : ((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d30 neg_nat_to_real_coercion
    have d32 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d33 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d34 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d35 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d37 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d35 d36 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((2:ℕ) + x : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d38
    have d40 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d33 d34 d37 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d31 d32 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d44 : ((2:ℕ) + (-2:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : x = x := by term_derivation_reflection
    have d46 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d47 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d48 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d49 : (((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d44 d48 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d50 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d50 neg_nat_to_real_coercion
    have d52 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d26 d51
    have d53 : (- x : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d52 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example53

namespace Example54
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (- x : ℝ) < ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) ↔ (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d11 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d12 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d13
    have d15 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d14 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d16 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d15
    have d17 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d23 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d24 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d19 d23 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d25 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d28 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d29 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d30 : ((- x : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d27 d28 eq_identity_coercion eq_int_to_real_coercion d29
    have d31 : ((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d30 neg_nat_to_real_coercion
    have d32 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d33 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d34 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d35 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d37 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d35 d36 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((2:ℕ) + x : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d38
    have d40 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d33 d34 d37 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d31 d32 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d44 : ((2:ℕ) + (-2:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : x = x := by term_derivation_reflection
    have d46 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d47 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d48 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d49 : (((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d44 d48 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d50 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d50 neg_nat_to_real_coercion
    have d52 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d26 d51
    have d53 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d52 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example54

namespace Example55
def h (x : ℝ) (h1 : (- x : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (- x : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : (- x : ℝ) < ((2:ℕ) : ℝ) ↔ (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d11 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d12 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d13
    have d15 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d14 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d16 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d15
    have d17 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d23 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d24 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d19 d23 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d25 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d28 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d29 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d30 : ((- x : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d27 d28 eq_identity_coercion eq_int_to_real_coercion d29
    have d31 : ((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d30 neg_nat_to_real_coercion
    have d32 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d33 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d34 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d35 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d37 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d35 d36 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((2:ℕ) + x : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d38
    have d40 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d33 d34 d37 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d31 d32 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d44 : ((2:ℕ) + (-2:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : x = x := by term_derivation_reflection
    have d46 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d47 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d48 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d49 : (((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d44 d48 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d50 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d50 neg_nat_to_real_coercion
    have d52 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d26 d51
    have d53 : (- x : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d52 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example55

namespace Example56
def h (x : ℝ) (h1 : (- x : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (- x : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) ↔ (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d5 : ((- x : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : ((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d8 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d9 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d10 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d11 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d12 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d10 d11 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d13 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d14 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d13
    have d15 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d8 d9 d12 d14 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d16 : (((-1:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d15
    have d17 : (((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d6 d7 eq_identity_coercion eq_int_to_real_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d20 : x = x := by term_derivation_reflection
    have d21 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d22 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d23 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d24 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d19 d23 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d25 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (- x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_atom
    have d28 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d29 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d30 : ((- x : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d27 d28 eq_identity_coercion eq_int_to_real_coercion d29
    have d31 : ((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d30 neg_nat_to_real_coercion
    have d32 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d33 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d34 : ((-1:ℤ) * (-2:ℤ) : ℤ) = (2:ℕ) := by term_derivation_literal_mul_literal
    have d35 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d36 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d37 : ((-1:ℤ) * ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d35 d36 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d38 : ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : ((2:ℕ) + x : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d38
    have d40 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d33 d34 d37 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : (((-2:ℤ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : (((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = ((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d31 d32 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d44 : ((2:ℕ) + (-2:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : x = x := by term_derivation_reflection
    have d46 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d47 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d48 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d49 : (((2:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d44 d48 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d50 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d49
    have d51 : ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d50 neg_nat_to_real_coercion
    have d52 : ((((- x : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((((- x : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d26 d51
    have d53 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d52 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
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
    have d : (-((2:ℕ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d16 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d18 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d19
    have d21 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_nat_to_real_coercion d20
    have d22 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d23 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d24 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d24 d26 d27 eq_int_to_real_coercion eq_identity_coercion
    have d29 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d30 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d23 d29 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d21 d22 eq_identity_coercion eq_rat_to_real_coercion d30
    have d32 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_rat_to_real_coercion
    have d33 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d34 : x = x := by term_derivation_reflection
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d36 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d33 d34 d35 eq_nat_to_real_coercion eq_identity_coercion
    have d37 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d38 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d36 d37
    have d39 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d40 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d38 d39 eq_identity_coercion eq_int_to_real_coercion d40
    have d42 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d41 neg_nat_to_real_coercion
    have d43 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d44 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d45 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d44
    have d46 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d42 d43 eq_identity_coercion eq_nat_to_real_coercion d45
    have d47 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d48 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d49 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d46 d47 eq_identity_coercion eq_int_to_real_coercion d48
    have d50 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d49 neg_nat_to_real_coercion
    have d51 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d32 d50
    have d52 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d51 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example58

namespace Example59
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) := by
    have d : (-((2:ℕ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d16 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d18 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d19
    have d21 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_nat_to_real_coercion d20
    have d22 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d23 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d24 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d24 d26 d27 eq_int_to_real_coercion eq_identity_coercion
    have d29 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d30 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d23 d29 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d21 d22 eq_identity_coercion eq_rat_to_real_coercion d30
    have d32 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_rat_to_real_coercion
    have d33 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d34 : x = x := by term_derivation_reflection
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d36 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d33 d34 d35 eq_nat_to_real_coercion eq_identity_coercion
    have d37 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d38 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d36 d37
    have d39 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d40 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d38 d39 eq_identity_coercion eq_int_to_real_coercion d40
    have d42 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d41 neg_nat_to_real_coercion
    have d43 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d44 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d45 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d46 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d47 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d48 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d46 d47 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d49 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d50 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d44 d45 d48 d49 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d51 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d42 d43 eq_identity_coercion eq_nat_to_real_coercion d51
    have d53 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d54 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d55 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d56 : x = x := by term_derivation_reflection
    have d57 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d58 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d59 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d55 d57 d58 eq_int_to_real_coercion eq_identity_coercion
    have d60 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d61 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d54 d60 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d62 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_rat_to_real_coercion d61
    have d63 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d62 neg_rat_to_real_coercion
    have d64 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d32 d63
    have d65 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d64 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example59

namespace Example60
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d16 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d18 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d19
    have d21 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_nat_to_real_coercion d20
    have d22 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d23 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d24 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d24 d26 d27 eq_int_to_real_coercion eq_identity_coercion
    have d29 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d30 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d23 d29 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d21 d22 eq_identity_coercion eq_rat_to_real_coercion d30
    have d32 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_rat_to_real_coercion
    have d33 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d34 : x = x := by term_derivation_reflection
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d36 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d33 d34 d35 eq_nat_to_real_coercion eq_identity_coercion
    have d37 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d38 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d36 d37
    have d39 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d40 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d38 d39 eq_identity_coercion eq_int_to_real_coercion d40
    have d42 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d41 neg_nat_to_real_coercion
    have d43 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d44 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d45 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d44
    have d46 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d42 d43 eq_identity_coercion eq_nat_to_real_coercion d45
    have d47 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d48 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d49 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d46 d47 eq_identity_coercion eq_int_to_real_coercion d48
    have d50 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d49 neg_nat_to_real_coercion
    have d51 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d32 d50
    have d52 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d51 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example60

namespace Example61
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (-((2:ℕ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d16 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d17 : (((1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d18 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d19
    have d21 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_nat_to_real_coercion d20
    have d22 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d23 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d24 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d28 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d24 d26 d27 eq_int_to_real_coercion eq_identity_coercion
    have d29 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d30 : ((((-1:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d23 d29 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d21 d22 eq_identity_coercion eq_rat_to_real_coercion d30
    have d32 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d31 neg_rat_to_real_coercion
    have d33 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d34 : x = x := by term_derivation_reflection
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d36 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d33 d34 d35 eq_nat_to_real_coercion eq_identity_coercion
    have d37 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d38 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d36 d37
    have d39 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d40 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d38 d39 eq_identity_coercion eq_int_to_real_coercion d40
    have d42 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d41 neg_nat_to_real_coercion
    have d43 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d44 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d45 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d44
    have d46 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d42 d43 eq_identity_coercion eq_nat_to_real_coercion d45
    have d47 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d48 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d49 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d46 d47 eq_identity_coercion eq_int_to_real_coercion d48
    have d50 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d49 neg_nat_to_real_coercion
    have d51 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d32 d50
    have d52 : (-((2:ℕ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d51 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example61

namespace Example62
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d16 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d17 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d18
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d19 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d21 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d20
    have d22 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d21
    have d23 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d24 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d28 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d29 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d24 d28 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_rat_to_real_coercion d29
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d30 neg_rat_to_real_coercion
    have d32 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d33 : x = x := by term_derivation_reflection
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d32 d33 d34 eq_nat_to_real_coercion eq_identity_coercion
    have d36 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d37 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d35 d36
    have d38 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d39 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d37 d38 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d40 neg_nat_to_real_coercion
    have d42 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d43 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d44 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d46 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d47 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d45 d46 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d48 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d49 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d48
    have d50 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d43 d44 d47 d49 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d51 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d41 d42 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d54 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d55 : x = x := by term_derivation_reflection
    have d56 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d57 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d58 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d59 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d54 d58 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d60 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_rat_to_real_coercion d59
    have d61 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d60 neg_rat_to_real_coercion
    have d62 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d31 d61
    have d63 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d62 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example62

namespace Example63
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d16 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d17 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d18
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d19 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d21 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d20
    have d22 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d21
    have d23 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d24 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d28 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d29 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d24 d28 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_rat_to_real_coercion d29
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d30 neg_rat_to_real_coercion
    have d32 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d33 : x = x := by term_derivation_reflection
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d32 d33 d34 eq_nat_to_real_coercion eq_identity_coercion
    have d36 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d37 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d35 d36
    have d38 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d39 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d37 d38 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d40 neg_nat_to_real_coercion
    have d42 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d43 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d44 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d46 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d47 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d45 d46 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d48 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d49 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d48
    have d50 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d43 d44 d47 d49 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d51 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d41 d42 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d54 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d55 : x = x := by term_derivation_reflection
    have d56 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d57 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d58 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d59 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d54 d58 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d60 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_int_to_real_coercion d59
    have d61 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d60 neg_nat_to_real_coercion
    have d62 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d31 d61
    have d63 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d62 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example63

namespace Example64
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (-((2:ℕ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d16 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d17 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d18
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d19 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d21 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d20
    have d22 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d21
    have d23 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d24 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d28 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d29 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d24 d28 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_rat_to_real_coercion d29
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d30 neg_rat_to_real_coercion
    have d32 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d33 : x = x := by term_derivation_reflection
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d32 d33 d34 eq_nat_to_real_coercion eq_identity_coercion
    have d36 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d37 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d35 d36
    have d38 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d39 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d37 d38 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d40 neg_nat_to_real_coercion
    have d42 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d43 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d44 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d46 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d47 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d45 d46 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d48 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d49 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d48
    have d50 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d43 d44 d47 d49 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d51 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d41 d42 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d54 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d55 : x = x := by term_derivation_reflection
    have d56 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d57 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d58 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d59 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d54 d58 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d60 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_int_to_real_coercion d59
    have d61 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d60 neg_nat_to_real_coercion
    have d62 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d31 d61
    have d63 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d62 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example64

namespace Example65
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d16 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d17 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d18
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d19 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d21 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d20
    have d22 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d21
    have d23 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d24 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d28 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d29 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d24 d28 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_rat_to_real_coercion d29
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d30 neg_rat_to_real_coercion
    have d32 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d33 : x = x := by term_derivation_reflection
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d32 d33 d34 eq_nat_to_real_coercion eq_identity_coercion
    have d36 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d37 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d35 d36
    have d38 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d39 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d37 d38 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d40 neg_nat_to_real_coercion
    have d42 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d43 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d44 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d46 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d47 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d45 d46 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d48 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d49 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d48
    have d50 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d43 d44 d47 d49 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d51 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d41 d42 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d54 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d55 : x = x := by term_derivation_reflection
    have d56 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d57 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d58 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d59 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d54 d58 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d60 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_int_to_real_coercion d59
    have d61 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d60 neg_nat_to_real_coercion
    have d62 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d31 d61
    have d63 : (-((2:ℕ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d62 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example65

namespace Example66
def h (x : ℝ) (h1 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) ↔ (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : x = x := by term_derivation_reflection
    have d4 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d5 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d2 d3 d4 eq_nat_to_real_coercion eq_identity_coercion
    have d6 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d7 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d5 d6
    have d8 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d9 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d10 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d7 d8 eq_identity_coercion eq_int_to_real_coercion d9
    have d11 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d10 neg_nat_to_real_coercion
    have d12 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d13 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d14 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d15 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d16 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d17 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d15 d16 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d18 : (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d19 : (((1:ℚ)/2:ℚ) + x : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d18
    have d20 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d13 d14 d17 d19 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d21 : (((-1:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d20
    have d22 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d21
    have d23 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d24 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d25 : x = x := by term_derivation_reflection
    have d26 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d27 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d28 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d29 : ((((1:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d24 d28 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d30 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d22 d23 eq_identity_coercion eq_rat_to_real_coercion d29
    have d31 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d30 neg_rat_to_real_coercion
    have d32 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d33 : x = x := by term_derivation_reflection
    have d34 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d35 : ((2:ℕ) * x : ℝ) = ((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d32 d33 d34 eq_nat_to_real_coercion eq_identity_coercion
    have d36 : (-((2:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d37 : (-((2:ℕ) * x : ℝ) : ℝ) = ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d35 d36
    have d38 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d39 : (((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d40 : ((-((2:ℕ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d37 d38 eq_identity_coercion eq_int_to_real_coercion d39
    have d41 : ((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d40 neg_nat_to_real_coercion
    have d42 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d43 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d44 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d45 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d46 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d47 : (((-1:ℚ)/2:ℚ) * ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d45 d46 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d48 : ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d49 : ((1:ℕ) + x : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d48
    have d50 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d43 d44 d47 d49 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d51 : (((-2:ℤ) + ((-2:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d50
    have d52 : (((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d41 d42 eq_identity_coercion eq_int_to_real_coercion d51
    have d53 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d54 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d55 : x = x := by term_derivation_reflection
    have d56 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d57 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d58 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d59 : (((1:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d54 d58 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d60 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d52 d53 eq_identity_coercion eq_int_to_real_coercion d59
    have d61 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d60 neg_nat_to_real_coercion
    have d62 : ((((-((2:ℕ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((2:ℕ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d31 d61
    have d63 : (-((2:ℕ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d62 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
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
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d20 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d22 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d23
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d24
    have d26 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d27 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d28 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d32 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d28 d30 d31 eq_int_to_real_coercion eq_identity_coercion
    have d33 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d34 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d27 d33 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_rat_to_real_coercion d34
    have d36 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d35 neg_rat_to_real_coercion
    have d37 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d38 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d39 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d39
    have d41 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d37 d38 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d40
    have d42 : x = x := by term_derivation_reflection
    have d43 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d44 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d41 d42 d43 eq_rat_to_real_coercion eq_identity_coercion
    have d45 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d46 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d44 d45
    have d47 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d48 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d46 d47 eq_identity_coercion eq_int_to_real_coercion d48
    have d50 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d49 neg_nat_to_real_coercion
    have d51 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d52 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d53 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d52
    have d54 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d50 d51 eq_identity_coercion eq_rat_to_real_coercion d53
    have d55 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d56 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d57 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d54 d55 eq_identity_coercion eq_int_to_real_coercion d56
    have d58 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d57 neg_nat_to_real_coercion
    have d59 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d36 d58
    have d60 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d59 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example68

namespace Example69
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) := by
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d20 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d22 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d23
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d24
    have d26 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d27 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d28 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d32 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d28 d30 d31 eq_int_to_real_coercion eq_identity_coercion
    have d33 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d34 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d27 d33 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_rat_to_real_coercion d34
    have d36 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d35 neg_rat_to_real_coercion
    have d37 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d38 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d39 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d39
    have d41 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d37 d38 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d40
    have d42 : x = x := by term_derivation_reflection
    have d43 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d44 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d41 d42 d43 eq_rat_to_real_coercion eq_identity_coercion
    have d45 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d46 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d44 d45
    have d47 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d48 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d46 d47 eq_identity_coercion eq_int_to_real_coercion d48
    have d50 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d49 neg_nat_to_real_coercion
    have d51 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d52 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d53 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d54 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d55 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d56 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d54 d55 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d57 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d58 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d52 d53 d56 d57 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d59 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d58
    have d60 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d50 d51 eq_identity_coercion eq_rat_to_real_coercion d59
    have d61 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d62 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d63 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d64 : x = x := by term_derivation_reflection
    have d65 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d66 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d67 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d63 d65 d66 eq_int_to_real_coercion eq_identity_coercion
    have d68 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d69 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d62 d68 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d70 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d60 d61 eq_identity_coercion eq_rat_to_real_coercion d69
    have d71 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d70 neg_rat_to_real_coercion
    have d72 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d36 d71
    have d73 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d72 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example69

namespace Example70
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d20 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d22 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d23
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d24
    have d26 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d27 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d28 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d32 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d28 d30 d31 eq_int_to_real_coercion eq_identity_coercion
    have d33 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d34 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d27 d33 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_rat_to_real_coercion d34
    have d36 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d35 neg_rat_to_real_coercion
    have d37 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d38 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d39 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d39
    have d41 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d37 d38 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d40
    have d42 : x = x := by term_derivation_reflection
    have d43 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d44 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d41 d42 d43 eq_rat_to_real_coercion eq_identity_coercion
    have d45 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d46 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d44 d45
    have d47 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d48 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d46 d47 eq_identity_coercion eq_int_to_real_coercion d48
    have d50 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d49 neg_nat_to_real_coercion
    have d51 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d52 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d53 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d52
    have d54 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d50 d51 eq_identity_coercion eq_rat_to_real_coercion d53
    have d55 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d56 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d57 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d54 d55 eq_identity_coercion eq_int_to_real_coercion d56
    have d58 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d57 neg_nat_to_real_coercion
    have d59 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d36 d58
    have d60 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d59 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example70

namespace Example71
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d20 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d21 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d22 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d23
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d24
    have d26 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d27 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d28 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d32 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d28 d30 d31 eq_int_to_real_coercion eq_identity_coercion
    have d33 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d34 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d27 d33 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d25 d26 eq_identity_coercion eq_rat_to_real_coercion d34
    have d36 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d35 neg_rat_to_real_coercion
    have d37 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d38 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d39 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d39
    have d41 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d37 d38 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d40
    have d42 : x = x := by term_derivation_reflection
    have d43 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d44 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d41 d42 d43 eq_rat_to_real_coercion eq_identity_coercion
    have d45 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d46 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d44 d45
    have d47 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d48 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d46 d47 eq_identity_coercion eq_int_to_real_coercion d48
    have d50 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d49 neg_nat_to_real_coercion
    have d51 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d52 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_simple_product_mul_literal comm_ring_mul_identity_coercion comm_ring_mul_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d53 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_literal d52
    have d54 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_div_eq d50 d51 eq_identity_coercion eq_rat_to_real_coercion d53
    have d55 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d56 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d57 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_add_eq d54 d55 eq_identity_coercion eq_int_to_real_coercion d56
    have d58 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d57 neg_nat_to_real_coercion
    have d59 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d36 d58
    have d60 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d59 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example71

namespace Example72
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d21 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d22
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d23 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d25 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d25
    have d27 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d28 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d32 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d33 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d28 d32 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d33
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d34 neg_rat_to_real_coercion
    have d36 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d37 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d38 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d38
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d36 d37 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d39
    have d41 : x = x := by term_derivation_reflection
    have d42 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d43 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d40 d41 d42 eq_rat_to_real_coercion eq_identity_coercion
    have d44 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d45 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d43 d44
    have d46 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d47 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d45 d46 eq_identity_coercion eq_int_to_real_coercion d47
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d48 neg_nat_to_real_coercion
    have d50 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d51 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d52 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d54 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d55 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d53 d54 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d56 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d57 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d56
    have d58 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d51 d52 d55 d57 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d59 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d58
    have d60 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d49 d50 eq_identity_coercion eq_rat_to_real_coercion d59
    have d61 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d62 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d63 : x = x := by term_derivation_reflection
    have d64 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d65 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d66 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d67 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d62 d66 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d68 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d60 d61 eq_identity_coercion eq_rat_to_real_coercion d67
    have d69 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d68 neg_rat_to_real_coercion
    have d70 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d35 d69
    have d71 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d70 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example72

namespace Example73
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d21 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d22
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d23 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d25 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d25
    have d27 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d28 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d32 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d33 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d28 d32 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d33
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d34 neg_rat_to_real_coercion
    have d36 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d37 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d38 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d38
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d36 d37 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d39
    have d41 : x = x := by term_derivation_reflection
    have d42 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d43 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d40 d41 d42 eq_rat_to_real_coercion eq_identity_coercion
    have d44 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d45 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d43 d44
    have d46 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d47 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d45 d46 eq_identity_coercion eq_int_to_real_coercion d47
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d48 neg_nat_to_real_coercion
    have d50 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d51 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d52 : (((-3:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d54 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d55 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d53 d54 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d56 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d57 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d56
    have d58 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d51 d52 d55 d57 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d59 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d58
    have d60 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d49 d50 eq_identity_coercion eq_rat_to_real_coercion d59
    have d61 : (-((3:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_neg_literal
    have d62 : ((3:ℕ) + (-3:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d63 : x = x := by term_derivation_reflection
    have d64 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d65 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d66 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d67 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d62 d66 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d68 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((3:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d60 d61 eq_identity_coercion eq_int_to_real_coercion d67
    have d69 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d68 neg_nat_to_real_coercion
    have d70 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d35 d69
    have d71 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d70 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example73

namespace Example74
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d21 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d22
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d23 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d25 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d25
    have d27 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d28 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d32 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d33 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d28 d32 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d33
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d34 neg_rat_to_real_coercion
    have d36 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d37 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d38 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d38
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d36 d37 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d39
    have d41 : x = x := by term_derivation_reflection
    have d42 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d43 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d40 d41 d42 eq_rat_to_real_coercion eq_identity_coercion
    have d44 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d45 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d43 d44
    have d46 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d47 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d45 d46 eq_identity_coercion eq_int_to_real_coercion d47
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d48 neg_nat_to_real_coercion
    have d50 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d51 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d52 : (((-3:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d54 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d55 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d53 d54 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d56 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d57 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d56
    have d58 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d51 d52 d55 d57 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d59 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d58
    have d60 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d49 d50 eq_identity_coercion eq_rat_to_real_coercion d59
    have d61 : (-((3:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_neg_literal
    have d62 : ((3:ℕ) + (-3:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d63 : x = x := by term_derivation_reflection
    have d64 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d65 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d66 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d67 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d62 d66 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d68 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((3:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d60 d61 eq_identity_coercion eq_int_to_real_coercion d67
    have d69 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d68 neg_nat_to_real_coercion
    have d70 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d35 d69
    have d71 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d70 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example74

namespace Example75
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d21 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d22
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d23 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d25 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d25
    have d27 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d28 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d32 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d33 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d28 d32 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d33
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d34 neg_rat_to_real_coercion
    have d36 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d37 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d38 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d38
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d36 d37 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d39
    have d41 : x = x := by term_derivation_reflection
    have d42 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d43 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d40 d41 d42 eq_rat_to_real_coercion eq_identity_coercion
    have d44 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d45 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d43 d44
    have d46 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d47 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d45 d46 eq_identity_coercion eq_int_to_real_coercion d47
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d48 neg_nat_to_real_coercion
    have d50 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d51 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d52 : (((-3:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d54 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d55 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d53 d54 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d56 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d57 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d56
    have d58 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d51 d52 d55 d57 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d59 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d58
    have d60 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d49 d50 eq_identity_coercion eq_rat_to_real_coercion d59
    have d61 : (-((3:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_neg_literal
    have d62 : ((3:ℕ) + (-3:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d63 : x = x := by term_derivation_reflection
    have d64 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d65 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d66 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d67 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d62 d66 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d68 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((3:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d60 d61 eq_identity_coercion eq_int_to_real_coercion d67
    have d69 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d68 neg_nat_to_real_coercion
    have d70 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d35 d69
    have d71 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d70 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example75

namespace Example76
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by
    have d : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) ↔ (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d13 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d14 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d12 eq_identity_coercion eq_int_to_real_coercion d13
    have d15 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d14 neg_nat_to_real_coercion
    have d16 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d17 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d18 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d19 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d20 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d21 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d19 d20 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d22 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d23 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d22
    have d24 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d17 d18 d21 d23 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d25 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d15 d16 eq_identity_coercion eq_rat_to_real_coercion d25
    have d27 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d28 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d29 : x = x := by term_derivation_reflection
    have d30 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d31 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d32 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d33 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d28 d32 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d34 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = x := by term_derivation_add_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d33
    have d35 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d34 neg_rat_to_real_coercion
    have d36 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d37 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d38 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d39 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d38
    have d40 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d36 d37 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d39
    have d41 : x = x := by term_derivation_reflection
    have d42 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d43 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d40 d41 d42 eq_rat_to_real_coercion eq_identity_coercion
    have d44 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d45 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d43 d44
    have d46 : (-((2:ℕ) : ℤ) : ℤ) = (-2:ℤ) := by term_derivation_neg_literal
    have d47 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((-2:ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_literal
    have d48 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((-((2:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d45 d46 eq_identity_coercion eq_int_to_real_coercion d47
    have d49 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) = ((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d48 neg_nat_to_real_coercion
    have d50 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d51 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d52 : (((-3:ℚ)/2:ℚ) * ((-2:ℤ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d53 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d54 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d55 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d53 d54 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d56 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d57 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d56
    have d58 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d51 d52 d55 d57 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d59 : (((-2:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d58
    have d60 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d49 d50 eq_identity_coercion eq_rat_to_real_coercion d59
    have d61 : (-((3:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_neg_literal
    have d62 : ((3:ℕ) + (-3:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d63 : x = x := by term_derivation_reflection
    have d64 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d65 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d66 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d67 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d62 d66 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d68 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((3:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = x := by term_derivation_add_eq d60 d61 eq_identity_coercion eq_int_to_real_coercion d67
    have d69 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) = x := by term_derivation_sub_eqs_add_neg d68 neg_nat_to_real_coercion
    have d70 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) - ((2:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d35 d69
    have d71 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d70 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example76

namespace Example77
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((0:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((0:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d19 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d20 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d19
    have d21 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d20 neg_nat_to_real_coercion
    have d22 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d23 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d24 : (((3:ℚ)/2:ℚ) * ((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d25 : (((3:ℚ)/2:ℚ) * ((0:ℕ) : ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d26 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d27 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d28 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d26 d27 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d29 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d30 : x = x := by term_derivation_reflection
    have d31 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d32 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d33 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d29 d31 d32 eq_int_to_real_coercion eq_identity_coercion
    have d34 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d35 : (((3:ℚ)/2:ℚ) * ((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d24 d25 d28 d34 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle nat_rat_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d36 : (((3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d37 : ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d40 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d23 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d21 d22 eq_identity_coercion eq_rat_to_real_coercion d41
    have d43 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d44 : ((((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d45 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_int_to_real_coercion d44
    have d46 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d45 neg_nat_to_real_coercion
    have d47 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d48 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d49 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d50 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d49
    have d51 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d47 d48 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d50
    have d52 : x = x := by term_derivation_reflection
    have d53 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d54 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d51 d52 d53 eq_rat_to_real_coercion eq_identity_coercion
    have d55 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d56 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d54 d55
    have d57 : y = y := by term_derivation_reflection
    have d58 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d59 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d58
    have d60 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d56 d57 eq_identity_coercion eq_identity_coercion d59
    have d61 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d62 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d63 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d60 d61 eq_identity_coercion eq_int_to_real_coercion d62
    have d64 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d63 neg_nat_to_real_coercion
    have d65 : ((1:ℚ)/3:ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d66 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((3:ℕ) : ℝ) : ℝ) = ((3:ℕ) * ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d67 : ((3:ℕ) * ((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d68 : ((3:ℕ) * (0:ℕ) : ℕ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d69 : ((3:ℕ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d70 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d71 : ((3:ℕ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d69 d70 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d72 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d73 : x = x := by term_derivation_reflection
    have d74 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d75 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d76 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d72 d74 d75 eq_int_to_real_coercion eq_identity_coercion
    have d77 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d78 : ((3:ℕ) * ((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d67 d68 d71 d77 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion nat_nat_real_coercion_triangle nat_real_real_coercion_triangle nat_nat_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d79 : ((3:ℕ) * (1:ℕ) : ℕ) = (3:ℕ) := by term_derivation_mul_one
    have d80 : ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d81 : ((3:ℕ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d79 d80 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d82 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d83 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((3:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d66 d78 d81 d82 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion nat_real_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d84 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d83
    have d85 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d64 d65 eq_identity_coercion eq_rat_to_real_coercion d84
    have d86 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d87 : ((((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d88 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d85 d86 eq_identity_coercion eq_int_to_real_coercion d87
    have d89 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d88 neg_nat_to_real_coercion
    have d90 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d46 d89
    have d91 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d90 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example77

namespace Example78
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : ((2:ℚ)/3:ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d32 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d34 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d36 : (((3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d37 : ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d40 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d41
    have d43 : (-(((-3:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d44 : (((-3:ℚ)/2:ℚ) + ((3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d45 d47 d48 eq_int_to_real_coercion eq_identity_coercion
    have d50 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d51 : ((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d44 d50 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d52 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d53 : (((((-3:ℚ)/2:ℚ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d51 d52 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((-3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_rat_to_real_coercion d53
    have d55 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d54 neg_rat_to_real_coercion
    have d56 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d57 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d58 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d58
    have d60 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d56 d57 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d59
    have d61 : x = x := by term_derivation_reflection
    have d62 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d63 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d60 d61 d62 eq_rat_to_real_coercion eq_identity_coercion
    have d64 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d65 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d63 d64
    have d66 : y = y := by term_derivation_reflection
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d68 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d67
    have d69 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d65 d66 eq_identity_coercion eq_identity_coercion d68
    have d70 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d71 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d72 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d69 d70 eq_identity_coercion eq_int_to_real_coercion d71
    have d73 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d72 neg_nat_to_real_coercion
    have d74 : ((1:ℚ)/3:ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d75 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((3:ℕ) : ℝ) : ℝ) = ((3:ℕ) * ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d76 : ((3:ℕ) * ((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d77 : ((3:ℕ) * (0:ℕ) : ℕ) = (0:ℕ) := by term_derivation_literal_mul_literal
    have d78 : ((3:ℕ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d79 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d80 : ((3:ℕ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d78 d79 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d81 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d82 : x = x := by term_derivation_reflection
    have d83 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d84 : ((-1:ℤ) * x : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d85 : ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d81 d83 d84 eq_int_to_real_coercion eq_identity_coercion
    have d86 : ((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d87 : ((3:ℕ) * ((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d76 d77 d80 d86 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion nat_nat_real_coercion_triangle nat_real_real_coercion_triangle nat_nat_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d88 : ((3:ℕ) * (1:ℕ) : ℕ) = (3:ℕ) := by term_derivation_mul_one
    have d89 : ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((3:ℕ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d88 d89 eq_nat_to_real_coercion comm_ring_mul_nat_to_real_coercion comm_ring_mul_identity_coercion
    have d91 : (((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d92 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((3:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d75 d87 d90 d91 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion nat_real_real_coercion_triangle nat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d93 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d92
    have d94 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d73 d74 eq_identity_coercion eq_rat_to_real_coercion d93
    have d95 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d96 : ((((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d97 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d94 d95 eq_identity_coercion eq_int_to_real_coercion d96
    have d98 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((3:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d97 neg_nat_to_real_coercion
    have d99 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / (((1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d55 d98
    have d100 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d99 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example78

namespace Example79
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) > ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d32 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul_power_one
    have d33 : (((1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((-1:ℚ)/2:ℚ) + y : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d34
    have d36 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d35 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d37 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d38 : (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d37 d38 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d40 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d41 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d36 d39 d40 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d42 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d41
    have d43 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_nat_to_real_coercion d42
    have d44 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d45 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d46 : y = y := by term_derivation_reflection
    have d47 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d48 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d49 : ((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_zero_add
    have d50 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = y := by term_derivation_sum_add_literal d45 d49 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d51 : (y + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d52 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d50 d51 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_rat_to_real_coercion d52
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_rat_to_real_coercion
    have d55 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d56 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d57 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d57
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d55 d56 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d58
    have d60 : x = x := by term_derivation_reflection
    have d61 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d62 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d59 d60 d61 eq_rat_to_real_coercion eq_identity_coercion
    have d63 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d64 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d62 d63
    have d65 : y = y := by term_derivation_reflection
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d66
    have d68 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d64 d65 eq_identity_coercion eq_identity_coercion d67
    have d69 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d70 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d71 : ((1:ℕ) * (((1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d72 : (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_div_literal d71
    have d73 : (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_div_eq d69 d70 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d72
    have d74 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d75 : (-(((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_eq d73 d74
    have d76 : ((-1:ℚ)/2:ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_reflection
    have d77 : ((0:ℕ) + ((-1:ℚ)/2:ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_zero_add
    have d78 : (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d79 : (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d77 d78 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion nat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d80 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d81 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d79 d80 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d82 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-(((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d68 d75 eq_identity_coercion eq_rat_to_real_coercion d81
    have d83 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d82 neg_rat_to_real_coercion
    have d84 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d85 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d86 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d85
    have d87 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d83 d84 eq_identity_coercion eq_nat_to_real_coercion d86
    have d88 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d89 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d90 : y = y := by term_derivation_reflection
    have d91 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d92 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d93 : ((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_zero_add
    have d94 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = y := by term_derivation_sum_add_literal d89 d93 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d95 : (y + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d96 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d94 d95 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d97 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d87 d88 eq_identity_coercion eq_rat_to_real_coercion d96
    have d98 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d97 neg_rat_to_real_coercion
    have d99 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d54 d98
    have d100 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d99 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example79

namespace Example80
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((0:ℕ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d32 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul_power_one
    have d33 : (((1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((-1:ℚ)/2:ℚ) + y : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d34
    have d36 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d35 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d37 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d38 : (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d37 d38 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d40 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d41 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d36 d39 d40 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d42 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d41
    have d43 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_nat_to_real_coercion d42
    have d44 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d45 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d46 : y = y := by term_derivation_reflection
    have d47 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d48 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d49 : ((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_zero_add
    have d50 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = y := by term_derivation_sum_add_literal d45 d49 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d51 : (y + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d52 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d50 d51 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_rat_to_real_coercion d52
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_rat_to_real_coercion
    have d55 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d56 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d57 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d57
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d55 d56 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d58
    have d60 : x = x := by term_derivation_reflection
    have d61 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d62 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d59 d60 d61 eq_rat_to_real_coercion eq_identity_coercion
    have d63 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d64 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d62 d63
    have d65 : y = y := by term_derivation_reflection
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d66
    have d68 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d64 d65 eq_identity_coercion eq_identity_coercion d67
    have d69 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d70 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d71 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d68 d69 eq_identity_coercion eq_int_to_real_coercion d70
    have d72 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d71 neg_nat_to_real_coercion
    have d73 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d74 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d75 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d74
    have d76 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d72 d73 eq_identity_coercion eq_nat_to_real_coercion d75
    have d77 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d78 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d79 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d76 d77 eq_identity_coercion eq_int_to_real_coercion d78
    have d80 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d79 neg_nat_to_real_coercion
    have d81 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d54 d80
    have d82 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d81 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example80

namespace Example81
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≥ ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≥
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize >
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d32 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul_power_one
    have d33 : (((1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((-1:ℚ)/2:ℚ) + y : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d34
    have d36 : (((1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d35 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d37 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d38 : (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : (((1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d37 d38 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d40 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d41 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d36 d39 d40 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d42 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d41
    have d43 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_nat_to_real_coercion d42
    have d44 : (-(((-1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d45 : (((-1:ℚ)/2:ℚ) + ((1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d46 : y = y := by term_derivation_reflection
    have d47 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d48 : ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) = y := by term_derivation_one_mul
    have d49 : ((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = y := by term_derivation_zero_add
    have d50 : ((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = y := by term_derivation_sum_add_literal d45 d49 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d51 : (y + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d52 : (((((-1:ℚ)/2:ℚ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d50 d51 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) + ((-(((-1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_rat_to_real_coercion d52
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_rat_to_real_coercion
    have d55 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d56 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d57 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d57
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d55 d56 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d58
    have d60 : x = x := by term_derivation_reflection
    have d61 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d62 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d59 d60 d61 eq_rat_to_real_coercion eq_identity_coercion
    have d63 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d64 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d62 d63
    have d65 : y = y := by term_derivation_reflection
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d66
    have d68 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d64 d65 eq_identity_coercion eq_identity_coercion d67
    have d69 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d70 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d71 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d68 d69 eq_identity_coercion eq_int_to_real_coercion d70
    have d72 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d71 neg_nat_to_real_coercion
    have d73 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d74 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_mul_one
    have d75 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d74
    have d76 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d72 d73 eq_identity_coercion eq_nat_to_real_coercion d75
    have d77 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d78 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_nf_add_zero
    have d79 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d76 d77 eq_identity_coercion eq_int_to_real_coercion d78
    have d80 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d79 neg_nat_to_real_coercion
    have d81 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((2:ℕ) : ℝ) : ℝ) - (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((0:ℕ) : ℝ) : ℝ) / ((1:ℕ) : ℝ) : ℝ) - ((0:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d54 d80
    have d82 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d81 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example81

namespace Example82
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d32 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d33 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d34
    have d36 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d35 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d37 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-3:ℤ) := by term_derivation_literal_mul_literal
    have d38 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d37 d38 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d40 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d41 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d36 d39 d40 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d42 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d41
    have d43 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d42
    have d44 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d45 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d49 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d50 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d45 d49 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d51 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d52 : (((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d50 d51 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_rat_to_real_coercion d52
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_rat_to_real_coercion
    have d55 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d56 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d57 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d57
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d55 d56 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d58
    have d60 : x = x := by term_derivation_reflection
    have d61 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d62 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d59 d60 d61 eq_rat_to_real_coercion eq_identity_coercion
    have d63 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d64 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d62 d63
    have d65 : y = y := by term_derivation_reflection
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d66
    have d68 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d64 d65 eq_identity_coercion eq_identity_coercion d67
    have d69 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d70 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d71 : ((1:ℕ) * (((1:ℚ)/2:ℚ)) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d72 : (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_div_literal d71
    have d73 : (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_div_eq d69 d70 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d72
    have d74 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d75 : (-(((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_eq d73 d74
    have d76 : ((-1:ℚ)/2:ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_reflection
    have d77 : ((0:ℕ) + ((-1:ℚ)/2:ℚ) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_zero_add
    have d78 : (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d79 : (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d77 d78 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion nat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d80 : ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d81 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d79 d80 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d82 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-(((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d68 d75 eq_identity_coercion eq_rat_to_real_coercion d81
    have d83 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) = ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d82 neg_rat_to_real_coercion
    have d84 : ((-1:ℚ)/3:ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d85 : (((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = ((-3:ℤ) * (((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d86 : ((-3:ℤ) * (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * ((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d87 : ((-3:ℤ) * (((-1:ℚ)/2:ℚ)) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d88 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d89 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d90 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d88 d89 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d91 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d92 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d91
    have d93 : ((-3:ℤ) * (((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d86 d87 d90 d92 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_rat_real_coercion_triangle int_real_real_coercion_triangle rat_rat_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d94 : ((-3:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_mul_one
    have d95 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d96 : ((-3:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d94 d95 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d97 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d98 : (((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d85 d93 d96 d97 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d99 : (((((-1:ℚ)/2:ℚ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d98
    have d100 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d83 d84 eq_identity_coercion eq_rat_to_real_coercion d99
    have d101 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d102 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d103 : x = x := by term_derivation_reflection
    have d104 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d105 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d106 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d107 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d102 d106 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d108 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d109 : (((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d107 d108 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d110 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d100 d101 eq_identity_coercion eq_rat_to_real_coercion d109
    have d111 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d110 neg_rat_to_real_coercion
    have d112 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d54 d111
    have d113 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℚ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d112 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example82

namespace Example83
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d32 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d33 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d34
    have d36 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d35 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d37 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-3:ℤ) := by term_derivation_literal_mul_literal
    have d38 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d37 d38 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d40 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d41 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d36 d39 d40 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d42 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d41
    have d43 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d42
    have d44 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d45 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d49 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d50 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d45 d49 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d51 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d52 : (((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d50 d51 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_rat_to_real_coercion d52
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_rat_to_real_coercion
    have d55 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d56 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d57 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d57
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d55 d56 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d58
    have d60 : x = x := by term_derivation_reflection
    have d61 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d62 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d59 d60 d61 eq_rat_to_real_coercion eq_identity_coercion
    have d63 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d64 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d62 d63
    have d65 : y = y := by term_derivation_reflection
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d66
    have d68 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d64 d65 eq_identity_coercion eq_identity_coercion d67
    have d69 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d70 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d71 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d72 : ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d73 : (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d71 d72 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d74 : (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d75 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d73 d74 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d76 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d68 d69 eq_identity_coercion eq_int_to_real_coercion d75
    have d77 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d76 neg_nat_to_real_coercion
    have d78 : ((-1:ℚ)/3:ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d79 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = ((-3:ℤ) * ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d80 : ((-3:ℤ) * ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d81 : ((-3:ℤ) * (-1:ℤ) : ℤ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d82 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d83 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d84 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d82 d83 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d85 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d86 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d85
    have d87 : ((-3:ℤ) * ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d80 d81 d84 d86 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d88 : ((-3:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_mul_one
    have d89 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((-3:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d88 d89 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d91 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d92 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d79 d87 d90 d91 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d93 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d92
    have d94 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d77 d78 eq_identity_coercion eq_rat_to_real_coercion d93
    have d95 : (-((3:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_neg_literal
    have d96 : ((3:ℕ) + (-3:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d97 : x = x := by term_derivation_reflection
    have d98 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d99 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d100 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d101 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d96 d100 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d102 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d103 : ((((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d101 d102 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d104 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((3:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d94 d95 eq_identity_coercion eq_int_to_real_coercion d103
    have d105 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d104 neg_nat_to_real_coercion
    have d106 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d54 d105
    have d107 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > > h1 d d1 d106 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example83

namespace Example84
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) < ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((-1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d32 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((-1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d34 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d36 : (((-1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d37 : (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((-1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d40 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d44 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d46 : y = y := by term_derivation_reflection
    have d47 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d48 : ((-1:ℤ) * y : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d45 d47 d48 eq_int_to_real_coercion eq_identity_coercion
    have d50 : ((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d51 : ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d44 d50 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d52 : (((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d53 : (((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d51 d52 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_rat_to_real_coercion d53
    have d55 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d54 neg_rat_to_real_coercion
    have d56 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d57 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d58 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d58
    have d60 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d56 d57 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d59
    have d61 : x = x := by term_derivation_reflection
    have d62 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d63 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d60 d61 d62 eq_rat_to_real_coercion eq_identity_coercion
    have d64 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d65 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d63 d64
    have d66 : y = y := by term_derivation_reflection
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d68 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d67
    have d69 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d65 d66 eq_identity_coercion eq_identity_coercion d68
    have d70 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d71 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d72 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d73 : ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d74 : (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d72 d73 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d75 : (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d76 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d74 d75 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d77 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d69 d70 eq_identity_coercion eq_int_to_real_coercion d76
    have d78 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d77 neg_nat_to_real_coercion
    have d79 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d80 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d81 : ((-1:ℤ) * ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d82 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d83 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d84 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d85 : ((-1:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d83 d84 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d86 : ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d87 : ((-1:ℤ) * ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d81 d82 d85 d86 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d88 : ((-1:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d89 : (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((-1:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d88 d89 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d91 : (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d92 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d80 d87 d90 d91 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d93 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d92
    have d94 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d78 d79 eq_identity_coercion eq_int_to_real_coercion d93
    have d95 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d96 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d97 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d98 : y = y := by term_derivation_reflection
    have d99 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d100 : ((-1:ℤ) * y : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d101 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d97 d99 d100 eq_int_to_real_coercion eq_identity_coercion
    have d102 : ((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d103 : (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d96 d102 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d104 : (((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d105 : ((((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d103 d104 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d106 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d94 d95 eq_identity_coercion eq_int_to_real_coercion d105
    have d107 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d106 neg_nat_to_real_coercion
    have d108 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d55 d107
    have d109 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish > ≥ h1 d d1 d108 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion gt_identity_coercion ge_identity_coercion
    assumption
  exact ()
end Example84

namespace Example85
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize <
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : (-2:ℤ) = (-2:ℤ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/2:ℚ) * (((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((1:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((-1:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-1:ℤ) := by term_derivation_literal_mul_literal
    have d32 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d33 : (((-1:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((-1:ℚ)/2:ℚ) * ((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d34 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d36 : (((-1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d37 : (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d38 : (((-1:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d36 d37 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d39 : ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d40 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d35 d38 d39 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d41 : ((((-1:ℤ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d40
    have d42 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) = ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_int_to_real_coercion d41
    have d43 : (-(((1:ℚ)/2:ℚ)) : ℚ) = ((-1:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d44 : (((1:ℚ)/2:ℚ) + ((-1:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d45 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d46 : y = y := by term_derivation_reflection
    have d47 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d48 : ((-1:ℤ) * y : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d49 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d45 d47 d48 eq_int_to_real_coercion eq_identity_coercion
    have d50 : ((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d51 : ((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d44 d50 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d52 : (((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d53 : (((((1:ℚ)/2:ℚ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d51 d52 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) + ((-(((1:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d42 d43 eq_identity_coercion eq_rat_to_real_coercion d53
    have d55 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d54 neg_rat_to_real_coercion
    have d56 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d57 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d58 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d58
    have d60 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d56 d57 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d59
    have d61 : x = x := by term_derivation_reflection
    have d62 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d63 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d60 d61 d62 eq_rat_to_real_coercion eq_identity_coercion
    have d64 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d65 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d63 d64
    have d66 : y = y := by term_derivation_reflection
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_greater comm_ring_add_identity_coercion
    have d68 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d67
    have d69 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d65 d66 eq_identity_coercion eq_identity_coercion d68
    have d70 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d71 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d72 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d73 : ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d74 : (((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d72 d73 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d75 : (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d76 : ((((0:ℕ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d74 d75 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d77 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d69 d70 eq_identity_coercion eq_int_to_real_coercion d76
    have d78 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d77 neg_nat_to_real_coercion
    have d79 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d80 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d81 : ((-1:ℤ) * ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d82 : ((-1:ℤ) * (-1:ℤ) : ℤ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d83 : ((-1:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_mul_one
    have d84 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d85 : ((-1:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d83 d84 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d86 : ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d87 : ((-1:ℤ) * ((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d81 d82 d85 d86 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d88 : ((-1:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d89 : (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((-1:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d88 d89 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d91 : (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d92 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d80 d87 d90 d91 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d93 : ((((-1:ℤ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d92
    have d94 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) = (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d78 d79 eq_identity_coercion eq_int_to_real_coercion d93
    have d95 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d96 : ((1:ℕ) + (-1:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d97 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d98 : y = y := by term_derivation_reflection
    have d99 : (y ^ (1:ℕ) : ℝ) = y := by term_derivation_power_one
    have d100 : ((-1:ℤ) * y : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d101 : ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d97 d99 d100 eq_int_to_real_coercion eq_identity_coercion
    have d102 : ((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_zero_add
    have d103 : (((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d96 d102 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d104 : (((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d105 : ((((1:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d103 d104 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d106 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d94 d95 eq_identity_coercion eq_int_to_real_coercion d105
    have d107 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((-1:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d106 neg_nat_to_real_coercion
    have d108 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-2:ℤ) : ℝ) : ℝ) - (((1:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / ((-1:ℤ) : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d55 d107
    have d109 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) < ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ > h1 d d1 d108 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion gt_identity_coercion
    assumption
  exact ()
end Example85

namespace Example86
def h (x y : ℝ) (h1 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) := by
    have d : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) ≤ ((1:ℕ) : ℝ) ↔ ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d1 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) ↔ ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound_derivation_normalize ≤
    have d2 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d3 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d4 : ((2:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d5 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_literal d4
    have d6 : (((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((2:ℚ)/3:ℚ) := by term_derivation_div_eq d2 d3 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d5
    have d7 : x = x := by term_derivation_reflection
    have d8 : (((2:ℚ)/3:ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d9 : ((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d6 d7 d8 eq_rat_to_real_coercion eq_identity_coercion
    have d10 : (-(((2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d11 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d9 d10
    have d12 : (2:ℕ) = (2:ℕ) := by term_derivation_reflection
    have d13 : y = y := by term_derivation_reflection
    have d14 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d15 : ((2:ℕ) * y : ℝ) = ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d12 d13 d14 eq_nat_to_real_coercion eq_identity_coercion
    have d16 : ((((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d17 : ((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) = (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d11 d15 eq_identity_coercion eq_identity_coercion d16
    have d18 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d19 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d20 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d21 : ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d22 : (((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d20 d21 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d23 : (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d24 : ((((0:ℕ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d22 d23 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d25 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d17 d18 eq_identity_coercion eq_int_to_real_coercion d24
    have d26 : (((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d25 neg_nat_to_real_coercion
    have d27 : ((-2:ℚ)/3:ℚ) = ((-2:ℚ)/3:ℚ) := by term_derivation_reflection
    have d28 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d29 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((-3:ℚ)/2:ℚ) * (((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d30 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) : ℚ) : ℚ) = ((3:ℚ)/2:ℚ) := by term_derivation_literal_mul_literal
    have d31 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d32 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d33 : (((-3:ℚ)/2:ℚ) * (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d31 d32 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d34 : (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d35 : (((3:ℚ)/2:ℚ) + x : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d34
    have d36 : (((-3:ℚ)/2:ℚ) * ((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = (((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d29 d30 d33 d35 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_rat_real_coercion_triangle rat_real_real_coercion_triangle int_rat_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d37 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) : ℚ) : ℚ) = (-3:ℤ) := by term_derivation_literal_mul_literal
    have d38 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d39 : (((-3:ℚ)/2:ℚ) * ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d37 d38 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d40 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d41 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d28 d36 d39 d40 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion rat_real_real_coercion_triangle rat_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d42 : ((((-1:ℤ) + (((-2:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((2:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d41
    have d43 : ((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) = ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d26 d27 eq_identity_coercion eq_rat_to_real_coercion d42
    have d44 : (-(((3:ℚ)/2:ℚ)) : ℚ) = ((-3:ℚ)/2:ℚ) := by term_derivation_neg_literal
    have d45 : (((3:ℚ)/2:ℚ) + ((-3:ℚ)/2:ℚ) : ℚ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d46 : x = x := by term_derivation_reflection
    have d47 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d48 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d49 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d50 : ((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d45 d49 comm_ring_add_identity_coercion rat_real_real_coercion_triangle real_real_real_coercion_triangle eq_rat_to_real_coercion comm_ring_add_rat_to_real_coercion rat_rat_real_coercion_triangle rat_rat_real_coercion_triangle
    have d51 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d52 : (((((3:ℚ)/2:ℚ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + (((-3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d50 d51 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle rat_real_real_coercion_triangle
    have d53 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-(((3:ℚ)/2:ℚ)) : ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d43 d44 eq_identity_coercion eq_rat_to_real_coercion d52
    have d54 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d53 neg_rat_to_real_coercion
    have d55 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d56 : (3:ℕ) = (3:ℕ) := by term_derivation_reflection
    have d57 : ((1:ℕ) * (((1:ℚ)/3:ℚ)) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_literal_mul_literal
    have d58 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_literal d57
    have d59 : (((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) = ((1:ℚ)/3:ℚ) := by term_derivation_div_eq d55 d56 eq_nat_to_rat_coercion eq_nat_to_rat_coercion d58
    have d60 : x = x := by term_derivation_reflection
    have d61 : (((1:ℚ)/3:ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d62 : ((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) = (((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_eq d59 d60 d61 eq_rat_to_real_coercion eq_identity_coercion
    have d63 : (-(((1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_product
    have d64 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) = (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_neg_eq d62 d63
    have d65 : y = y := by term_derivation_reflection
    have d66 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_product_add_product_less comm_ring_add_identity_coercion
    have d67 : ((((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d66
    have d68 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) = (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d64 d65 eq_identity_coercion eq_identity_coercion d67
    have d69 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d70 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d71 : ((0:ℕ) + (-1:ℤ) : ℤ) = (-1:ℤ) := by term_derivation_zero_add
    have d72 : ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d73 : (((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d71 d72 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d74 : (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d75 : ((((0:ℕ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-1:ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d73 d74 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d76 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d68 d69 eq_identity_coercion eq_int_to_real_coercion d75
    have d77 : (((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) = (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d76 neg_nat_to_real_coercion
    have d78 : ((-1:ℚ)/3:ℚ) = ((-1:ℚ)/3:ℚ) := by term_derivation_reflection
    have d79 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = ((-3:ℤ) * ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_base_mul_literal
    have d80 : ((-3:ℤ) * ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_non_one_literal_mul_atom
    have d81 : ((-3:ℤ) * (-1:ℤ) : ℤ) = (3:ℕ) := by term_derivation_literal_mul_literal
    have d82 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ)) : ℚ) = (1:ℕ) := by term_derivation_literal_mul_literal
    have d83 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul_power_one
    have d84 : ((-3:ℤ) * (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_mul_product d82 d83 eq_rat_to_real_coercion comm_ring_mul_rat_to_real_coercion comm_ring_mul_identity_coercion
    have d85 : ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d86 : ((3:ℕ) + x : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_atom d85
    have d87 : ((-3:ℤ) * ((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) : ℝ) = ((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d80 d81 d84 d86 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_int_real_coercion_triangle int_real_real_coercion_triangle int_int_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d88 : ((-3:ℤ) * ((1:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_mul_one
    have d89 : ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_reflection
    have d90 : ((-3:ℤ) * ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) := by term_derivation_mul_product d88 d89 eq_int_to_real_coercion comm_ring_mul_int_to_real_coercion comm_ring_mul_identity_coercion
    have d91 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_reflection
    have d92 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) * ((-3:ℤ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_literal_mul_sum d79 d87 d90 d91 real_pow_nat_to_real_pow_nat_coercion comm_ring_add_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion eq_identity_coercion comm_ring_mul_identity_coercion int_real_real_coercion_triangle int_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion
    have d93 : ((((-1:ℤ) + (((-1:ℚ)/3:ℚ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((1:ℕ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_literal d92
    have d94 : ((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) = (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_div_eq d77 d78 eq_identity_coercion eq_rat_to_real_coercion d93
    have d95 : (-((3:ℕ) : ℤ) : ℤ) = (-3:ℤ) := by term_derivation_neg_literal
    have d96 : ((3:ℕ) + (-3:ℤ) : ℤ) = (0:ℕ) := by term_derivation_literal_add_literal
    have d97 : x = x := by term_derivation_reflection
    have d98 : (x ^ (1:ℕ) : ℝ) = x := by term_derivation_power_one
    have d99 : ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) = x := by term_derivation_one_mul
    have d100 : ((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = x := by term_derivation_zero_add
    have d101 : (((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) : ℝ) : ℝ) = x := by term_derivation_sum_add_literal d96 d100 comm_ring_add_identity_coercion nat_real_real_coercion_triangle real_real_real_coercion_triangle eq_int_to_real_coercion comm_ring_add_int_to_real_coercion nat_int_real_coercion_triangle int_int_real_coercion_triangle
    have d102 : (x + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_atom_add_product
    have d103 : ((((3:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sum_add_literal d101 d102 comm_ring_add_identity_coercion real_real_real_coercion_triangle real_real_real_coercion_triangle eq_identity_coercion comm_ring_add_identity_coercion real_real_real_coercion_triangle int_real_real_coercion_triangle
    have d104 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) + ((-((3:ℕ) : ℤ) : ℤ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_add_eq d94 d95 eq_identity_coercion eq_int_to_real_coercion d103
    have d105 : (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) = (((0:ℕ) + ((1:ℕ) * (x ^ (1:ℕ) : ℝ) : ℝ) : ℝ) + ((-3:ℤ) * (y ^ (1:ℕ) : ℝ) : ℝ) : ℝ) := by term_derivation_sub_eqs_add_neg d104 neg_nat_to_real_coercion
    have d106 : (((((-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + ((2:ℕ) * y : ℝ) : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-2:ℚ)/3:ℚ) : ℝ) : ℝ) - (((3:ℚ)/2:ℚ) : ℝ) : ℝ) = (((((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) - ((1:ℕ) : ℝ) : ℝ) / (((-1:ℚ)/3:ℚ) : ℝ) : ℝ) - ((3:ℕ) : ℝ) : ℝ) := by term_derivation_non_trivial_expr_equivalence d54 d105
    have d107 : ((-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℚ) * x : ℝ) : ℝ) + y : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound_derivation_finish ≥ ≥ h1 d d1 d106 comm_ring_sub_identity_coercion comm_ring_sub_identity_coercion ge_identity_coercion ge_identity_coercion
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

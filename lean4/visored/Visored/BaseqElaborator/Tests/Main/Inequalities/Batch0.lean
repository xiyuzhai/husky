import Mathlib
import Visored.Tactics

namespace Example1
def h := by
  have h1 : (0:ℕ) = (0:ℕ) := by term_trivial
  exact ()
end Example1

namespace Example2
def h := by
  have h1 : (1:ℕ) + (1:ℕ) = (2:ℕ) := by term_trivial
  exact ()
end Example2

namespace Example3
def h := by
  have h1 : (1:ℕ) * (1:ℕ) = (1:ℕ) := by term_trivial
  exact ()
end Example3

namespace Example4
def h := by
  have h1 : (1:ℕ) * (1:ℕ) = (1:ℕ) := by term_trivial
  exact ()
end Example4

namespace Example5
def h := by
  have h1 : ((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) * ((2:ℕ) : ℚ) = ((1:ℕ) : ℚ) := by term_trivial
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
  have h1 : x - x = ((0:ℕ) : ℝ) := by term_trivial
  exact ()
end Example9

namespace Example10
def h (x : ℝ) := by
  have h1 : x + x = ((2:ℕ) : ℝ) * x := by term_trivial
  exact ()
end Example10

namespace Example11
def h (x : ℝ) := by
  have h1 : x ^ (2:ℕ) ≥ ((0:ℕ) : ℝ) := by apply sq_nonneg
  exact ()
end Example11

namespace Example12
def h (x : ℝ) (h1 : x ≥ ((1:ℕ) : ℝ)) := by
  have h2 : x - ((1:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by
    have d : x = x := by term_derivation_reflection
    have d1 : (1:ℕ) = (1:ℕ) := by term_derivation_reflection
    have d2 : x = x := by term_derivation_reflection
    have d3 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d4 : x + ((-1:ℤ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_atom_add_non_zero_literal
    have d5 : x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_add_eq d2 d3 eq_identity_coercion eq_int_to_real_coercion d4
    have d6 : x - ((1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_sub_eqs_add_neg d5 neg_nat_to_real_coercion
    have d7 : x ≥ ((1:ℕ) : ℝ) ↔ ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d8 : x = x := by term_derivation_reflection
    have d9 : (-((1:ℕ) : ℤ) : ℤ) = (-1:ℤ) := by term_derivation_neg_literal
    have d10 : x + ((-1:ℤ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_atom_add_non_zero_literal
    have d11 : x + ((-((1:ℕ) : ℤ) : ℤ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_add_eq d8 d9 eq_identity_coercion eq_int_to_real_coercion d10
    have d12 : x - ((1:ℕ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_sub_eqs_add_neg d11 neg_nat_to_real_coercion
    have d13 : (0:ℕ) = (0:ℕ) := by term_derivation_reflection
    have d14 : (-1:ℤ) = (-1:ℤ) := by term_derivation_reflection
    have d15 : x = x := by term_derivation_reflection
    have d16 : x ^ (1:ℕ) = x := by term_derivation_power_one
    have d17 : ((1:ℕ) : ℝ) * x ^ (1:ℕ) = x := by term_derivation_one_mul
    have d18 : ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_reflection
    have d19 : ((-1:ℤ) : ℝ) + x = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_add_atom d18
    have d20 : ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_add_eq d14 d17 eq_int_to_real_coercion eq_identity_coercion d19
    have d21 : (-((0:ℕ) : ℤ) : ℤ) = (0:ℕ) := by term_derivation_neg_literal
    have d22 : ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) + ((0:ℕ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_nf_add_zero
    have d23 : ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) + ((-((0:ℕ) : ℤ) : ℤ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_add_eq d20 d21 eq_identity_coercion eq_nat_to_real_coercion d22
    have d24 : ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) - ((0:ℕ) : ℝ) = ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) := by term_derivation_sub_eqs_add_neg d23 neg_nat_to_real_coercion
    have d25 : x - ((1:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) ↔ ((-1:ℤ) : ℝ) + ((1:ℕ) : ℝ) * x ^ (1:ℕ) ≥ ((0:ℕ) : ℝ) := by term_derivation_num_comparison
    have d26 : x - ((1:ℕ) : ℝ) ≥ ((0:ℕ) : ℝ) := by term_derivation_non_trivial_finish
    assumption
  exact ()
end Example12

namespace Example13
def h (x : ℝ) := by
  have h1 : ((2:ℕ) : ℝ) * (((1:ℕ) : ℝ) + x) = ((2:ℕ) : ℝ) + ((2:ℕ) : ℝ) * x := by term_trivial
  exact ()
end Example13

namespace Example14
def h (x : ℝ) := by
  have h1 : (((1:ℕ) : ℝ) + x) * x = x + x ^ (2:ℕ) := by comm_ring
  exact ()
end Example14

namespace Example15
def h (x : ℝ) := by
  have h1 : (((1:ℕ) : ℝ) + x) * (((1:ℕ) : ℝ) + x) = ((1:ℕ) : ℝ) + ((2:ℕ) : ℝ) * x + x ^ (2:ℕ) := by comm_ring
  exact ()
end Example15

namespace Example16
def h (x y : ℝ) := by
  have h1 : (((1:ℕ) : ℝ) + x) * (((1:ℕ) : ℝ) + y) = ((1:ℕ) : ℝ) + x + y + x * y := by comm_ring
  exact ()
end Example16

namespace Example17
def h (x y : ℝ) := by
  have h1 : (x + y) ^ (2:ℕ) = x ^ (2:ℕ) + ((2:ℕ) : ℝ) * x * y + y ^ (2:ℕ) := by comm_ring
  exact ()
end Example17

namespace Example18
def h (x y : ℝ) := by
  have h1 : (x + y) ^ (3:ℕ) = x ^ (3:ℕ) + ((3:ℕ) : ℝ) * x ^ (2:ℕ) * y + ((3:ℕ) : ℝ) * x * y ^ (2:ℕ) + y ^ (3:ℕ) := by comm_ring
  exact ()
end Example18

namespace Example19
def h (x y : ℝ) := by
  have h1 : (x + y) ^ (4:ℕ) = x ^ (4:ℕ) + ((4:ℕ) : ℝ) * x ^ (3:ℕ) * y + ((6:ℕ) : ℝ) * x ^ (2:ℕ) * y ^ (2:ℕ) + ((4:ℕ) : ℝ) * x * y ^ (3:ℕ) + y ^ (4:ℕ) := by comm_ring
  exact ()
end Example19

namespace Example20
def h (x y : ℝ) := by
  have h1 : (x + y) ^ (5:ℕ) = x ^ (5:ℕ) + ((5:ℕ) : ℝ) * x ^ (4:ℕ) * y + ((10:ℕ) : ℝ) * x ^ (3:ℕ) * y ^ (2:ℕ) + ((10:ℕ) : ℝ) * x ^ (2:ℕ) * y ^ (3:ℕ) + ((5:ℕ) : ℝ) * x * y ^ (4:ℕ) + y ^ (5:ℕ) := by comm_ring
  exact ()
end Example20

namespace Example21
def h (x y : ℝ) := by
  have h1 : (x + y) ^ (6:ℕ) = x ^ (6:ℕ) + ((6:ℕ) : ℝ) * x ^ (5:ℕ) * y + ((15:ℕ) : ℝ) * x ^ (4:ℕ) * y ^ (2:ℕ) + ((20:ℕ) : ℝ) * x ^ (3:ℕ) * y ^ (3:ℕ) + ((15:ℕ) : ℝ) * x ^ (2:ℕ) * y ^ (4:ℕ) + ((6:ℕ) : ℝ) * x * y ^ (5:ℕ) + y ^ (6:ℕ) := by comm_ring
  exact ()
end Example21

namespace Example22
def h (x y : ℝ) := by
  have h1 : (x + y) ^ (7:ℕ) = x ^ (7:ℕ) + ((7:ℕ) : ℝ) * x ^ (6:ℕ) * y + ((21:ℕ) : ℝ) * x ^ (5:ℕ) * y ^ (2:ℕ) + ((35:ℕ) : ℝ) * x ^ (4:ℕ) * y ^ (3:ℕ) + ((35:ℕ) : ℝ) * x ^ (3:ℕ) * y ^ (4:ℕ) + ((21:ℕ) : ℝ) * x ^ (2:ℕ) * y ^ (5:ℕ) + ((7:ℕ) : ℝ) * x * y ^ (6:ℕ) + y ^ (7:ℕ) := by comm_ring
  exact ()
end Example22

namespace Example23
def h (x y : ℝ) := by
  have h1 : (x + y) ^ (8:ℕ) = x ^ (8:ℕ) + ((8:ℕ) : ℝ) * x ^ (7:ℕ) * y + ((28:ℕ) : ℝ) * x ^ (6:ℕ) * y ^ (2:ℕ) + ((56:ℕ) : ℝ) * x ^ (5:ℕ) * y ^ (3:ℕ) + ((70:ℕ) : ℝ) * x ^ (4:ℕ) * y ^ (4:ℕ) + ((56:ℕ) : ℝ) * x ^ (3:ℕ) * y ^ (5:ℕ) + ((28:ℕ) : ℝ) * x ^ (2:ℕ) * y ^ (6:ℕ) + ((8:ℕ) : ℝ) * x * y ^ (7:ℕ) + y ^ (8:ℕ) := by comm_ring
  exact ()
end Example23

namespace Example24
def h (x y : ℝ) := by
  have h1 : (x + y) ^ (9:ℕ) = x ^ (9:ℕ) + ((9:ℕ) : ℝ) * x ^ (8:ℕ) * y + ((36:ℕ) : ℝ) * x ^ (7:ℕ) * y ^ (2:ℕ) + ((84:ℕ) : ℝ) * x ^ (6:ℕ) * y ^ (3:ℕ) + ((126:ℕ) : ℝ) * x ^ (5:ℕ) * y ^ (4:ℕ) + ((126:ℕ) : ℝ) * x ^ (4:ℕ) * y ^ (5:ℕ) + ((84:ℕ) : ℝ) * x ^ (3:ℕ) * y ^ (6:ℕ) + ((36:ℕ) : ℝ) * x ^ (2:ℕ) * y ^ (7:ℕ) + ((9:ℕ) : ℝ) * x * y ^ (8:ℕ) + y ^ (9:ℕ) := by comm_ring
  exact ()
end Example24

namespace Example25
def h (x : ℝ) := by
  have h1 : (x ^ (2:ℕ) + ((1:ℕ) : ℝ)) ^ (2:ℕ) = x ^ (4:ℕ) + ((2:ℕ) : ℝ) * x ^ (2:ℕ) + ((1:ℕ) : ℝ) := by comm_ring
  exact ()
end Example25

namespace Example26
def h (x y : ℝ) := by
  have h1 : (x ^ (2:ℕ) + y ^ (2:ℕ)) ^ (2:ℕ) = x ^ (4:ℕ) + ((2:ℕ) : ℝ) * x ^ (2:ℕ) * y ^ (2:ℕ) + y ^ (4:ℕ) := by comm_ring
  exact ()
end Example26

namespace Example27
def h (x : ℝ) (n : ℕ) := by
  have h1 : (x ^ n + ((1:ℕ) : ℝ)) ^ (2:ℕ) = x ^ ((2:ℕ) * n) + ((2:ℕ) : ℝ) * x ^ n + ((1:ℕ) : ℝ) := by comm_ring
  exact ()
end Example27

namespace Example28
def h (x y : ℝ) (n : ℕ) := by
  have h1 : (x ^ n + y ^ n) ^ (2:ℕ) = x ^ ((2:ℕ) * n) + ((2:ℕ) : ℝ) * x ^ n * y ^ n + y ^ ((2:ℕ) * n) := by comm_ring
  exact ()
end Example28

namespace Example29
def h (x : ℝ) (n : ℕ) := by
  have h1 : (x ^ n ^ (2:ℕ) + ((1:ℕ) : ℝ)) ^ (2:ℕ) = x ^ ((2:ℕ) * n ^ (2:ℕ)) + ((2:ℕ) : ℝ) * x ^ n ^ (2:ℕ) + ((1:ℕ) : ℝ) := by comm_ring
  exact ()
end Example29

namespace Example30
def h (x : ℝ) (n : ℕ) := by
  have h1 : (x ^ ((2:ℕ) * n) + ((1:ℕ) : ℝ)) ^ (2:ℕ) = x ^ ((4:ℕ) * n) + ((2:ℕ) : ℝ) * x ^ ((2:ℕ) * n) + ((1:ℕ) : ℝ) := by comm_ring
  exact ()
end Example30

namespace Example31
def h := by
  have h1 : (1000340282366920938463463374607431768211456:ℕ) = (1000340282366920938463463374607431768211456:ℕ) := by term_trivial
  exact ()
end Example31

namespace Example32
def h (x y : ℝ) := by
  have h1 : x + y = y + x := by term_trivial
  exact ()
end Example32

namespace Example33
def h (x : ℝ) (h1 : x = ((1:ℕ) : ℝ)) := by
  have h2 : x = ((1:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example33

namespace Example34
def h := by
  let x := (1:ℕ)
  have h1 : x = (1:ℕ) := by let_assigned
  have h2 : x = (1:ℕ) := by old_main_hypothesis
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
  have h4 : x + y = z := by litnum_reduce
  exact ()
end Example36

namespace Example37
def h (x : ℝ) (h1 : x > ((0:ℕ) : ℝ)) := by
  have h2 : x > ((0:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example37

namespace Example38
def h (x : ℝ) (h1 : x > ((1:ℕ) : ℝ)) := by
  have h2 : x > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example38

namespace Example39
def h (x : ℝ) (h1 : x > ((1:ℕ) : ℝ)) := by
  have h2 : x ≥ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example39

namespace Example40
def h (x : ℝ) (h1 : x ≥ ((1:ℕ) : ℝ)) := by
  have h2 : x ≥ ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example40

namespace Example41
def h (x : ℝ) (h1 : x ≥ ((1:ℕ) : ℝ)) := by
  have h2 : x > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example41

namespace Example42
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example42

namespace Example43
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x < ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example43

namespace Example44
def h (x : ℝ) (h1 : x < ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example44

namespace Example45
def h (x : ℝ) (h1 : x ≤ ((1:ℕ) : ℝ)) := by
  have h2 : x < ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example45

namespace Example46
def h (x : ℝ) (h1 : x ≤ ((1:ℕ) : ℝ)) := by
  have h2 : x ≤ ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example46

namespace Example47
def h (x : ℝ) (h1 : (- x : ℝ) > ((0:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) > ((0:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example47

namespace Example48
def h (x : ℝ) (h1 : (- x : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example48

namespace Example49
def h (x : ℝ) (h1 : (- x : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example49

namespace Example50
def h (x : ℝ) (h1 : (- x : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example50

namespace Example51
def h (x : ℝ) (h1 : (- x : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example51

namespace Example52
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example52

namespace Example53
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example53

namespace Example54
def h (x : ℝ) (h1 : (- x : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example54

namespace Example55
def h (x : ℝ) (h1 : (- x : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example55

namespace Example56
def h (x : ℝ) (h1 : (- x : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (- x : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example56

namespace Example57
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) > ((0:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) > ((0:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example57

namespace Example58
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example58

namespace Example59
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example59

namespace Example60
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example60

namespace Example61
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example61

namespace Example62
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example62

namespace Example63
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example63

namespace Example64
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example64

namespace Example65
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example65

namespace Example66
def h (x : ℝ) (h1 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-(((2:ℕ) : ℝ) * x) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example66

namespace Example67
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) > ((0:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) > ((0:ℕ) : ℝ) := by old_main_hypothesis
  exact ()
end Example67

namespace Example68
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example68

namespace Example69
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) > ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≥ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example69

namespace Example70
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≥ ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example70

namespace Example71
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example71

namespace Example72
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≤ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example72

namespace Example73
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example73

namespace Example74
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example74

namespace Example75
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) < ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example75

namespace Example76
def h (x : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) ≤ ((2:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example76

namespace Example77
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y > ((0:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example77

namespace Example78
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y > ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example78

namespace Example79
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y > ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y ≥ (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℝ) := by litnum_bound
  exact ()
end Example79

namespace Example80
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y ≥ ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example80

namespace Example81
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y ≥ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y > ((0:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example81

namespace Example82
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y ≤ (((1:ℕ) : ℚ) / ((2:ℕ) : ℚ) : ℝ) := by litnum_bound
  exact ()
end Example82

namespace Example83
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y < ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example83

namespace Example84
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y < ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y ≤ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example84

namespace Example85
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y < ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example85

namespace Example86
def h (x y : ℝ) (h1 : (-((((2:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + ((2:ℕ) : ℝ) * y ≤ ((1:ℕ) : ℝ)) := by
  have h2 : (-((((1:ℕ) : ℚ) / ((3:ℕ) : ℚ) : ℝ) * x) : ℝ) + y ≤ ((1:ℕ) : ℝ) := by litnum_bound
  exact ()
end Example86

namespace Example87
def h := by
  have h1 : (0:ℕ) < (2:ℕ) := by calc
    (0:ℕ) < (1:ℕ) := by obvious
    _ < (2:ℕ) := by obvious
  exact ()
end Example87

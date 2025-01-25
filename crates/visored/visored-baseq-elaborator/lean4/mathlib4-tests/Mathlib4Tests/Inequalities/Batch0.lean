import Mathlib

macro "term_trivial": tactic =>`(tactic|
  first
  | simp; done
  | ring; done
  | ring_nf; done
  | linarith; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "old_main_hypothesis": tactic =>`(tactic|
  first
  | assumption; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "let_assigned": tactic =>`(tactic|
  first
  | dsimp; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_equivalence": tactic =>`(tactic|
  first
  | simp; done
  | ring; done
  | ring_nf; done
  | linarith; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "comm_ring": tactic =>`(tactic|
  first
  | ring; done
  | ring_nf; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "litnum_reduce": tactic =>`(tactic|
  first
  | simp; done
  | simp [*]; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "litnum_bound": tactic =>`(tactic|
  first
  | linarith; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)


-- Reflection
theorem term_derivation_reflection {α} {a : α} : a = a := by rfl

-- NumComparison
theorem term_derivation_num_comparison : true := by sorry

-- SubEqsAddNeg
theorem term_derivation_sub_eqs_add_neg : true := by sorry

-- LiteralAddLiteral
theorem term_derivation_literal_add_literal : true := by sorry

-- AddEq
theorem term_derivation_add_eq : true := by sorry

-- AdditionInterchange
theorem term_derivation_addition_interchange : true := by sorry

-- AdditionAssociativity
theorem term_derivation_addition_associativity : true := by sorry

-- AdditionIdentity
theorem term_derivation_addition_identity : true := by sorry

-- AdditionInverse
theorem term_derivation_addition_inverse : true := by sorry

-- AdditionDistributivity
theorem term_derivation_addition_distributivity : true := by sorry

-- NegLiteral
theorem term_derivation_neg_literal { α } { a : α } [Neg α] : -a = -a := by rfl

-- NegEq
theorem term_derivation_neg_eq : true := by sorry

-- NegAtom
theorem term_derivation_neg_atom : true := by sorry

-- NegSum
theorem term_derivation_neg_sum : true := by sorry

-- NegProduct
theorem term_derivation_neg_product : true := by sorry

-- NegExponential
theorem term_derivation_neg_exponential : true := by sorry

-- AtomAddNonZeroLiteral
theorem term_derivation_atom_add_non_zero_literal { α } { a : α } { c : α } [CommRing α] : a + c = c + 1 * a := by ring

-- LiteralMul
theorem term_derivation_literal_mul : true := by sorry

-- MulEq
theorem term_derivation_mul_eq : true := by sorry

-- AtomMulSwap
theorem term_derivation_atom_mul_swap : true := by sorry

-- OneMul
theorem term_derivation_one_mul : true := by sorry

-- NonOneLiteralMulAtom
theorem term_derivation_nonone_literal_mul_atom : true := by sorry

-- NfAddZero
theorem term_derivation_nf_add_zero : true := by sorry

-- NonTrivialFinish
theorem term_derivation_non_trivial_finish : true := by sorry

-- AtomMulAtomLess
theorem term_derivation_atom_mul_atom_less : true := by sorry

-- AtomMulAtomEqual
theorem term_derivation_atom_mul_atom_equal : true := by sorry

-- AtomMulAtomGreater
theorem term_derivation_atom_mul_atom_greater : true := by sorry

-- Sqrt
theorem term_derivation_sqrt : true := by sorry

-- AddAtom
theorem term_derivation_add_atom : true := by sorry

-- MulProduct
theorem term_derivation_mul_product : true := by sorry

-- NonReducedPower
theorem term_derivation_non_reduced_power : true := by sorry

-- PowerOne
theorem term_derivation_power_one : true := by sorry

-- AtomAddProduct
theorem term_derivation_atom_add_product : true := by sorry

-- ZeroAdd
theorem term_derivation_zero_add : true := by sorry

-- SumAddProductEqualKeep
theorem term_derivation_sum_add_product_equal_keep : true := by sorry

-- SumAddProductEqualCancel
theorem term_derivation_sum_add_product_equal_cancel : true := by sorry

-- SumAddProductGreater
theorem term_derivation_sum_add_product_greater : true := by sorry

-- ProductAddProductLess
theorem term_derivation_product_add_product_less : true := by sorry

-- ProductAddProductEqualKeep
theorem term_derivation_product_add_product_equal_keep : true := by sorry

-- ProductAddProductEqualCancel
theorem term_derivation_product_add_product_equal_cancel : true := by sorry

-- ProductAddProductGreater
theorem term_derivation_product_add_product_greater : true := by sorry

-- SimpleProductMulExponentialLess
theorem term_derivation_simple_product_mul_exponential_less : true := by sorry

-- SimpleProductMulExponentialGreater
theorem term_derivation_simple_product_mul_exponential_greater : true := by sorry

-- SimpleProductMulBaseLess
theorem term_derivation_simple_product_mul_base_less : true := by sorry

-- SimpleProductMulBaseGreater
theorem term_derivation_simple_product_mul_base_greater : true := by sorry

-- AddSum
theorem term_derivation_add_sum : true := by sorry

-- DivEq
theorem term_derivation_div_eq : true := by sorry

-- DivLiteral
theorem term_derivation_div_literal : true := by sorry

-- LiteralMulSum
theorem term_derivation_literal_mul_sum : true := by sorry

-- SumAddLiteral
theorem term_derivation_sum_add_literal : true := by sorry

-- ProductAddLiteral
theorem term_derivation_product_add_literal : true := by sorry

-- DivAtom
theorem term_derivation_div_atom : true := by sorry

-- AtomMulExponentialLess
theorem term_derivation_atom_mul_exponential_less : true := by sorry

-- AtomMulExponentialGreater
theorem term_derivation_atom_mul_exponential_greater : true := by sorry



namespace Example1
def h := by
  have h1 : 0 = 0 := by term_trivial
  exact ()
end Example1

namespace Example2
def h := by
  have h1 : 1 + 1 = 2 := by term_trivial
  exact ()
end Example2

namespace Example3
def h := by
  have h1 : 1 * 1 = 1 := by term_trivial
  exact ()
end Example3

namespace Example4
def h := by
  have h1 : 1 * 1 = 1 := by term_trivial
  exact ()
end Example4

namespace Example5
def h := by
  have h1 : (1 : ℚ) / (2 : ℚ) * (2 : ℚ) = (1 : ℚ) := by term_trivial
  exact ()
end Example5

namespace Example6
def h := by
  have h1 : 0 < 1 := by term_trivial
  exact ()
end Example6

namespace Example7
def h := by
  have h1 : 0 ≠ 1 := by term_trivial
  exact ()
end Example7

namespace Example8
def h (x : ℝ) := by
  have h1 : x = x := by term_trivial
  exact ()
end Example8

namespace Example9
def h (x : ℝ) := by
  have h1 : x - x = (0 : ℝ) := by term_trivial
  exact ()
end Example9

namespace Example10
def h (x : ℝ) := by
  have h1 : x + x = (2 : ℝ) * x := by term_trivial
  exact ()
end Example10

namespace Example11
def h (x : ℝ) := by
  have h1 : x ^ 2 ≥ (0 : ℝ) := by apply sq_nonneg
  exact ()
end Example11

namespace Example12
def h (x : ℝ) (h1 : x ≥ (1 : ℝ)) := by
  have h2 : x - (1 : ℝ) ≥ (0 : ℝ) := by
    have d : x = x := term_derivation_reflection
    have d1 : 1 = 1 := term_derivation_reflection
    have d2 : x = x := term_derivation_reflection
    have d3 : -(1 : ℤ) = -1 := term_derivation_neg_literal
    have d4 : x + (-1 : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_atom_add_non_zero_literal
    have d5 : x + (-(1 : ℤ) : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_add_eq
    have d6 : x - (1 : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_literal_add_literal
    have d7 : x ≥ (1 : ℝ) ↔ (-1 : ℝ) + (1 : ℝ) * x ^ 1 ≥ (0 : ℝ) := term_derivation_num_comparison
    have d8 : x = x := term_derivation_reflection
    have d9 : -(1 : ℤ) = -1 := term_derivation_neg_literal
    have d10 : x + (-1 : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_atom_add_non_zero_literal
    have d11 : x + (-(1 : ℤ) : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_add_eq
    have d12 : x - (1 : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_literal_add_literal
    have d13 : 0 = 0 := term_derivation_reflection
    have d14 : -1 = -1 := term_derivation_reflection
    have d15 : x = x := term_derivation_reflection
    have d16 : x ^ 1 = x := term_derivation_power_one
    have d17 : (1 : ℝ) * x ^ 1 = x := term_derivation_one_mul
    have d18 : (-1 : ℝ) + (1 : ℝ) * x ^ 1 = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_reflection
    have d19 : (-1 : ℝ) + x = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_add_atom
    have d20 : (-1 : ℝ) + (1 : ℝ) * x ^ 1 = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_add_eq
    have d21 : -(0 : ℤ) = 0 := term_derivation_neg_literal
    have d22 : (-1 : ℝ) + (1 : ℝ) * x ^ 1 + (0 : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_nf_add_zero
    have d23 : (-1 : ℝ) + (1 : ℝ) * x ^ 1 + (-(0 : ℤ) : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_add_eq
    have d24 : (-1 : ℝ) + (1 : ℝ) * x ^ 1 - (0 : ℝ) = (-1 : ℝ) + (1 : ℝ) * x ^ 1 := term_derivation_literal_add_literal
    have d25 : x - (1 : ℝ) ≥ (0 : ℝ) ↔ (-1 : ℝ) + (1 : ℝ) * x ^ 1 ≥ (0 : ℝ) := term_derivation_num_comparison
    have d26 : x - (1 : ℝ) ≥ (0 : ℝ) := term_derivation_non_trivial_finish
    assumption
  exact ()
end Example12

namespace Example13
def h (x : ℝ) := by
  have h1 : (2 : ℝ) * ((1 : ℝ) + x) = (2 : ℝ) + (2 : ℝ) * x := by term_trivial
  exact ()
end Example13

namespace Example14
def h (x : ℝ) := by
  have h1 : ((1 : ℝ) + x) * x = x + x ^ 2 := by comm_ring
  exact ()
end Example14

namespace Example15
def h (x : ℝ) := by
  have h1 : ((1 : ℝ) + x) * ((1 : ℝ) + x) = (1 : ℝ) + (2 : ℝ) * x + x ^ 2 := by comm_ring
  exact ()
end Example15

namespace Example16
def h (x y : ℝ) := by
  have h1 : ((1 : ℝ) + x) * ((1 : ℝ) + y) = (1 : ℝ) + x + y + x * y := by comm_ring
  exact ()
end Example16

namespace Example17
def h (x y : ℝ) := by
  have h1 : (x + y) ^ 2 = x ^ 2 + (2 : ℝ) * x * y + y ^ 2 := by comm_ring
  exact ()
end Example17

namespace Example18
def h (x y : ℝ) := by
  have h1 : (x + y) ^ 3 = x ^ 3 + (3 : ℝ) * x ^ 2 * y + (3 : ℝ) * x * y ^ 2 + y ^ 3 := by comm_ring
  exact ()
end Example18

namespace Example19
def h (x y : ℝ) := by
  have h1 : (x + y) ^ 4 = x ^ 4 + (4 : ℝ) * x ^ 3 * y + (6 : ℝ) * x ^ 2 * y ^ 2 + (4 : ℝ) * x * y ^ 3 + y ^ 4 := by comm_ring
  exact ()
end Example19

namespace Example20
def h (x y : ℝ) := by
  have h1 : (x + y) ^ 5 = x ^ 5 + (5 : ℝ) * x ^ 4 * y + (10 : ℝ) * x ^ 3 * y ^ 2 + (10 : ℝ) * x ^ 2 * y ^ 3 + (5 : ℝ) * x * y ^ 4 + y ^ 5 := by comm_ring
  exact ()
end Example20

namespace Example21
def h (x y : ℝ) := by
  have h1 : (x + y) ^ 6 = x ^ 6 + (6 : ℝ) * x ^ 5 * y + (15 : ℝ) * x ^ 4 * y ^ 2 + (20 : ℝ) * x ^ 3 * y ^ 3 + (15 : ℝ) * x ^ 2 * y ^ 4 + (6 : ℝ) * x * y ^ 5 + y ^ 6 := by comm_ring
  exact ()
end Example21

namespace Example22
def h (x y : ℝ) := by
  have h1 : (x + y) ^ 7 = x ^ 7 + (7 : ℝ) * x ^ 6 * y + (21 : ℝ) * x ^ 5 * y ^ 2 + (35 : ℝ) * x ^ 4 * y ^ 3 + (35 : ℝ) * x ^ 3 * y ^ 4 + (21 : ℝ) * x ^ 2 * y ^ 5 + (7 : ℝ) * x * y ^ 6 + y ^ 7 := by comm_ring
  exact ()
end Example22

namespace Example23
def h (x y : ℝ) := by
  have h1 : (x + y) ^ 8 = x ^ 8 + (8 : ℝ) * x ^ 7 * y + (28 : ℝ) * x ^ 6 * y ^ 2 + (56 : ℝ) * x ^ 5 * y ^ 3 + (70 : ℝ) * x ^ 4 * y ^ 4 + (56 : ℝ) * x ^ 3 * y ^ 5 + (28 : ℝ) * x ^ 2 * y ^ 6 + (8 : ℝ) * x * y ^ 7 + y ^ 8 := by comm_ring
  exact ()
end Example23

namespace Example24
def h (x y : ℝ) := by
  have h1 : (x + y) ^ 9 = x ^ 9 + (9 : ℝ) * x ^ 8 * y + (36 : ℝ) * x ^ 7 * y ^ 2 + (84 : ℝ) * x ^ 6 * y ^ 3 + (126 : ℝ) * x ^ 5 * y ^ 4 + (126 : ℝ) * x ^ 4 * y ^ 5 + (84 : ℝ) * x ^ 3 * y ^ 6 + (36 : ℝ) * x ^ 2 * y ^ 7 + (9 : ℝ) * x * y ^ 8 + y ^ 9 := by comm_ring
  exact ()
end Example24

namespace Example25
def h (x : ℝ) := by
  have h1 : (x ^ 2 + (1 : ℝ)) ^ 2 = x ^ 4 + (2 : ℝ) * x ^ 2 + (1 : ℝ) := by comm_ring
  exact ()
end Example25

namespace Example26
def h (x y : ℝ) := by
  have h1 : (x ^ 2 + y ^ 2) ^ 2 = x ^ 4 + (2 : ℝ) * x ^ 2 * y ^ 2 + y ^ 4 := by comm_ring
  exact ()
end Example26

namespace Example27
def h (x : ℝ) (n : ℕ) := by
  have h1 : (x ^ n + (1 : ℝ)) ^ 2 = x ^ (2 * n) + (2 : ℝ) * x ^ n + (1 : ℝ) := by comm_ring
  exact ()
end Example27

namespace Example28
def h (x y : ℝ) (n : ℕ) := by
  have h1 : (x ^ n + y ^ n) ^ 2 = x ^ (2 * n) + (2 : ℝ) * x ^ n * y ^ n + y ^ (2 * n) := by comm_ring
  exact ()
end Example28

namespace Example29
def h (x : ℝ) (n : ℕ) := by
  have h1 : (x ^ n ^ 2 + (1 : ℝ)) ^ 2 = x ^ (2 * n ^ 2) + (2 : ℝ) * x ^ n ^ 2 + (1 : ℝ) := by comm_ring
  exact ()
end Example29

namespace Example30
def h (x : ℝ) (n : ℕ) := by
  have h1 : (x ^ (2 * n) + (1 : ℝ)) ^ 2 = x ^ (4 * n) + (2 : ℝ) * x ^ (2 * n) + (1 : ℝ) := by comm_ring
  exact ()
end Example30

namespace Example31
def h := by
  have h1 : 1000340282366920938463463374607431768211456 = 1000340282366920938463463374607431768211456 := by term_trivial
  exact ()
end Example31

namespace Example32
def h (x y : ℝ) := by
  have h1 : x + y = y + x := by term_trivial
  exact ()
end Example32

namespace Example33
def h (x : ℝ) (h1 : x = (1 : ℝ)) := by
  have h2 : x = (1 : ℝ) := by old_main_hypothesis
  exact ()
end Example33

namespace Example34
def h := by
  let x := 1
  have h1 : x = 1 := by let_assigned
  have h2 : x = 1 := by old_main_hypothesis
  exact ()
end Example34

namespace Example35
def h := by
  let x := 1
  have h1 : x = 1 := by let_assigned
  have h2 : x > 0 := by litnum_reduce
  exact ()
end Example35

namespace Example36
def h := by
  let x := 1
  have h1 : x = 1 := by let_assigned
  let y := 1
  have h2 : y = 1 := by let_assigned
  let z := 2
  have h3 : z = 2 := by let_assigned
  have h4 : x + y = z := by litnum_reduce
  exact ()
end Example36

namespace Example37
def h (x : ℝ) (h1 : x > (0 : ℝ)) := by
  have h2 : x > (0 : ℝ) := by old_main_hypothesis
  exact ()
end Example37

namespace Example38
def h (x : ℝ) (h1 : x > (1 : ℝ)) := by
  have h2 : x > (0 : ℝ) := by litnum_bound
  exact ()
end Example38

namespace Example39
def h (x : ℝ) (h1 : x > (1 : ℝ)) := by
  have h2 : x ≥ (1 : ℝ) := by litnum_bound
  exact ()
end Example39

namespace Example40
def h (x : ℝ) (h1 : x ≥ (1 : ℝ)) := by
  have h2 : x ≥ (0 : ℝ) := by litnum_bound
  exact ()
end Example40

namespace Example41
def h (x : ℝ) (h1 : x ≥ (1 : ℝ)) := by
  have h2 : x > (0 : ℝ) := by litnum_bound
  exact ()
end Example41

namespace Example42
def h (x : ℝ) (h1 : x < (1 : ℝ)) := by
  have h2 : x ≤ (1 : ℝ) := by litnum_bound
  exact ()
end Example42

namespace Example43
def h (x : ℝ) (h1 : x < (1 : ℝ)) := by
  have h2 : x < (2 : ℝ) := by litnum_bound
  exact ()
end Example43

namespace Example44
def h (x : ℝ) (h1 : x < (1 : ℝ)) := by
  have h2 : x ≤ (2 : ℝ) := by litnum_bound
  exact ()
end Example44

namespace Example45
def h (x : ℝ) (h1 : x ≤ (1 : ℝ)) := by
  have h2 : x < (2 : ℝ) := by litnum_bound
  exact ()
end Example45

namespace Example46
def h (x : ℝ) (h1 : x ≤ (1 : ℝ)) := by
  have h2 : x ≤ (2 : ℝ) := by litnum_bound
  exact ()
end Example46

namespace Example47
def h (x : ℝ) (h1 : (- x : ℝ) > (0 : ℝ)) := by
  have h2 : (- x : ℝ) > (0 : ℝ) := by old_main_hypothesis
  exact ()
end Example47

namespace Example48
def h (x : ℝ) (h1 : (- x : ℝ) > (1 : ℝ)) := by
  have h2 : (- x : ℝ) > (0 : ℝ) := by litnum_bound
  exact ()
end Example48

namespace Example49
def h (x : ℝ) (h1 : (- x : ℝ) > (1 : ℝ)) := by
  have h2 : (- x : ℝ) ≥ (1 : ℝ) := by litnum_bound
  exact ()
end Example49

namespace Example50
def h (x : ℝ) (h1 : (- x : ℝ) ≥ (1 : ℝ)) := by
  have h2 : (- x : ℝ) ≥ (0 : ℝ) := by litnum_bound
  exact ()
end Example50

namespace Example51
def h (x : ℝ) (h1 : (- x : ℝ) ≥ (1 : ℝ)) := by
  have h2 : (- x : ℝ) > (0 : ℝ) := by litnum_bound
  exact ()
end Example51

namespace Example52
def h (x : ℝ) (h1 : (- x : ℝ) < (1 : ℝ)) := by
  have h2 : (- x : ℝ) ≤ (1 : ℝ) := by litnum_bound
  exact ()
end Example52

namespace Example53
def h (x : ℝ) (h1 : (- x : ℝ) < (1 : ℝ)) := by
  have h2 : (- x : ℝ) < (2 : ℝ) := by litnum_bound
  exact ()
end Example53

namespace Example54
def h (x : ℝ) (h1 : (- x : ℝ) < (1 : ℝ)) := by
  have h2 : (- x : ℝ) ≤ (2 : ℝ) := by litnum_bound
  exact ()
end Example54

namespace Example55
def h (x : ℝ) (h1 : (- x : ℝ) ≤ (1 : ℝ)) := by
  have h2 : (- x : ℝ) < (2 : ℝ) := by litnum_bound
  exact ()
end Example55

namespace Example56
def h (x : ℝ) (h1 : (- x : ℝ) ≤ (1 : ℝ)) := by
  have h2 : (- x : ℝ) ≤ (2 : ℝ) := by litnum_bound
  exact ()
end Example56

namespace Example57
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) > (0 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) > (0 : ℝ) := by old_main_hypothesis
  exact ()
end Example57

namespace Example58
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) > (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) > (0 : ℝ) := by litnum_bound
  exact ()
end Example58

namespace Example59
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) > (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) ≥ (1 : ℝ) := by litnum_bound
  exact ()
end Example59

namespace Example60
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) ≥ (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) ≥ (0 : ℝ) := by litnum_bound
  exact ()
end Example60

namespace Example61
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) ≥ (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) > (0 : ℝ) := by litnum_bound
  exact ()
end Example61

namespace Example62
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) < (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) ≤ (1 : ℝ) := by litnum_bound
  exact ()
end Example62

namespace Example63
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) < (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) < (2 : ℝ) := by litnum_bound
  exact ()
end Example63

namespace Example64
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) < (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) ≤ (2 : ℝ) := by litnum_bound
  exact ()
end Example64

namespace Example65
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) ≤ (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) < (2 : ℝ) := by litnum_bound
  exact ()
end Example65

namespace Example66
def h (x : ℝ) (h1 : (-((2 : ℝ) * x) : ℝ) ≤ (1 : ℝ)) := by
  have h2 : (-((2 : ℝ) * x) : ℝ) ≤ (2 : ℝ) := by litnum_bound
  exact ()
end Example66

namespace Example67
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) > (0 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) > (0 : ℝ) := by old_main_hypothesis
  exact ()
end Example67

namespace Example68
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) > (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) > (0 : ℝ) := by litnum_bound
  exact ()
end Example68

namespace Example69
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) > (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≥ (1 : ℝ) := by litnum_bound
  exact ()
end Example69

namespace Example70
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≥ (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≥ (0 : ℝ) := by litnum_bound
  exact ()
end Example70

namespace Example71
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≥ (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) > (0 : ℝ) := by litnum_bound
  exact ()
end Example71

namespace Example72
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) < (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≤ (1 : ℝ) := by litnum_bound
  exact ()
end Example72

namespace Example73
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) < (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) < (2 : ℝ) := by litnum_bound
  exact ()
end Example73

namespace Example74
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) < (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≤ (2 : ℝ) := by litnum_bound
  exact ()
end Example74

namespace Example75
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≤ (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) < (2 : ℝ) := by litnum_bound
  exact ()
end Example75

namespace Example76
def h (x : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≤ (1 : ℝ)) := by
  have h2 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) ≤ (2 : ℝ) := by litnum_bound
  exact ()
end Example76

namespace Example77
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y > (0 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y > (0 : ℝ) := by litnum_bound
  exact ()
end Example77

namespace Example78
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y > (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y > (0 : ℝ) := by litnum_bound
  exact ()
end Example78

namespace Example79
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y > (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y ≥ ((1 : ℚ) / (2 : ℚ) : ℝ) := by litnum_bound
  exact ()
end Example79

namespace Example80
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y ≥ (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y ≥ (0 : ℝ) := by litnum_bound
  exact ()
end Example80

namespace Example81
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y ≥ (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y > (0 : ℝ) := by litnum_bound
  exact ()
end Example81

namespace Example82
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y < (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y ≤ ((1 : ℚ) / (2 : ℚ) : ℝ) := by litnum_bound
  exact ()
end Example82

namespace Example83
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y < (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y < (1 : ℝ) := by litnum_bound
  exact ()
end Example83

namespace Example84
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y < (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y ≤ (1 : ℝ) := by litnum_bound
  exact ()
end Example84

namespace Example85
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y ≤ (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y < (1 : ℝ) := by litnum_bound
  exact ()
end Example85

namespace Example86
def h (x y : ℝ) (h1 : (-(((2 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + (2 : ℝ) * y ≤ (1 : ℝ)) := by
  have h2 : (-(((1 : ℚ) / (3 : ℚ) : ℝ) * x) : ℝ) + y ≤ (1 : ℝ) := by litnum_bound
  exact ()
end Example86

namespace Example87
def h := by
  have h1 : 0 < 2 := by calc
    0 < 1 := by obvious
    _ < 2 := by obvious
  exact ()
end Example87

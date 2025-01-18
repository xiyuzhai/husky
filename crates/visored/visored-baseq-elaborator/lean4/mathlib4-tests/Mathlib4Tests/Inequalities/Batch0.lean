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

macro "term_derivation_variable": tactic =>`(tactic|
  first
  | rfl; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_literal": tactic =>`(tactic|
  first
  | rfl; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_item_path": tactic =>`(tactic|
  first
  | rfl; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_sum": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_sub": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_product": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_div": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_finalize" d1:term:1024 d2:term:1024 : tactic =>`(tactic|
  (apply (Iff.mpr $d2); apply (Iff.mp $d1); assumption)
)

macro "term_derivation_chaining_separated_list": tactic =>`(tactic|
  first
  | ring; done
  | (constructor; repeat (intro h; linarith))
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_square": tactic =>`(tactic|
  first
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

macro "term_derivation_power": tactic =>`(tactic|
  first
  | rfl; done
  | ring; done
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)


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
  have h1 : (2 : ℚ) ≠ 0 := by term_trivial
  have h2 : (1 : ℚ) / (2 : ℚ) * (2 : ℚ) = (1 : ℚ) := by
    have d : (2 : ℚ) = 2 := by term_derivation_literal
    have d1 : 0 = 0 := by term_derivation_literal
    have d2 : (2 : ℚ) ≠ 0 ↔ true := by term_derivation_chaining_separated_list
    have d3 : (1 : ℚ) = 1 := by term_derivation_literal
    have d4 : (2 : ℚ) = 2 := by term_derivation_literal
    have d5 : (1 : ℚ) / (2 : ℚ) = (1 : ℚ) / (2 : ℚ) := by term_derivation_div
    have d6 : (2 : ℚ) = 2 := by term_derivation_literal
    have d7 : (1 : ℚ) / (2 : ℚ) * (2 : ℚ) = (1 : ℚ) := by term_derivation_product
    have d8 : (1 : ℚ) = 1 := by term_derivation_literal
    have d9 : (1 : ℚ) / (2 : ℚ) * (2 : ℚ) = (1 : ℚ) ↔ true := by term_derivation_chaining_separated_list
    have d10 : (1 : ℚ) / (2 : ℚ) * (2 : ℚ) = (1 : ℚ) := by term_derivation_finalize d2 d9
    assumption
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
    have d : x = x := by term_derivation_variable
    have d1 : (1 : ℝ) = 1 := by term_derivation_literal
    have d2 : x ≥ (1 : ℝ) ↔ (-1 : ℝ) + x ≥ (0 : ℝ) := by term_derivation_chaining_separated_list
    have d3 : x = x := by term_derivation_variable
    have d4 : (1 : ℝ) = 1 := by term_derivation_literal
    have d5 : x - (1 : ℝ) = (-1 : ℝ) + x := by term_derivation_sub
    have d6 : (0 : ℝ) = 0 := by term_derivation_literal
    have d7 : x - (1 : ℝ) ≥ (0 : ℝ) ↔ (-1 : ℝ) + x ≥ (0 : ℝ) := by term_derivation_chaining_separated_list
    have d8 : x - (1 : ℝ) ≥ (0 : ℝ) := by term_derivation_finalize d2 d7
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
  have h2 : x = 1 := by
    have d : x = x := by term_derivation_variable
    have d1 : 1 = 1 := by term_derivation_literal
    have d2 : x = 1 ↔ (-1 : ℤ) + (x : ℤ) = (0 : ℤ) := by term_derivation_chaining_separated_list
    have d3 : x = x := by term_derivation_variable
    have d4 : 1 = 1 := by term_derivation_literal
    have d5 : x = 1 ↔ (-1 : ℤ) + (x : ℤ) = (0 : ℤ) := by term_derivation_chaining_separated_list
    have d6 : x = 1 := by term_derivation_finalize d2 d5
    assumption
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

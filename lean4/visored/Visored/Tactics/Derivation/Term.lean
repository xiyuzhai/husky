import Mathlib

macro "term_derivation_reflection": tactic => `(tactic|
  first
  | fail "Could not prove this goal automatically. Afterall, this is an ad hoc implementation."
)

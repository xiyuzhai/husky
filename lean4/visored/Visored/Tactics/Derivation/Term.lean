import Mathlib
import Visored.Tactics.Derivation.Term.Sum
import Visored.Tactics.Derivation.Term.Product
import Visored.Tactics.Derivation.Term.Coercion

macro "term_derivation_neg_literal": tactic => `(tactic| norm_num)
macro "term_derivation_num_comparison": tactic => `(tactic| fail)
macro "term_derivation_reflection": tactic => `(tactic| rfl)
macro "term_derivation_power_one": tactic => `(tactic| fail)
macro "term_derivation_one_mul": tactic => `(tactic| fail)
macro "term_derivation_nf_add_zero": tactic => `(tactic| fail)
macro "term_derivation_non_trivial_finish": tactic => `(tactic| fail)

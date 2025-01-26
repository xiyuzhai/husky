import Mathlib
import Visored.Tactics.Derivation.Term.Sum
import Visored.Tactics.Derivation.Term.Product
import Visored.Tactics.Derivation.Term.Coercion

macro "term_derivation_add_eq": tactic => `(tactic| sorry)
macro "term_derivation_atom_add_non_zero_literal": tactic => `(tactic| sorry)
macro "term_derivation_neg_literal": tactic => `(tactic| norm_num)
macro "term_derivation_num_comparison": tactic => `(tactic| sorry)
macro "term_derivation_reflection": tactic => `(tactic| rfl)
macro "term_derivation_sub_eqs_add_neg": tactic => `(tactic| sorry)
macro "term_derivation_power_one": tactic => `(tactic| sorry)
macro "term_derivation_one_mul": tactic => `(tactic| sorry)
macro "term_derivation_nf_add_zero": tactic => `(tactic| sorry)
macro "term_derivation_non_trivial_finish": tactic => `(tactic| sorry)

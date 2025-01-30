import Mathlib
import Visored.Tactics.Derivation.Term.Sum
import Visored.Tactics.Derivation.Term.Product
import Visored.Tactics.Derivation.Term.Coercion

macro "term_derivation_neg_literal": tactic => `(tactic| norm_num)
macro "term_derivation_num_comparison": tactic => `(tactic| norm_num)
macro "term_derivation_reflection": tactic => `(tactic| rfl)
/-- derive `dst` from `src`, `src_nf` and `dst_nf` -/
macro "term_derivation_non_trivial_finish" src:term:1024 src_nf:term:1024 dst_nf:term:1024 : tactic => `(tactic| fail "not implemented")

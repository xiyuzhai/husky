
macro "term_derivation_power_one": tactic => `(tactic| simp)
macro "term_derivation_one_mul": tactic => `(tactic| simp)
macro "term_derivation_mul_one": tactic => `(tactic| simp)
macro "term_derivation_div_literal": tactic => `(tactic| simp)
macro "term_derivation_div_eq": tactic => `(tactic| fail)

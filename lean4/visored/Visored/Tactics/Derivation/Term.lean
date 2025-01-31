import Mathlib
import Visored.Tactics.Derivation.Term.Sum
import Visored.Tactics.Derivation.Term.Product
import Visored.Tactics.Derivation.Term.Coercion

macro "term_derivation_neg_literal": tactic => `(tactic| norm_num)
macro "term_derivation_num_comparison": tactic => `(tactic| norm_num)
macro "term_derivation_reflection": tactic => `(tactic| rfl)

theorem term_derivation_non_trivial_hypothesis_equivalence {src dst nf : Prop} (hsrc: src) (hsrc_nf: src ↔ nf) (hdst_nf: dst ↔ nf) : dst := by
  have hnf : nf := hsrc_nf.mp hsrc
  exact hdst_nf.mpr hnf

/-- derive `dst` from `src`, `src_nf` and `dst_nf` -/
macro "term_derivation_non_trivial_hypothesis_equivalence" src:term:1024 src_nf:term:1024 dst_nf:term:1024 : tactic
  => `(tactic| exact term_derivation_non_trivial_hypothesis_equivalence $src $src_nf $dst_nf)

theorem term_derivation_non_trivial_expr_equivalence_eq {α} {a b term: α}
  (ha_nf: a = term)
  (hb_nf: b = term)
  : a = b := by
  rw [ha_nf, hb_nf]


macro "term_derivation_non_trivial_expr_equivalence_eq" ha_nf:term:1024 hb_nf:term:1024 : tactic
  => `(tactic| exact term_derivation_non_trivial_expr_equivalence_eq $ha_nf $hb_nf)

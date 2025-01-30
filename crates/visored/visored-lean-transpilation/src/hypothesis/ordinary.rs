use super::*;

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(super) fn build_ordinary_hypothesis_tactics(
        &mut self,
        hypothesis: VdMirHypothesisIdx,
        hypothesis_entry: &VdMirHypothesisEntry,
        ln_tactics: &mut Vec<LnMirTacticData>,
    ) {
        let construction_tactics = match *hypothesis_entry.construction() {
            VdMirHypothesisConstruction::Sorry => {
                let default_tactic_data = self.default_tactic_data();
                self.alloc_tactics([default_tactic_data])
            }
            VdMirHypothesisConstruction::TermTrivial(b) => {
                let custom_tactic_data = self.custom_tactic_data("term_trivial", None, None);
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::Apply {
                path,
                is_real_coercion,
            } => match path {
                VdTheoremPath::SquareNonnegative => {
                    match is_real_coercion {
                        VdMirCoercionConstruction::Trivial => (),
                        VdMirCoercionConstruction::Obvious(arena_idx) => {
                            todo!("handle this properly.")
                        }
                    }
                    let hypothesis = self.alloc_expr(LnMirExprEntry::new(LnMirExprData::ItemPath(
                        LnTheoremPath::SquareNonnegative.into(),
                    )));
                    self.alloc_tactics([
                        LnMirTacticData::Simp,
                        LnMirTacticData::Apply { hypothesis },
                    ])
                }
            },
            VdMirHypothesisConstruction::Assume => return,
            VdMirHypothesisConstruction::TermEquivalence {
                hypothesis,
                derivation_chunk,
            } => self.build_derivation_tactics(derivation_chunk, ln_tactics),
            VdMirHypothesisConstruction::CommRing => {
                let custom_tactic_data = self.custom_tactic_data("comm_ring", None, None);
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::LetAssigned => {
                let custom_tactic_data = self.custom_tactic_data("let_assigned", None, None);
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::LitnumReduce => {
                let custom_tactic_data = self.custom_tactic_data("litnum_reduce", None, None);
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::LitnumBound => {
                let custom_tactic_data = self.custom_tactic_data("litnum_bound", None, None);
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::Kurapika => todo!(),
        };
        let construction = self.alloc_expr(LnMirExprEntry::new(LnMirExprData::By {
            tactics: construction_tactics,
        }));
        let ident = self.mangle_hypothesis(hypothesis);
        ln_tactics.push(LnMirTacticData::Have {
            ident,
            ty: Some(hypothesis_entry.expr().to_lean(self)),
            construction,
        });
    }
}

use super::*;

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(super) fn build_ordinary_hypothesis_tactics(
        &mut self,
        hypothesis_entry: &VdMirHypothesisEntry,
        ln_tactics: &mut Vec<LnMirTacticData>,
    ) {
        let construction_tactics = match hypothesis_entry.construction() {
            VdMirHypothesisConstruction::Sorry => {
                let default_tactic_data = self.default_tactic_data();
                self.alloc_tactics([default_tactic_data])
            }
            VdMirHypothesisConstruction::TermTrivial(b) => {
                let custom_tactic_data = self.custom_tactic_data("term_trivial");
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::Apply {
                path,
                is_real_coercion,
            } => {
                match is_real_coercion {
                    VdMirCoercion::Trivial => (),
                    VdMirCoercion::Obvious(arena_idx) => todo!("handle this properly."),
                }
                self.alloc_tactics([LnMirTacticData::Apply {
                    path: match path {
                        VdTheoremPath::SquareNonnegative => LnTheoremPath::SquareNonnegative,
                    },
                }])
            }
            VdMirHypothesisConstruction::Assume => return,
            VdMirHypothesisConstruction::TermEquivalent {
                hypothesis,
                derivations,
            } => {
                for _ in derivations {
                    todo!("handle derivations");
                }
                let custom_tactic_data = self.custom_tactic_data("term_equivalent");
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::CommRing => {
                let custom_tactic_data = self.custom_tactic_data("comm_ring");
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::LetAssigned => {
                let custom_tactic_data = self.custom_tactic_data("let_assigned");
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::LitnumReduce => {
                let custom_tactic_data = self.custom_tactic_data("litnum_reduce");
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::LitnumBound => {
                let custom_tactic_data = self.custom_tactic_data("litnum_bound");
                self.alloc_tactics([custom_tactic_data])
            }
            VdMirHypothesisConstruction::Kurapika => todo!(),
        };
        let construction = self.alloc_expr(LnMirExprEntry::new(
            LnMirExprData::By {
                tactics: construction_tactics,
            },
            None,
        ));
        let ident = self.mangle_hypothesis();
        ln_tactics.push(LnMirTacticData::Have {
            ident,
            ty: Some(hypothesis_entry.expr().to_lean(self)),
            construction,
        });
    }
}

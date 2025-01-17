use super::*;

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(super) fn build_old_main_hypothesis_tactics(
        &mut self,
        main_hypothesis: VdMirHypothesisIdx,
        ln_tactics: &mut Vec<LnMirTacticData>,
    ) {
        let custom_tactic_data = self.custom_tactic_data("old_main_hypothesis", None, None);
        let construction_tactics = self.alloc_tactics([custom_tactic_data]);
        let construction = self.alloc_expr(LnMirExprEntry::new(
            LnMirExprData::By {
                tactics: construction_tactics,
            },
            None,
        ));
        ln_tactics.push(LnMirTacticData::Have {
            ident: self.mangle_old_main_hypothesis(),
            ty: Some(
                self.hypothesis_arena()[main_hypothesis]
                    .expr()
                    .to_lean(self),
            ),
            construction,
        });
    }
}

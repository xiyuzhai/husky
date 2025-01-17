mod nontrivial_chain;
mod old_main;
mod ordinary;

use super::*;
use lean_entity_path::theorem::LnTheoremPath;
use lean_mir_expr::{
    expr::{LnMirExprData, LnMirExprEntry},
    tactic::{LnMirTacticData, LnMirTacticIdxRange},
};
use visored_entity_path::theorem::VdTheoremPath;
use visored_mir_expr::{
    coercion::VdMirCoercion,
    expr::VdMirExprData,
    hypothesis::{
        chunk::VdMirHypothesisChunk, construction::VdMirHypothesisConstruction,
        VdMirHypothesisEntry, VdMirHypothesisIdx,
    },
};

impl<'a, S> VdLeanTranspilationBuilder<'a, S>
where
    S: IsVdLeanTranspilationScheme,
{
    pub(crate) fn build_hypothesis_chunk_tactics(
        &mut self,
        hypothesis_chunk: VdMirHypothesisChunk,
        ln_tactics: &mut Vec<LnMirTacticData>,
    ) {
        let new_hypotheses = hypothesis_chunk.new_hypotheses();
        let main_hypothesis = hypothesis_chunk.main_hypothesis();
        for hypothesis in new_hypotheses {
            self.build_hypothesis_tactics(hypothesis, ln_tactics);
        }
        if !new_hypotheses.contains(main_hypothesis) {
            self.build_old_main_hypothesis_tactics(main_hypothesis, ln_tactics);
        }
    }

    fn build_hypothesis_tactics(
        &mut self,
        hypothesis: VdMirHypothesisIdx,
        ln_tactics: &mut Vec<LnMirTacticData>,
    ) {
        let hypothesis_entry = &self.hypothesis_arena()[hypothesis];
        match *self.expr_arena()[hypothesis_entry.expr()].data() {
            VdMirExprData::ChainingSeparatedList {
                leader,
                ref followers,
                joined_signature: Some(joined_signature),
            } => self.build_nontrivial_chain_hypothesis_tactics(
                hypothesis_entry,
                leader,
                followers,
                joined_signature,
                ln_tactics,
            ),
            _ => self.build_ordinary_hypothesis_tactics(hypothesis, hypothesis_entry, ln_tactics),
        }
    }
}

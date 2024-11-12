use super::*;
use symbol::local_defn::VdSemSymbolLocalDefnIdx;
use visored_global_resolution::resolution::letter::VdLetterGlobalResolution;
use visored_syn_expr::symbol::resolution::{
    letter::VdSynLetterSymbolResolution, VdSynSymbolResolution,
};

#[derive(Debug, PartialEq, Eq)]
pub enum VdSemLetterDispatch {
    Global(VdLetterGlobalResolution),
    Local(VdSemSymbolLocalDefnIdx),
}

impl<'a> VdSemExprBuilder<'a> {
    pub(super) fn build_letter(
        &mut self,
        syn_expr: VdSynExprIdx,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
    ) -> VdSemExprData {
        use husky_print_utils::p;
        p!(token_idx_range, self.syn_expr_arena()[syn_expr]);
        let resolution = &self.symbol_resolution_table()[syn_expr];
        let dispatch = match resolution {
            Ok(resolution) => {
                let VdSynSymbolResolution::Letter(resolution) = resolution else {
                    unreachable!()
                };
                self.build_letter_dispatch(resolution)
            }
            Err(e) => todo!("letter = `{letter}`, e = {e}"),
        };
        VdSemExprData::Letter {
            token_idx_range,
            letter,
            dispatch,
        }
    }

    fn build_letter_dispatch(
        &mut self,
        resolution: &VdSynLetterSymbolResolution,
    ) -> VdSemLetterDispatch {
        match *resolution {
            VdSynLetterSymbolResolution::Global(global_resolution) => {
                VdSemLetterDispatch::Global(global_resolution)
            }
            VdSynLetterSymbolResolution::Local(local_defn_idx) => {
                VdSemLetterDispatch::Local(local_defn_idx.to_vd_sem(self))
            }
        }
    }
}

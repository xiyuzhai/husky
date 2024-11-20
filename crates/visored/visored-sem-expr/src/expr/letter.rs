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
    ) -> (VdSemExprData, VdType) {
        let resolution = &self.syn_symbol_resolution_table()[syn_expr];
        let dispatch = match resolution {
            Ok(resolution) => {
                let VdSynSymbolResolution::Letter(resolution) = resolution else {
                    unreachable!()
                };
                self.build_letter_dispatch(resolution)
            }
            Err(e) => todo!("letter = `{letter}`, e = {e}"),
        };
        let ty = match dispatch {
            VdSemLetterDispatch::Global(global_resolution) => {
                self.infer_letter_ty_from_global_resolution(global_resolution)
            }
            VdSemLetterDispatch::Local(local_defn) => {
                self.infer_letter_ty_from_local_defn(local_defn)
            }
        };
        (
            VdSemExprData::Letter {
                token_idx_range,
                letter,
                dispatch,
            },
            ty,
        )
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

    fn infer_letter_ty_from_global_resolution(
        &mut self,
        global_resolution: VdLetterGlobalResolution,
    ) -> VdType {
        match global_resolution {
            VdLetterGlobalResolution::Item(item_path) => self.item_path_zfc_type_table()[item_path],
        }
    }

    fn infer_letter_ty_from_local_defn(&mut self, local_defn: VdSemSymbolLocalDefnIdx) -> VdType {
        self.symbol_local_defn_storage()[local_defn].ty()
    }

    pub(super) fn calc_letter_term(
        &self,
        expr: VdSemExprIdx,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
        dispatch: &VdSemLetterDispatch,
    ) -> VdTerm {
        match *dispatch {
            VdSemLetterDispatch::Global(global_resolution) => self
                .calc_letter_term_from_global_resolution(
                    expr,
                    token_idx_range,
                    letter,
                    global_resolution,
                ),
            VdSemLetterDispatch::Local(local_defn) => {
                self.calc_letter_term_from_local_defn(expr, token_idx_range, letter, local_defn)
            }
        }
    }

    fn calc_letter_term_from_global_resolution(
        &self,
        expr: VdSemExprIdx,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
        global_resolution: VdLetterGlobalResolution,
    ) -> VdTerm {
        match global_resolution {
            VdLetterGlobalResolution::Item(item_path) => {
                VdTerm::new_item_path(item_path, self.db())
            }
        }
    }

    fn calc_letter_term_from_local_defn(
        &self,
        expr: VdSemExprIdx,
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
        local_defn: VdSemSymbolLocalDefnIdx,
    ) -> VdTerm {
        todo!()
    }
}

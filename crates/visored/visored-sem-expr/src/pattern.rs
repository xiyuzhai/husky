use super::*;
use latex_math_letter::letter::LxMathLetter;
use latex_token::idx::LxTokenIdxRange;
use symbol::local_defn::VdSemSymbolLocalDefnIdx;
use visored_syn_expr::{
    pattern::VdSynPattern,
    symbol::resolution::{letter::VdSynLetterSymbolResolution, VdSynSymbolResolution},
};
use visored_term::ty::VdType;

#[derive(Debug, PartialEq, Eq)]
pub enum VdSemPattern {
    Letter {
        token_idx_range: LxTokenIdxRange,
        letter: LxMathLetter,
        local_defn: VdSemSymbolLocalDefnIdx,
    },
}

impl ToVdSem<VdSemPattern> for &VdSynPattern {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemPattern {
        match *self {
            VdSynPattern::Letter {
                token_idx_range,
                letter,
                pattern_expr,
            } => {
                let Ok(resolution) = &builder.syn_symbol_resolution_table()[pattern_expr] else {
                    todo!()
                };
                let syn_local_defn = match *resolution {
                    VdSynSymbolResolution::Letter(ref symbol_resolution) => {
                        match *symbol_resolution {
                            VdSynLetterSymbolResolution::Local(local_defn) => local_defn,
                            _ => todo!(),
                        }
                    }
                };
                VdSemPattern::Letter {
                    token_idx_range,
                    letter,
                    local_defn: syn_local_defn.to_vd_sem(builder),
                }
            }
        }
    }
}

impl<'db> VdSemExprBuilder<'db> {
    pub(crate) fn infer_pattern_symbol_tys(&mut self, pattern: &VdSemPattern, ty: VdType) {
        match *pattern {
            VdSemPattern::Letter {
                token_idx_range,
                letter,
                local_defn,
            } => self.set_local_defn_ty(local_defn, ty),
        }
    }
}

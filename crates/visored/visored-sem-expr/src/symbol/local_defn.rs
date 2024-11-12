use super::*;
use idx_arena::ArenaIdx;
use latex_math_letter::letter::LxMathLetter;
use latex_token::idx::LxTokenIdxRange;
use visored_syn_expr::symbol::local_defn::VdSynSymbolLocalDefnIdx;

#[derive(Debug, PartialEq, Eq)]
pub struct VdSemSymbolLocalDefn {
    pub head: VdSemSymbolLocalDefnHead,
    pub body: VdSemSymbolLocalDefnBody,
}

#[derive(Debug, PartialEq, Eq)]
pub enum VdSemSymbolLocalDefnHead {
    Letter(LxTokenIdxRange, LxMathLetter),
}

#[derive(Debug, PartialEq, Eq)]
pub enum VdSemSymbolLocalDefnBody {
    Assigned,
    Placeholder,
}

pub type VdSemSymbolLocalDefnIdx = ArenaIdx<VdSemSymbolLocalDefn>;

impl ToVdSem<VdSemSymbolLocalDefnIdx> for VdSynSymbolLocalDefnIdx {
    fn to_vd_sem(self, _: &mut VdSemExprBuilder) -> VdSemSymbolLocalDefnIdx {
        // INVARIANCE: the index is always the same as the syn index
        unsafe { VdSemSymbolLocalDefnIdx::new_ext(self.index()) }
    }
}

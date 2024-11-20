pub mod storage;

use super::*;
use idx_arena::{Arena, ArenaIdx};
use latex_math_letter::letter::LxMathLetter;
use latex_token::idx::LxTokenIdxRange;
use visored_item_path::module::VdModulePath;
use visored_syn_expr::symbol::local_defn::{
    VdSynSymbolLocalDefnBody, VdSynSymbolLocalDefnHead, VdSynSymbolLocalDefnIdx,
};
use visored_term::ty::VdType;

#[derive(Debug, PartialEq, Eq)]
pub struct VdSemSymbolLocalDefnData {
    head: VdSemSymbolLocalDefnHead,
    body: VdSemSymbolLocalDefnBody,
    /// initialized to be `None`
    /// and will be set to the inferred type when the type is inferred
    ty: Option<VdType>,
    module_path: VdModulePath,
}

impl VdSemSymbolLocalDefnData {
    pub fn head(&self) -> &VdSemSymbolLocalDefnHead {
        &self.head
    }

    pub fn body(&self) -> &VdSemSymbolLocalDefnBody {
        &self.body
    }

    pub fn ty(&self) -> VdType {
        self.ty.expect("all local defns' types are inferred")
    }

    pub fn module_path(&self) -> VdModulePath {
        self.module_path
    }
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

pub type VdSemSymbolLocalDefnArena = Arena<VdSemSymbolLocalDefnData>;
pub type VdSemSymbolLocalDefnIdx = ArenaIdx<VdSemSymbolLocalDefnData>;

impl ToVdSem<VdSemSymbolLocalDefnIdx> for VdSynSymbolLocalDefnIdx {
    fn to_vd_sem(self, _: &mut VdSemExprBuilder) -> VdSemSymbolLocalDefnIdx {
        // INVARIANCE: the index is always the same as the syn index
        unsafe { VdSemSymbolLocalDefnIdx::new_ext(self.index()) }
    }
}

impl VdSemSymbolLocalDefnData {
    pub(crate) fn set_ty(&mut self, ty: VdType) {
        debug_assert!(self.ty.is_none(), "local defn's type is already inferred");
        self.ty = Some(ty);
    }
}

impl<'a> VdSemExprBuilder<'a> {
    pub(crate) fn build_symbol_local_defns(
        &mut self,
        syn_symbol_local_defn_storage: &VdSynSymbolLocalDefnStorage,
    ) {
        let mut defns = vec![];
        for defn in syn_symbol_local_defn_storage.defn_arena() {
            defns.push(self.build_symbol_local_defn(defn));
        }
        self.alloc_local_defns(defns);
    }

    fn build_symbol_local_defn(
        &mut self,
        defn: &VdSynSymbolLocalDefnData,
    ) -> VdSemSymbolLocalDefnData {
        let head = self.build_symbol_local_defn_head(defn.head());
        let body = self.build_symbol_local_defn_body(defn.body());
        VdSemSymbolLocalDefnData {
            head,
            body,
            ty: None,
            module_path: defn.module_path(),
        }
    }

    fn build_symbol_local_defn_head(
        &mut self,
        head: &VdSynSymbolLocalDefnHead,
    ) -> VdSemSymbolLocalDefnHead {
        match *head {
            VdSynSymbolLocalDefnHead::Letter {
                token_idx_range,
                letter,
            } => VdSemSymbolLocalDefnHead::Letter(token_idx_range, letter),
        }
    }

    fn build_symbol_local_defn_body(
        &mut self,
        body: &VdSynSymbolLocalDefnBody,
    ) -> VdSemSymbolLocalDefnBody {
        match *body {
            VdSynSymbolLocalDefnBody::Assigned => VdSemSymbolLocalDefnBody::Assigned,
            VdSynSymbolLocalDefnBody::Placeholder => VdSemSymbolLocalDefnBody::Placeholder,
        }
    }
}

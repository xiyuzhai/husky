use super::*;

pub struct VdSemSymbolLocalDefnStorage {
    defn_arena: VdSemSymbolLocalDefnArena,
}

impl std::ops::Deref for VdSemSymbolLocalDefnStorage {
    type Target = VdSemSymbolLocalDefnArena;

    fn deref(&self) -> &Self::Target {
        &self.defn_arena
    }
}

impl VdSemSymbolLocalDefnStorage {
    pub(crate) fn new_empty() -> Self {
        Self {
            defn_arena: Default::default(),
        }
    }
}

impl VdSemSymbolLocalDefnStorage {
    pub fn defn_arena(&self) -> &VdSemSymbolLocalDefnArena {
        &self.defn_arena
    }
}

impl VdSemSymbolLocalDefnStorage {
    pub(crate) fn set_defns(&mut self, defns: Vec<VdSemSymbolLocalDefnData>) {
        debug_assert!(self.defn_arena.is_empty());
        self.defn_arena = unsafe { VdSemSymbolLocalDefnArena::new_ext(defns) };
    }

    pub(crate) fn set_local_defn_ty(&mut self, local_defn: VdSemSymbolLocalDefnIdx, ty: VdType) {
        self.defn_arena.update(local_defn, |data| data.set_ty(ty));
    }
}

use super::*;

pub struct VdMirSymbolLocalDefnStorage {
    defn_arena: VdMirSymbolLocalDefnArena,
}
impl VdMirSymbolLocalDefnStorage {
    pub(crate) fn new_empty() -> Self {
        Self {
            defn_arena: VdMirSymbolLocalDefnArena::default(),
        }
    }

    pub fn defn_arena(&self) -> &VdMirSymbolLocalDefnArena {
        &self.defn_arena
    }
}

impl VdMirSymbolLocalDefnStorage {
    pub(crate) fn set_defns(&mut self, data: Vec<VdMirSymbolLocalDefnData>) {
        self.defn_arena = unsafe { VdMirSymbolLocalDefnArena::new_ext(data) };
    }
}

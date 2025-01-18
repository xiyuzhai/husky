pub mod chunk;
pub mod construction;

use self::construction::VdMirDerivationConstruction;
use crate::*;
use expr::VdMirExprIdx;
use hypothesis::constructor::VdMirHypothesisConstructor;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};

#[derive(Debug, PartialEq, Eq)]
pub struct VdMirDerivationEntry {
    prop: VdMirExprIdx,
    construction: VdMirDerivationConstruction,
}

pub type VdMirDerivationIdx = ArenaIdx<VdMirDerivationEntry>;
pub type VdMirDerivationIdxRange = ArenaIdxRange<VdMirDerivationEntry>;
pub type VdMirDerivationArena = Arena<VdMirDerivationEntry>;
pub type VdMirDerivationArenaRef<'a> = ArenaRef<'a, VdMirDerivationEntry>;
pub type VdMirDerivationMap<T> = ArenaMap<VdMirDerivationEntry, T>;

impl VdMirDerivationEntry {
    pub fn new<'db, Src>(
        prop: VdMirExprIdx,
        construction: VdMirDerivationConstruction,
        hc: &VdMirHypothesisConstructor<'db, Src>,
    ) -> Self {
        construction.check(prop, hc);
        Self { prop, construction }
    }
}

impl VdMirDerivationEntry {
    pub fn prop(&self) -> VdMirExprIdx {
        self.prop
    }

    pub fn construction(&self) -> &VdMirDerivationConstruction {
        &self.construction
    }
}

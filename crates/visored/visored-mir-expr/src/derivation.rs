pub mod chunk;
pub mod construction;

use self::construction::VdMirDerivationConstruction;
use crate::*;
use expr::VdMirExprIdx;
use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};

#[derive(Debug, PartialEq, Eq)]
pub struct VdMirDerivationEntry {
    prop: VdMirExprIdx,
    construction: VdMirDerivationConstruction,
}

pub type VdMirDerivationIdx = ArenaIdx<VdMirDerivationEntry>;
pub type VdMirDerivationIdxRange = ArenaIdxRange<VdMirDerivationEntry>;
pub type VdMirDerivationArena = Arena<VdMirDerivationEntry>;
pub type VdMirDerivationArenaRef<'a> = ArenaRef<'a, VdMirDerivationEntry>;

impl VdMirDerivationEntry {
    pub fn new(prop: VdMirExprIdx, construction: VdMirDerivationConstruction) -> Self {
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

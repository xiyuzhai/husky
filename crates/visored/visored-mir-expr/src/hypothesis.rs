pub mod chunk;
pub mod construction;
pub mod constructor;
pub mod contradiction;
pub mod region;
pub mod stack;

use self::construction::VdMirHypothesisConstruction;
use crate::{derivation::VdMirDerivationIdxRange, expr::VdMirExprIdx};
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};

pub struct VdMirHypothesisEntry {
    expr: VdMirExprIdx,
    construction: VdMirHypothesisConstruction,
}

pub type VdMirHypothesisIdx = ArenaIdx<VdMirHypothesisEntry>;
pub type VdMirHypothesisIdxRange = ArenaIdxRange<VdMirHypothesisEntry>;
pub type VdMirHypothesisArena = Arena<VdMirHypothesisEntry>;
pub type VdMirHypothesisArenaRef<'a> = ArenaRef<'a, VdMirHypothesisEntry>;

impl VdMirHypothesisEntry {
    pub fn new(expr: VdMirExprIdx, construction: VdMirHypothesisConstruction) -> Self {
        Self { expr, construction }
    }
}

impl VdMirHypothesisEntry {
    pub fn expr(&self) -> VdMirExprIdx {
        self.expr
    }

    pub fn construction(&self) -> &VdMirHypothesisConstruction {
        &self.construction
    }
}

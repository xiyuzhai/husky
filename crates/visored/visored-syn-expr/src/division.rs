use crate::stmt::VdSynStmtIdxRange;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use latex_prelude::division::LxDivisionKind;

#[derive(Debug, PartialEq, Eq)]
pub struct VdSynDivisionData {
    pub kind: LxDivisionKind,
    pub stmts: VdSynStmtIdxRange,
}

pub type VdSynDivisionArena = Arena<VdSynDivisionData>;
pub type VdSynDivisionArenaRef<'a> = ArenaRef<'a, VdSynDivisionData>;
pub type VdSynDivisionMap<T> = ArenaMap<VdSynDivisionData, T>;
pub type VdSynDivisionIdx = ArenaIdx<VdSynDivisionData>;
pub type VdSynDivisionIdxRange = ArenaIdxRange<VdSynDivisionData>;

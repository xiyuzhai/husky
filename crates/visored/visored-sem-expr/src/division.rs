use crate::stmt::VdSemStmtIdxRange;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use latex_prelude::division::LxDivisionKind;

#[derive(Debug, PartialEq, Eq)]
pub struct VdSemDivisionData {
    pub kind: LxDivisionKind,
    pub stmts: VdSemStmtIdxRange,
}

pub type VdSemDivisionArena = Arena<VdSemDivisionData>;
pub type VdSemDivisionArenaRef<'a> = ArenaRef<'a, VdSemDivisionData>;
pub type VdSemDivisionMap<T> = ArenaMap<VdSemDivisionData, T>;
pub type VdSemDivisionIdx = ArenaIdx<VdSemDivisionData>;
pub type VdSemDivisionIdxRange = ArenaIdxRange<VdSemDivisionData>;

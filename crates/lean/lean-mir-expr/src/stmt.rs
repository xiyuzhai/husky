use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use smallvec::SmallVec;

#[derive(Debug, PartialEq, Eq)]
pub enum LnMirStmtData {}

pub type LnMirStmtArena = Arena<LnMirStmtData>;
pub type LnMirStmtArenaRef<'a> = ArenaRef<'a, LnMirStmtData>;
pub type LnMirStmtIdx = ArenaIdx<LnMirStmtData>;
pub type LnMirStmtIdxRange = ArenaIdxRange<LnMirStmtData>;

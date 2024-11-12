use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use smallvec::SmallVec;

#[derive(Debug, PartialEq, Eq)]
pub enum LnHirStmtData {}

pub type LnHirStmtArena = Arena<LnHirStmtData>;
pub type LnHirStmtArenaRef<'a> = ArenaRef<'a, LnHirStmtData>;
pub type LnHirStmtIdx = ArenaIdx<LnHirStmtData>;
pub type LnHirStmtIdxRange = ArenaIdxRange<LnHirStmtData>;

use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use smallvec::SmallVec;

#[derive(Debug, PartialEq, Eq)]
pub enum LnMirTacticData {
    Obtain,
    Exact,
    Cases,
    Rcases,
    Have,
    Show,
}

pub type LnMirTacticArena = Arena<LnMirTacticData>;
pub type LnMirTacticArenaRef<'a> = ArenaRef<'a, LnMirTacticData>;
pub type LnMirTacticIdx = ArenaIdx<LnMirTacticData>;
pub type LnMirTacticIdxRange = ArenaIdxRange<LnMirTacticData>;

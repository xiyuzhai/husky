use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use smallvec::SmallVec;

#[derive(Debug, PartialEq, Eq)]
pub enum LnHirTacticData {
    Obtain,
    Exact,
    Cases,
    Rcases,
    Have,
    Show,
}

pub type LnHirTacticArena = Arena<LnHirTacticData>;
pub type LnHirTacticArenaRef<'a> = ArenaRef<'a, LnHirTacticData>;
pub type LnHirTacticIdx = ArenaIdx<LnHirTacticData>;
pub type LnHirTacticIdxRange = ArenaIdxRange<LnHirTacticData>;

use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use lean_opr::opr::binary::LnBinaryOpr;
use lean_term::instantiation::LnInstantiation;
use smallvec::SmallVec;

use crate::expr::LnMirExprIdx;

#[derive(Debug, PartialEq, Eq)]
pub enum LnMirTacticData {
    Obtain,
    Exact,
    Cases,
    Rcases,
    Have,
    Show,
    Calc {
        leader: LnMirExprIdx,
        followers: SmallVec<[((LnBinaryOpr, LnInstantiation), LnMirExprIdx); 4]>,
    },
    Sorry,
}

pub type LnMirTacticArena = Arena<LnMirTacticData>;
pub type LnMirTacticArenaRef<'a> = ArenaRef<'a, LnMirTacticData>;
pub type LnMirTacticIdx = ArenaIdx<LnMirTacticData>;
pub type LnMirTacticIdxRange = ArenaIdxRange<LnMirTacticData>;

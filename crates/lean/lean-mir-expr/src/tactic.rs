use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use lean_coword::ident::LnIdent;
use lean_entity_path::theorem::LnTheoremPath;
use lean_opr::opr::binary::LnBinaryOpr;
use lean_term::instantiation::LnInstantiation;
use smallvec::SmallVec;

use crate::expr::{LnMirExprIdx, LnMirExprIdxRange};

#[derive(Debug, PartialEq, Eq)]
pub enum LnMirTacticData {
    Intro {},
    Obtain,
    Exact {
        term: LnMirExprIdx,
    },
    Cases,
    Rcases,
    Have {
        // TODO: pattern??
        ident: LnIdent,
        ty: Option<LnMirExprIdx>,
        construction: LnMirExprIdx,
    },
    Let {
        // TODO: pattern??
        ident: LnIdent,
        ty: Option<LnMirExprIdx>,
        construction: LnMirExprIdx,
    },
    Show {
        ty: LnMirExprIdx,
        tactics: LnMirTacticIdxRange,
    },
    Calc {
        leader: LnMirExprIdx,
        followers: SmallVec<[((LnBinaryOpr, LnInstantiation), LnMirExprIdx); 4]>,
    },
    Sorry,
    First {
        arms: LnMirTacticIdxRange,
    },
    Apply {
        hypothesis: LnMirExprIdx,
    },
    Obvious,
    Custom {
        name: &'static str,
        arguments: Option<LnMirExprIdxRange>,
        construction: Option<LnMirExprIdx>,
    },
    Assumption,
}

pub type LnMirTacticArena = Arena<LnMirTacticData>;
pub type LnMirTacticArenaRef<'a> = ArenaRef<'a, LnMirTacticData>;
pub type LnMirTacticIdx = ArenaIdx<LnMirTacticData>;
pub type LnMirTacticIdxRange = ArenaIdxRange<LnMirTacticData>;

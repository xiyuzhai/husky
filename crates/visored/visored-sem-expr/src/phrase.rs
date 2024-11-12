pub mod noun;

use crate::expr::VdSemExprIdx;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use noun::VdSemNounPhraseData;

pub enum VdSemPhrase {
    Expr(VdSemExprIdx),
}

pub enum VdSemPhraseData {
    Noun(VdSemNounPhraseData),
}

pub type VdSemPhraseArena = Arena<VdSemPhraseData>;
pub type VdSemPhraseMap<T> = ArenaMap<VdSemPhraseData, T>;
pub type VdSemPhraseArenaRef<'a> = ArenaRef<'a, VdSemPhraseData>;
pub type VdSemPhraseIdx = ArenaIdx<VdSemPhraseData>;
pub type VdSemPhraseIdxRange = ArenaIdxRange<VdSemPhraseData>;

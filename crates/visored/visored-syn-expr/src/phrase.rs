pub mod noun;

use crate::{expr::VdSynExprIdx, symbol::builder::VdSynSymbolBuilder};
use idx_arena::{
    map::ArenaMap, ordered_map::ArenaOrderedMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef,
};
use noun::VdSynNounPhraseData;

pub enum VdSynPhrase {
    Expr(VdSynExprIdx),
}

pub enum VdSynPhraseData {
    Noun(VdSynNounPhraseData),
}

pub type VdSynPhraseArena = Arena<VdSynPhraseData>;
pub type VdSynPhraseArenaRef<'a> = ArenaRef<'a, VdSynPhraseData>;
pub type VdSynPhraseIdx = ArenaIdx<VdSynPhraseData>;
pub type VdSynPhraseIdxRange = ArenaIdxRange<VdSynPhraseData>;
pub type VdSynPhraseMap<T> = ArenaMap<VdSynPhraseData, T>;
pub type VdSynPhraseOrderedMap<T> = ArenaOrderedMap<VdSynPhraseData, T>;

impl<'db> VdSynSymbolBuilder<'db> {
    pub(crate) fn build_phrase_aux(&mut self, phrase: VdSynPhraseIdx) {
        match self.phrase_arena()[phrase] {
            VdSynPhraseData::Noun(ref data) => todo!(),
        }
    }
}

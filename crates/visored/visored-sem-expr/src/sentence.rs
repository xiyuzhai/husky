use crate::{
    builder::VdSemExprBuilder,
    clause::{VdSemClauseData, VdSemClauseIdx, VdSemClauseIdxRange},
    ToVdSem,
};
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use latex_token::idx::LxRoseTokenIdx;
use visored_syn_expr::sentence::{
    VdSynSentenceData, VdSynSentenceEnd, VdSynSentenceIdx, VdSynSentenceIdxRange,
};

#[derive(Debug, PartialEq, Eq)]
pub enum VdSemSentenceData {
    Clauses {
        clauses: VdSemClauseIdxRange,
        end: VdSemSentenceEnd,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSemSentenceEnd {
    Period(LxRoseTokenIdx),
    Void,
}

pub type VdSemSentenceArena = Arena<VdSemSentenceData>;
pub type VdSemSentenceArenaRef<'a> = ArenaRef<'a, VdSemSentenceData>;
pub type VdSemSentenceIdx = ArenaIdx<VdSemSentenceData>;
pub type VdSemSentenceIdxRange = ArenaIdxRange<VdSemSentenceData>;
pub type VdSemSentenceMap<T> = ArenaMap<VdSemSentenceData, T>;

impl ToVdSem<VdSemSentenceIdxRange> for VdSynSentenceIdxRange {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemSentenceIdxRange {
        let mut sentences: Vec<VdSemSentenceData> = vec![];
        for sentence in self {
            sentences.push(builder.build_sentence(sentence));
        }
        builder.alloc_sentences(sentences)
    }
}

impl<'a> VdSemExprBuilder<'a> {
    fn build_sentence(&mut self, sentence: VdSynSentenceIdx) -> VdSemSentenceData {
        match self.syn_sentence_arena()[sentence] {
            VdSynSentenceData::Clauses { clauses, end } => VdSemSentenceData::Clauses {
                clauses: clauses.to_vd_sem(self),
                end: end.to_vd_sem(self),
            },
        }
    }
}

impl ToVdSem<VdSemSentenceEnd> for VdSynSentenceEnd {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemSentenceEnd {
        match self {
            VdSynSentenceEnd::Period(lx_rose_token_idx) => {
                VdSemSentenceEnd::Period(lx_rose_token_idx)
            }
            VdSynSentenceEnd::Void => VdSemSentenceEnd::Void,
        }
    }
}

pub enum VdSemSentenceChild {
    Clause(VdSemClauseIdx),
}

impl VdSemSentenceData {
    pub fn children(&self) -> Vec<VdSemSentenceChild> {
        match *self {
            VdSemSentenceData::Clauses { clauses, end } => clauses
                .into_iter()
                .map(|c| VdSemSentenceChild::Clause(c))
                .collect(),
        }
    }
}

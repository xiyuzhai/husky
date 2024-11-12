use std::iter::Peekable;

use crate::{
    builder::VdSynExprBuilder,
    clause::{VdSynClauseIdx, VdSynClauseIdxRange},
};
use husky_coword::Coword;
use idx_arena::{
    map::ArenaMap, ordered_map::ArenaOrderedMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef,
};
use latex_ast::ast::rose::{LxRoseAstData, LxRoseAstIdx};
use latex_rose_punctuation::LxRosePunctuation;
use latex_token::idx::LxRoseTokenIdx;

#[derive(Debug, PartialEq, Eq)]
pub enum VdSynSentenceData {
    Clauses {
        clauses: VdSynClauseIdxRange,
        end: VdSynSentenceEnd,
    },
}

pub enum VdSynSentenceChild {
    Clause(VdSynClauseIdx),
}

impl VdSynSentenceData {
    pub(crate) fn children(&self) -> Vec<VdSynSentenceChild> {
        match self {
            VdSynSentenceData::Clauses { clauses, .. } => clauses
                .into_iter()
                .map(VdSynSentenceChild::Clause)
                .collect(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSynSentenceEnd {
    Period(LxRoseTokenIdx),
}

pub type VdSynSentenceArena = Arena<VdSynSentenceData>;
pub type VdSynSentenceArenaRef<'a> = ArenaRef<'a, VdSynSentenceData>;
pub type VdSynSentenceIdx = ArenaIdx<VdSynSentenceData>;
pub type VdSynSentenceIdxRange = ArenaIdxRange<VdSynSentenceData>;
pub type VdSynSentenceMap<T> = ArenaMap<VdSynSentenceData, T>;
pub type VdSynSentenceOrderedMap<T> = ArenaOrderedMap<VdSynSentenceData, T>;

impl<'db> VdSynExprBuilder<'db> {
    pub(crate) fn parse_sentence(
        &mut self,
        token_idx: LxRoseTokenIdx,
        word: Coword,
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
    ) -> VdSynSentenceData {
        let clauses = vec![self.parse_clause(token_idx, word, asts)];
        let end = loop {
            if let Some(ast_idx) = asts.next() {
                match self.ast_arena()[ast_idx] {
                    LxRoseAstData::TextEdit { .. } => todo!(),
                    LxRoseAstData::Word(lx_rose_token_idx, coword) => todo!(),
                    LxRoseAstData::Punctuation(pucntuation_token_idx, punctuation) => {
                        match punctuation {
                            LxRosePunctuation::Comma => todo!(),
                            LxRosePunctuation::Period => {
                                break VdSynSentenceEnd::Period(pucntuation_token_idx)
                            }
                            LxRosePunctuation::Colon => todo!(),
                            LxRosePunctuation::Semicolon => todo!(),
                            LxRosePunctuation::Exclamation => todo!(),
                            LxRosePunctuation::Question => todo!(),
                        }
                    }
                    LxRoseAstData::Math {
                        left_dollar_token_idx,
                        math_asts,
                        right_dollar_token_idx,
                    } => todo!(),
                }
            } else {
                todo!()
            }
        };
        let clauses = self.alloc_clauses(clauses);
        VdSynSentenceData::Clauses { clauses, end }
    }
}

pub mod r#let;
#[cfg(test)]
mod tests;

use self::r#let::VdSemLetClauseDispatch;
use super::*;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use latex_token::idx::{LxMathTokenIdx, LxRoseTokenIdx};
use visored_syn_expr::clause::{VdSynClauseData, VdSynClauseIdx, VdSynClauseIdxRange};

#[derive(Debug, PartialEq, Eq)]
pub enum VdSemClauseData {
    Verb,
    Let {
        let_token_idx: LxRoseTokenIdx,
        left_dollar_token_idx: LxRoseTokenIdx,
        formula: VdSemExprIdx,
        right_dollar_token_idx: LxRoseTokenIdx,
        dispatch: VdSemLetClauseDispatch,
    },
    Assume {
        assume_token_idx: LxRoseTokenIdx,
        left_dollar_token_idx: LxRoseTokenIdx,
        formula: VdSemExprIdx,
        right_dollar_token_idx: LxRoseTokenIdx,
    },
    Then {
        then_token_idx: LxRoseTokenIdx,
        left_dollar_token_idx: LxRoseTokenIdx,
        formula: VdSemExprIdx,
        right_dollar_token_idx: LxRoseTokenIdx,
    },
}

pub type VdSemClauseArena = Arena<VdSemClauseData>;
pub type VdSemClauseArenaRef<'a> = ArenaRef<'a, VdSemClauseData>;
pub type VdSemClauseIdx = ArenaIdx<VdSemClauseData>;
pub type VdSemClauseIdxRange = ArenaIdxRange<VdSemClauseData>;
pub type VdSemClauseMap<T> = ArenaMap<VdSemClauseData, T>;

impl ToVdSem<VdSemClauseIdxRange> for VdSynClauseIdxRange {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemClauseIdxRange {
        let mut clauses: Vec<VdSemClauseData> = vec![];
        for clause in self {
            clauses.push(builder.build_clause(clause));
        }
        builder.alloc_clauses(clauses)
    }
}

impl<'a> VdSemExprBuilder<'a> {
    fn build_clause(&mut self, clause: VdSynClauseIdx) -> VdSemClauseData {
        match self.syn_clause_arena()[clause] {
            VdSynClauseData::Let {
                let_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
                ref resolution,
            } => self.build_let_clause(
                let_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
                resolution,
            ),
            VdSynClauseData::Assume {
                assume_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
            } => VdSemClauseData::Assume {
                assume_token_idx,
                left_dollar_token_idx,
                formula: formula.to_vd_sem(self),
                right_dollar_token_idx,
            },
            VdSynClauseData::Then {
                then_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
            } => VdSemClauseData::Then {
                then_token_idx,
                left_dollar_token_idx,
                formula: formula.to_vd_sem(self),
                right_dollar_token_idx,
            },
        }
    }
}

pub enum VdSemClauseChild {
    Expr(VdSemExprIdx),
}

impl VdSemClauseData {
    pub fn children(&self) -> Vec<VdSemClauseChild> {
        match *self {
            VdSemClauseData::Verb => todo!(),
            VdSemClauseData::Let {
                let_token_idx,
                left_dollar_token_idx,
                right_dollar_token_idx,
                formula,
                ..
            } => vec![VdSemClauseChild::Expr(formula)],
            VdSemClauseData::Assume {
                assume_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
            } => vec![VdSemClauseChild::Expr(formula)],
            VdSemClauseData::Then {
                then_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
            } => vec![VdSemClauseChild::Expr(formula)],
        }
    }
}

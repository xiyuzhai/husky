pub mod block;
#[cfg(test)]
mod tests;

use self::block::*;
use crate::{expr::VdMirExprIdx, pattern::VdMirPattern, *};
use idx_arena::{Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use visored_entity_path::module::VdModulePath;
use visored_prelude::division::VdDivisionLevel;
use visored_sem_expr::{
    clause::{
        r#let::{placeholder::VdSemLetClausePlaceholderTypeRepr, VdSemLetClauseDispatch},
        VdSemClauseData, VdSemClauseIdx, VdSemClauseIdxRange,
    },
    division::{VdSemDivisionData, VdSemDivisionIdx, VdSemDivisionIdxRange},
    sentence::{VdSemSentenceData, VdSemSentenceIdx, VdSemSentenceIdxRange},
    stmt::{VdSemStmtData, VdSemStmtIdx, VdSemStmtIdxRange},
};
use visored_term::ty::VdType;

#[derive(Debug, PartialEq, Eq)]
pub enum VdMirStmtData {
    Block {
        stmts: VdMirStmtIdxRange,
        meta: VdMirBlockMeta,
    },
    LetPlaceholder {
        pattern: VdMirPattern,
        ty: VdMirExprIdx,
    },
    LetAssigned {
        pattern: VdMirPattern,
        assignment: VdMirExprIdx,
    },
    Then {
        formula: VdMirExprIdx,
    },
}

pub type VdMirStmtArena = Arena<VdMirStmtData>;
pub type VdMirStmtArenaRef<'a> = ArenaRef<'a, VdMirStmtData>;
pub type VdMirStmtIdx = ArenaIdx<VdMirStmtData>;
pub type VdMirStmtIdxRange = ArenaIdxRange<VdMirStmtData>;

impl ToVdMir<VdMirStmtIdxRange> for VdSemDivisionIdxRange {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirStmtIdxRange {
        let data = self
            .into_iter()
            .map(|division| builder.build_stmt_from_sem_division(division))
            .collect::<Vec<_>>();
        builder.alloc_stmts(data)
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn build_stmt_from_sem_division(&mut self, division: VdSemDivisionIdx) -> VdMirStmtData {
        match *self.sem_division_arena()[division].data() {
            VdSemDivisionData::Stmts { stmts } => VdMirStmtData::Block {
                stmts: stmts.to_vd_mir(self),
                meta: VdMirBlockMeta::Division(
                    VdDivisionLevel::Stmts,
                    self.sem_division_arena()[division].module_path(),
                ),
            },
            // TODO: what to do for title?
            VdSemDivisionData::Divisions {
                command_token_idx,
                level,
                lcurl_token_idx,
                rcurl_token_idx,
                subdivisions,
            } => VdMirStmtData::Block {
                stmts: subdivisions.to_vd_mir(self),
                meta: VdMirBlockMeta::Division(
                    level,
                    self.sem_division_arena()[division].module_path(),
                ),
            },
        }
    }
}

impl ToVdMir<VdMirStmtIdxRange> for VdSemStmtIdxRange {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirStmtIdxRange {
        let data = self
            .into_iter()
            .map(|stmt| builder.build_stmt_from_sem_stmt(stmt))
            .collect::<Vec<_>>();
        builder.alloc_stmts(data)
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn build_stmt_from_sem_stmt(&mut self, stmt: VdSemStmtIdx) -> VdMirStmtData {
        match *self.sem_stmt_arena()[stmt].data() {
            VdSemStmtData::Paragraph(sentences) => VdMirStmtData::Block {
                stmts: sentences.to_vd_mir(self),
                meta: VdMirBlockMeta::Paragraph,
            },
            VdSemStmtData::Environment {
                environment_signature,
                stmts,
                begin_command_token_idx,
                end_rcurl_token_idx,
            } => VdMirStmtData::Block {
                stmts: stmts.to_vd_mir(self),
                meta: VdMirBlockMeta::Environment(
                    environment_signature.path(),
                    self.sem_stmt_arena()[stmt].module_path(),
                ),
            },
        }
    }
}

impl ToVdMir<VdMirStmtIdxRange> for VdSemSentenceIdxRange {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirStmtIdxRange {
        let data = self
            .into_iter()
            .map(|sentence| builder.build_stmt_from_sem_sentence(sentence))
            .collect::<Vec<_>>();
        builder.alloc_stmts(data)
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn build_stmt_from_sem_sentence(&mut self, sentence: VdSemSentenceIdx) -> VdMirStmtData {
        match self.sem_sentence_arena()[sentence] {
            VdSemSentenceData::Clauses { clauses, end } => VdMirStmtData::Block {
                stmts: clauses.to_vd_mir(self),
                meta: VdMirBlockMeta::Sentence,
            },
        }
    }
}

impl ToVdMir<VdMirStmtIdxRange> for VdSemClauseIdxRange {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirStmtIdxRange {
        let data = self
            .into_iter()
            .map(|clause| builder.build_stmt_from_sem_clause(clause))
            .collect::<Vec<_>>();
        builder.alloc_stmts(data)
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn build_stmt_from_sem_clause(&mut self, clause: VdSemClauseIdx) -> VdMirStmtData {
        match self.sem_clause_arena()[clause] {
            VdSemClauseData::Verb => todo!(),
            VdSemClauseData::Let {
                let_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
                ref dispatch,
            } => match dispatch {
                VdSemLetClauseDispatch::Assigned(dispatch) => todo!(),
                VdSemLetClauseDispatch::Placeholder(dispatch) => VdMirStmtData::LetPlaceholder {
                    pattern: dispatch.pattern().to_vd_mir(self),
                    ty: match *dispatch.ty_repr() {
                        VdSemLetClausePlaceholderTypeRepr::Expr(ty_expr) => ty_expr.to_vd_mir(self),
                    },
                },
            },
            VdSemClauseData::Assume {
                assume_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
            } => VdMirStmtData::LetPlaceholder {
                pattern: VdMirPattern::Assumed,
                ty: formula.to_vd_mir(self),
            },
            VdSemClauseData::Then {
                then_token_idx,
                left_dollar_token_idx,
                formula,
                right_dollar_token_idx,
            } => VdMirStmtData::Then {
                formula: formula.to_vd_mir(self),
            },
            VdSemClauseData::Todo(lx_rose_token_idx) => todo!(),
        }
    }
}

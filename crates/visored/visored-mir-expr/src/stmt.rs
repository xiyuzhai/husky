//! Note the difference of the concept of `stmt` in visored compared with those in provers like Lean, Rocq, Isabelle.
//!
//! Things like `have` and `show` are tactics in traditional provers, but are statements in visored.
//!
//! This is actually more similar to those in natural languages.
pub mod block;
#[cfg(test)]
mod tests;

use self::block::*;
use crate::{expr::VdMirExprIdx, pattern::VdMirPattern, *};
use hint::{VdMirHintData, VdMirHintEntry, VdMirHintIdx, VdMirHintIdxRange, VdMirHintSource};
use hypothesis::{contradiction::VdMirHypothesisResult, VdMirHypothesisIdx};
use idx_arena::{
    map::ArenaMap, ordered_map::ArenaOrderedMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef,
};
use once_place::OncePlace;
use visored_entity_path::module::VdModulePath;
use visored_global_resolution::resolution::environment::VdEnvironmentGlobalResolution;
use visored_prelude::division::VdDivisionLevel;
use visored_sem_expr::{
    block::{VdSemBlockData, VdSemBlockIdx, VdSemBlockIdxRange},
    clause::{
        r#let::{placeholder::VdSemLetClausePlaceholderTypeRepr, VdSemLetClauseDispatch},
        VdSemClauseData, VdSemClauseIdx, VdSemClauseIdxRange,
    },
    division::{VdSemDivisionData, VdSemDivisionIdx, VdSemDivisionIdxRange},
    sentence::{VdSemSentenceData, VdSemSentenceIdx, VdSemSentenceIdxRange},
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
    Assume {
        prop: VdMirExprIdx,
        hypothesis_place: OncePlace<VdMirHypothesisResult>,
    },
    LetAssigned {
        pattern: VdMirPattern,
        assignment: VdMirExprIdx,
    },
    Goal {
        prop: VdMirExprIdx,
    },
    Have {
        prop: VdMirExprIdx,
        hint: Option<VdMirHintIdx>,
        hypothesis_place: OncePlace<VdMirHypothesisResult>,
    },
    Show {
        prop: VdMirExprIdx,
        hint: Option<VdMirHintIdx>,
    },
    Qed {
        goal_and_hypothesis_place: Option<(VdMirExprIdx, OncePlace<VdMirHypothesisResult>)>,
    },
}

#[derive(Debug)]
pub struct VdMirStmtEntry {
    data: VdMirStmtData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VdMirStmtSource {
    Stmt(VdSemBlockIdx),
    Division(VdSemDivisionIdx),
    Sentence(VdSemSentenceIdx),
    Clause(VdSemClauseIdx),
    Qed(VdSemSentenceIdxRange),
}

pub type VdMirStmtArena = Arena<VdMirStmtEntry>;
pub type VdMirStmtOrderedMap<T> = ArenaOrderedMap<VdMirStmtEntry, T>;
pub type VdMirStmtMap<T> = ArenaMap<VdMirStmtEntry, T>;
pub type VdMirStmtArenaRef<'a> = ArenaRef<'a, VdMirStmtEntry>;
pub type VdMirStmtIdx = ArenaIdx<VdMirStmtEntry>;
pub type VdMirStmtIdxRange = ArenaIdxRange<VdMirStmtEntry>;

impl VdMirStmtEntry {
    pub fn new(data: VdMirStmtData) -> Self {
        Self { data }
    }

    pub fn new_qed(goal: Option<VdMirExprIdx>) -> Self {
        Self::new(VdMirStmtData::Qed {
            goal_and_hypothesis_place: goal.map(|goal| (goal, OncePlace::default())),
        })
    }
}

impl VdMirStmtEntry {
    pub fn data(&self) -> &VdMirStmtData {
        &self.data
    }

    pub(crate) fn data_mut(&mut self) -> &mut VdMirStmtData {
        &mut self.data
    }
}

impl ToVdMir<VdMirStmtIdxRange> for VdSemDivisionIdxRange {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirStmtIdxRange {
        let entries = self
            .into_iter()
            .map(|division| VdMirStmtEntry::new(builder.build_stmt_from_sem_division(division)))
            .collect::<Vec<_>>();
        let sources = self.into_iter().map(VdMirStmtSource::Division);
        builder.alloc_stmts(entries, sources)
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

impl ToVdMir<VdMirStmtIdxRange> for VdSemBlockIdxRange {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirStmtIdxRange {
        let entries = self
            .into_iter()
            .map(|stmt| VdMirStmtEntry::new(builder.build_mir_stmt_from_block(stmt)))
            .collect::<Vec<_>>();
        let sources = self.into_iter().map(VdMirStmtSource::Stmt);
        builder.alloc_stmts(entries, sources)
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn build_mir_stmt_from_block(&mut self, block: VdSemBlockIdx) -> VdMirStmtData {
        match *self.sem_block_arena()[block].data() {
            VdSemBlockData::Paragraph(sentences) => VdMirStmtData::Block {
                stmts: (sentences, None).to_vd_mir(self),
                meta: VdMirBlockMeta::Paragraph,
            },
            VdSemBlockData::Environment {
                environment_signature,
                resolution,
                stmts,
                begin_command_token_idx,
                end_rcurl_token_idx,
            } => VdMirStmtData::Block {
                stmts: stmts.to_vd_mir(self),
                meta: VdMirBlockMeta::Environment(
                    environment_signature.path(),
                    match resolution {
                        VdEnvironmentGlobalResolution::Environment(vd_environment_path) => {
                            vd_environment_path
                        }
                    },
                    self.sem_block_arena()[block].module_path(),
                ),
            },
        }
    }
}

impl ToVdMir<VdMirStmtIdxRange> for (VdSemSentenceIdxRange, Option<VdMirExprIdx>) {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirStmtIdxRange {
        let (sentences, mut ext_goal) = self;
        let mut entries = sentences
            .into_iter()
            .map(|sentence| VdMirStmtEntry::new(builder.build_stmt_from_sem_sentence(sentence)))
            .collect::<Vec<_>>();
        let goal = builder.collect_goal(ext_goal, &entries);
        entries.push(VdMirStmtEntry::new_qed(goal));
        let sources = sentences
            .into_iter()
            .map(VdMirStmtSource::Sentence)
            .chain([VdMirStmtSource::Qed(sentences)]);
        builder.alloc_stmts(entries, sources)
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn collect_goal(
        &self,
        ext_goal: Option<VdMirExprIdx>,
        entries: &[VdMirStmtEntry],
    ) -> Option<VdMirExprIdx> {
        let mut goal = ext_goal;
        for entry in entries {
            self.collect_goal_aux(entry, &mut goal);
        }
        goal
    }

    fn collect_goal_aux(&self, entry: &VdMirStmtEntry, goal: &mut Option<VdMirExprIdx>) {
        match *entry.data() {
            VdMirStmtData::Goal { prop } => {
                if goal.is_some() {
                    todo!();
                }
                *goal = Some(prop)
            }
            VdMirStmtData::Block { stmts, ref meta } => {
                for stmt in stmts {
                    self.collect_goal_aux(&self.stmt_arena()[stmt], goal);
                }
            }
            _ => {}
        }
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn build_stmt_from_sem_sentence(&mut self, sentence: VdSemSentenceIdx) -> VdMirStmtData {
        match self.sem_sentence_arena()[sentence] {
            VdSemSentenceData::Clauses { clauses, end } => VdMirStmtData::Block {
                stmts: clauses.to_vd_mir(self),
                meta: VdMirBlockMeta::Sentence,
            },
            VdSemSentenceData::Have => todo!(),
            VdSemSentenceData::Show => todo!(),
        }
    }
}

impl ToVdMir<VdMirStmtIdxRange> for VdSemClauseIdxRange {
    fn to_vd_mir(self, builder: &mut VdMirExprBuilder) -> VdMirStmtIdxRange {
        let entries = self
            .into_iter()
            .map(|clause| VdMirStmtEntry::new(builder.build_stmt_from_sem_clause(clause)))
            .collect::<Vec<_>>();
        let sources = self.into_iter().map(VdMirStmtSource::Clause);
        builder.alloc_stmts(entries, sources)
    }
}

impl<'db> VdMirExprBuilder<'db> {
    fn build_stmt_from_sem_clause(&mut self, clause: VdSemClauseIdx) -> VdMirStmtData {
        match *self.sem_clause_arena()[clause].data() {
            VdSemClauseData::Verb => todo!(),
            VdSemClauseData::Let {
                left_math_delimiter_token_idx: left_dollar_token_idx,
                formula,
                right_math_delimiter_token_idx: right_dollar_token_idx,
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
                left_math_delimiter_token_idx: left_dollar_token_idx,
                formula,
                right_math_delimiter_token_idx: right_dollar_token_idx,
            } => VdMirStmtData::Assume {
                prop: formula.to_vd_mir(self),
                hypothesis_place: OncePlace::default(),
            },
            VdSemClauseData::Goal {
                left_math_delimiter_token_idx: left_dollar_token_idx,
                formula,
                right_math_delimiter_token_idx: right_dollar_token_idx,
            } => VdMirStmtData::Goal {
                prop: formula.to_vd_mir(self),
            },
            VdSemClauseData::Have {
                left_math_delimiter_token_idx: left_dollar_token_idx,
                formula,
                right_math_delimiter_token_idx: right_dollar_token_idx,
            } => VdMirStmtData::Have {
                prop: formula.to_vd_mir(self),
                hint: None, // ad hoc
                hypothesis_place: OncePlace::default(),
            },
            VdSemClauseData::Show {
                left_math_delimiter_token_idx: left_dollar_token_idx,
                formula,
                right_math_delimiter_token_idx: right_dollar_token_idx,
            } => VdMirStmtData::Show {
                prop: formula.to_vd_mir(self),
                hint: None, // ad hoc
            },
            VdSemClauseData::Todo(lx_rose_token_idx) => todo!(),
        }
    }
}

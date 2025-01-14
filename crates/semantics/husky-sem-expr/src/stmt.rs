pub mod condition;
pub mod if_else_stmt;
mod let_stmt;
pub mod loop_stmt;
pub mod match_stmt;

use self::condition::*;
use self::if_else_stmt::*;
use self::loop_stmt::*;
use self::match_stmt::*;

use husky_regional_token::{
    AssertRegionalToken, BreakRegionalToken, DoRegionalToken, EolRegionalToken,
    EolSemicolonRegionalToken, EolWithRegionalToken, EqRegionalToken, ForextRegionalToken,
    LetRegionalToken, MatchRegionalToken, RequireRegionalToken, ReturnRegionalToken,
    StmtForRegionalToken, WhileRegionalToken,
};
use husky_token_data::TokenDataResult;
use idx_arena::{map::ArenaMap, Arena, ArenaIdx, ArenaIdxRange, ArenaRef};
use vec_like::VecPairMap;

use crate::{obelisks::let_variable::LetVariableObelisk, *};

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum SemStmtData {
    Let {
        let_token: LetRegionalToken,
        let_pattern_sem_obelisk: LetVariableObelisk,
        contract: Contract,
        eq_token: EqRegionalToken,
        initial_value: SemExprIdx,
        coercion_outcome: Option<ExpectCoercionOutcome>,
    },
    Return {
        return_token: ReturnRegionalToken,
        result: SemExprIdx,
        coercion_outcome: Option<ExpectCoercionOutcome>,
    },
    Require {
        require_token: RequireRegionalToken,
        condition: SemCondition,
    },
    Assert {
        assert_token: AssertRegionalToken,
        condition: SemCondition,
    },
    Break {
        break_token: BreakRegionalToken,
    },
    Eval {
        expr: SemExprIdx,
        outcome: Option<ExpectationOutcome>,
        // todo: change this to EolOrEolSemicolonToken
        eol_semicolon: Option<EolSemicolonRegionalToken>,
    },
    ForBetween {
        for_token: StmtForRegionalToken,
        particulars: SemForBetweenParticulars,
        for_loop_varible_idx: CurrentVariableIdx,
        eol_colon: EolRegionalToken,
        stmts: SemStmtIdxRange,
    },
    ForIn {
        for_token: StmtForRegionalToken,
        range: SemExprIdx,
        eol_colon: EolRegionalToken,
        stmts: SemStmtIdxRange,
    },
    Forext {
        forext_token: ForextRegionalToken,
        particulars: SemaForextParticulars,
        eol_colon: EolRegionalToken,
        stmts: SemStmtIdxRange,
    },
    While {
        while_token: WhileRegionalToken,
        condition: SemCondition,
        eol_colon: EolRegionalToken,
        stmts: SemStmtIdxRange,
    },
    DoWhile {
        do_token: DoRegionalToken,
        while_token: WhileRegionalToken,
        condition: SemCondition,
        eol_colon: EolRegionalToken,
        stmts: SemStmtIdxRange,
    },
    IfElse {
        if_branch: SemIfBranch,
        elif_branches: Vec<SemElifBranch>,
        else_branch: Option<SemElseBranch>,
    },
    Match {
        match_token: MatchRegionalToken,
        opd: SemExprIdx,
        contract: Contract,
        eol_with_token: EolWithRegionalToken,
        case_branches: Vec<SemCaseBranch>,
    },
    Narrate {
        narrate_token: husky_regional_token::NarrateRegionalToken,
    },
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct SemStmtEntry {
    data_result: SemExprDataResult<SemStmtData>,
    ty_result: SemExprTypeResult<FlyTerm>,
}

impl SemStmtEntry {
    pub fn data_result(&self) -> SemExprDataResultRef<&SemStmtData> {
        self.data_result.as_ref()
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Default)]
pub(crate) struct SemStmtBatch {
    entries: SmallVec<[SemStmtEntry; 8]>,
}

impl SemStmtBatch {
    pub(crate) fn add(
        &mut self,
        (data_result, ty_result): (SemExprDataResult<SemStmtData>, SemExprTypeResult<FlyTerm>),
    ) {
        self.entries.push(SemStmtEntry {
            data_result,
            ty_result,
        })
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Default, PartialEq, Eq)]
pub struct SemStmtArena(Arena<SemStmtEntry>);

impl SemStmtArena {
    pub(crate) fn alloc_many(&mut self, batch: SemStmtBatch) -> SemStmtIdxRange {
        SemStmtIdxRange(self.0.alloc_many(batch.entries))
    }

    pub fn arena_ref<'a>(&'a self) -> SemStmtArenaRef<'a> {
        SemStmtArenaRef(self.0.as_arena_ref())
    }
}

#[derive(Clone, Copy)]
pub struct SemStmtArenaRef<'a>(ArenaRef<'a, SemStmtEntry>);

impl<'a> SemStmtArenaRef<'a> {
    pub fn len(self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn indexed_iter(self) -> impl Iterator<Item = (SemStmtIdx, &'a SemStmtEntry)> {
        self.0
            .indexed_iter()
            .map(|(idx, entry)| (SemStmtIdx(idx), entry))
    }

    #[inline]
    pub fn iter(self) -> impl Iterator<Item = &'a SemStmtEntry> + 'a {
        self.0.iter()
    }
}

impl<'a> std::ops::Index<SemStmtIdx> for SemStmtArenaRef<'a> {
    type Output = SemStmtEntry;

    fn index(&self, index: SemStmtIdx) -> &Self::Output {
        &self.0[index.0]
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SemStmtIdx(ArenaIdx<SemStmtEntry>);

impl SemStmtIdx {
    pub fn data<'a>(self, arena_ref: SemStmtArenaRef<'a>) -> &'a SemStmtData {
        arena_ref
            .0
            .index(self.0)
            .data_result
            .as_ref()
            .expect("no error")
    }

    pub fn index(self) -> usize {
        self.0.index()
    }
}

impl std::ops::Sub<usize> for SemStmtIdx {
    type Output = SemStmtIdx;

    fn sub(self, rhs: usize) -> Self::Output {
        SemStmtIdx(self.0 - rhs)
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SemStmtIdxRange(ArenaIdxRange<SemStmtEntry>);

impl SemStmtIdxRange {
    pub fn iter(self) -> impl Iterator<Item = SemStmtIdx> {
        self.0.into_iter().map(SemStmtIdx)
    }

    pub fn start(self) -> SemStmtIdx {
        SemStmtIdx(self.0.start())
    }

    pub fn end(self) -> SemStmtIdx {
        SemStmtIdx(self.0.end())
    }

    pub fn last(self) -> Option<SemStmtIdx> {
        let last = self.0.last()?;
        Some(SemStmtIdx(last))
    }

    pub fn split_last(self) -> (Self, SemStmtIdx) {
        let (range, last) = self.0.split_last_unwrap();
        (Self(range), SemStmtIdx(last))
    }
}

impl IntoIterator for SemStmtIdxRange {
    type Item = SemStmtIdx;

    type IntoIter = std::iter::Map<
        <ArenaIdxRange<stmt::SemStmtEntry> as IntoIterator>::IntoIter,
        fn(ArenaIdx<SemStmtEntry>) -> SemStmtIdx,
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(SemStmtIdx)
    }
}

impl IntoIterator for &SemStmtIdxRange {
    type Item = SemStmtIdx;

    type IntoIter = std::iter::Map<
        <ArenaIdxRange<stmt::SemStmtEntry> as IntoIterator>::IntoIter,
        fn(ArenaIdx<SemStmtEntry>) -> SemStmtIdx,
    >;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter().map(SemStmtIdx)
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct SemStmtMap<V>(ArenaMap<SemStmtEntry, V>);

pub type SemStmtsMap<V> = VecPairMap<SemStmtIdxRange, V>;

impl<V> SemStmtMap<V> {
    pub fn new(sem_stmt_arena: SemStmtArenaRef<'_>) -> SemStmtMap<V> {
        Self(ArenaMap::new2(sem_stmt_arena.0))
    }

    pub fn insert(&mut self, stmt: SemStmtIdx, v: V) -> Option<V> {
        self.0.insert(stmt.0, v)
    }

    pub fn insert_new(&mut self, stmt: SemStmtIdx, v: V) {
        self.0.insert_new(stmt.0, v)
    }

    pub fn insert_new_or_merge(&mut self, stmt: SemStmtIdx, v: V, f: impl FnOnce(&mut V, V)) {
        self.0.insert_new_or_merge(stmt.0, v, f)
    }

    pub fn get(&self, stmt: SemStmtIdx) -> Option<&V> {
        self.0.get(stmt.0)
    }

    pub fn get_stmt_by_value_copied(&self, v: V) -> Option<SemStmtIdx>
    where
        V: PartialEq + Copy,
    {
        self.0.get_idx_by_value(&v).map(SemStmtIdx)
    }

    pub fn map<R>(&self, f: impl Fn(&V) -> R) -> SemStmtMap<R> {
        SemStmtMap(self.0.map(f))
    }
}

impl<V> std::ops::Index<SemStmtIdx> for SemStmtMap<V> {
    type Output = V;

    fn index(&self, index: SemStmtIdx) -> &Self::Output {
        &self.0[index.0]
    }
}

impl<'a, V> IntoIterator for &'a SemStmtMap<V> {
    type Item = (SemStmtIdx, &'a V);

    type IntoIter = impl Iterator<Item = Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|(idx, v)| (SemStmtIdx(idx), v))
    }
}

impl<'a> SemExprBuilder<'a> {
    pub(crate) fn build_sem_branch<Expectation: ExpectFlyTerm>(
        &mut self,
        stmts: SynStmtIdxRange,
        merger: &mut BranchTypeMerger<Expectation>,
    ) -> SemStmtIdxRange {
        let (stmts, stmts_ty) =
            self.build_sem_stmts_with_its_ty_returned(stmts, merger.expr_expectation().clone());
        merger.add(self, stmts_ty);
        stmts
    }

    pub(crate) fn build_sem_stmts(
        &mut self,
        stmts: SynStmtIdxRange,
        block_ty_expectation: impl ExpectFlyTerm,
    ) -> SemStmtIdxRange {
        let mut batch = SemStmtBatch::default();
        for stmt in stmts.start()..(stmts.end() - 1) {
            batch.add(self.infer_new_nonlast_stmt(stmt));
        }
        batch.add(self.build_sem_stmt(stmts.end() - 1, block_ty_expectation));
        self.alloc_stmt_batch(batch)
    }

    pub(crate) fn build_sem_stmts_with_its_ty_returned(
        &mut self,
        stmts: SynStmtIdxRange,
        block_ty_expectation: impl ExpectFlyTerm,
    ) -> (SemStmtIdxRange, Option<FlyTerm>) {
        let mut batch = SemStmtBatch::default();
        for stmt in stmts.start()..(stmts.end() - 1) {
            batch.add(self.infer_new_nonlast_stmt(stmt));
        }
        let (data_result, ty_result) = self.build_sem_stmt(stmts.end() - 1, block_ty_expectation);
        let ty = ty_result.as_ref().ok().copied();
        batch.add((data_result, ty_result));
        (self.alloc_stmt_batch(batch), ty)
    }

    fn infer_new_nonlast_stmt(
        &mut self,
        stmt_idx: SynStmtIdx,
    ) -> (SemExprDataResult<SemStmtData>, SemExprTypeResult<FlyTerm>) {
        let expect_unit = self.expect_unit();
        self.build_sem_stmt(stmt_idx, expect_unit)
    }

    fn build_sem_stmt(
        &mut self,
        stmt_idx: SynStmtIdx,
        stmt_ty_expectation: impl ExpectFlyTerm,
    ) -> (SemExprDataResult<SemStmtData>, SemExprTypeResult<FlyTerm>) {
        match self.syn_expr_region_data()[stmt_idx] {
            SynStmtData::Let {
                let_token,
                ref let_variables_pattern,
                ref assign_token,
                initial_value,
            } => self.build_let_stmt(
                let_token,
                let_variables_pattern,
                assign_token,
                initial_value,
            ),
            SynStmtData::Return {
                return_token,
                result,
            } => {
                let (result, coercion_outcome) = match self.return_ty() {
                    Some(return_ty) => self.build_expr_with_outcome(
                        result,
                        ExpectCoercion::new_move(return_ty.into()),
                    ),
                    None => (self.build_expr(result, ExpectAnyDerived), None),
                };
                (
                    Ok(SemStmtData::Return {
                        return_token,
                        result,
                        coercion_outcome,
                    }),
                    Ok(self.term_menu().never().into()),
                )
            }
            SynStmtData::Require {
                require_token,
                condition,
            } => {
                let condition = self.build_sem_condition(condition);
                (
                    Ok(SemStmtData::Require {
                        require_token,
                        condition,
                    }),
                    Ok(self.term_menu().unit_ty_ontology().into()),
                )
            }
            SynStmtData::Assert {
                assert_token,
                condition,
            } => {
                let condition = self.build_sem_condition(condition);
                (
                    Ok(SemStmtData::Assert {
                        assert_token,
                        condition,
                    }),
                    Ok(self.term_menu().unit_ty_ontology().into()),
                )
            }
            SynStmtData::Break { break_token } => (
                Ok(SemStmtData::Break { break_token }),
                Ok(self.term_menu().never().into()),
            ),
            SynStmtData::Eval {
                expr_idx,
                eol_semicolon,
            } => match eol_semicolon {
                Ok(eol_semicolon) => {
                    let (expr, ty, outcome) = match eol_semicolon {
                        None => match stmt_ty_expectation.destination() {
                            FlyTermDestination::AnyOriginal | FlyTermDestination::AnyDerived => {
                                self.build_expr_with_ty_and_outcome2(expr_idx, stmt_ty_expectation)
                            }
                            FlyTermDestination::Specific(stmt_ty) => {
                                let (expr, outcome) =
                                    self.build_expr_with_outcome(expr_idx, stmt_ty_expectation);
                                // we don't use type of expression here because of possible coersion
                                (expr, Some(stmt_ty), outcome.map(Into::into))
                            }
                        },
                        Some(_) => {
                            let (sem_expr_idx, expr_ty, outcome) =
                                self.build_expr_with_ty_and_outcome2(expr_idx, ExpectAnyOriginal);
                            let ty_result = match expr_ty {
                                Some(ty) => match ty.base_resolved(self) {
                                    FlyTermBase::Eth(ty) if ty == self.term_menu().never() => {
                                        Some(self.term_menu().never().into())
                                    }
                                    _ => Some(self.term_menu().unit_ty_ontology().into()),
                                },
                                None => None,
                            };
                            (sem_expr_idx, ty_result, outcome)
                        }
                    };
                    (
                        Ok(SemStmtData::Eval {
                            expr,
                            eol_semicolon,
                            outcome,
                        }),
                        ty.ok_or(DerivedSemExprTypeError::EvalExprTypeNotInferred.into()),
                    )
                }
                Err(_) => {
                    let _ = self.build_expr_with_ty_and_outcome(expr_idx, ExpectAnyDerived);
                    todo!()
                }
            },
            SynStmtData::ForBetween {
                for_token,
                ref particulars,
                for_loop_varible_idx,
                ref block,
                ref eol_colon,
            } => {
                let expr_expectation = self.expect_unit();
                let Ok(particulars) =
                    self.build_sem_for_between_particulars(particulars, for_loop_varible_idx)
                else {
                    todo!()
                };
                let block = self.build_sem_stmts(*block, expr_expectation);
                let &Ok(eol_colon) = eol_colon else { todo!() };
                (
                    Ok(SemStmtData::ForBetween {
                        for_token,
                        particulars,
                        for_loop_varible_idx,
                        eol_colon,
                        stmts: block,
                    }),
                    Ok(self.term_menu().unit_ty_ontology().into()),
                )
            }
            SynStmtData::ForIn {
                ref condition,
                block,
                ..
            } => todo!(),
            SynStmtData::ForExt {
                forext_token,
                ref particulars,
                block,
                ref eol_colon,
            } => {
                let (forext_loop_var_sem_expr_idx, forext_loop_var_ty) = self
                    .build_expr_with_ty(particulars.forext_loop_var_expr_idx, ExpectAnyOriginal);
                let Some(forext_loop_var_ty) = forext_loop_var_ty else {
                    todo!()
                };
                let particulars = self.build_sem_forext_particulars(
                    particulars,
                    forext_loop_var_sem_expr_idx,
                    forext_loop_var_ty,
                );
                let block_ty_expectation = self.expect_unit();
                let block = self.build_sem_stmts(block, block_ty_expectation);
                let &Ok(eol_colon) = eol_colon else { todo!() };
                (
                    Ok(SemStmtData::Forext {
                        forext_token,
                        particulars,
                        eol_colon,
                        stmts: block,
                    }),
                    Ok(self.term_menu().unit_ty_ontology().into()),
                )
            }
            SynStmtData::While {
                while_token,
                ref condition,
                block,
                ref eol_colon,
            } => {
                let condition = match condition {
                    Ok(condition) => self.build_sem_condition(*condition),
                    Err(_) => todo!(),
                };
                let &Ok(eol_colon) = eol_colon else { todo!() };
                let expect_unit = self.expect_unit();
                let block = self.build_sem_stmts(block, expect_unit);
                (
                    Ok(SemStmtData::While {
                        while_token,
                        condition,
                        eol_colon,
                        stmts: block,
                    }),
                    Ok(self.term_menu().unit_ty_ontology().into()),
                )
            }
            SynStmtData::DoWhile {
                do_token,
                while_token,
                ref condition,
                block,
                ref eol_colon,
            } => {
                let condition = match condition {
                    Ok(condition) => self.build_sem_condition(*condition),
                    Err(_) => todo!(),
                };
                let &Ok(eol_colon) = eol_colon else { todo!() };
                let expect_unit = self.expect_unit();
                let block = self.build_sem_stmts(block, expect_unit);
                (
                    Ok(SemStmtData::DoWhile {
                        do_token,
                        while_token,
                        condition,
                        eol_colon,
                        stmts: block,
                    }),
                    Ok(self.term_menu().unit_ty_ontology().into()),
                )
            }
            SynStmtData::IfElse {
                ref if_branch,
                ref elif_branches,
                ref else_branch,
            } => self.build_if_else_stmt(
                if_branch,
                elif_branches,
                else_branch.as_ref(),
                stmt_ty_expectation,
            ),
            SynStmtData::Match {
                match_token,
                ref match_expr,
                ref eol_with_token,
                ref case_branches,
            } => self.build_match_stmt(
                match_token,
                match_expr,
                eol_with_token,
                case_branches,
                stmt_ty_expectation,
            ),
            SynStmtData::Narrate { narrate_token } => (
                Ok(SemStmtData::Narrate { narrate_token }),
                Ok(self.term_menu().unit_ty_ontology().into()),
            ),
        }
    }

    pub(crate) fn build_sem_condition(&mut self, expr: SynExprIdx) -> SemCondition {
        let (expr, outcome) = self.build_expr_with_outcome(expr, ExpectConditionType);
        match *expr.data(self.sem_expr_arena().arena_ref()) {
            SemExprData::Be {
                src,
                contract,
                be_regional_token_idx,
                target,
            } => SemCondition::Be {
                expr,
                src,
                contract,
                be_regional_token_idx,
                target,
            },
            _ => SemCondition::Other {
                expr,
                conversion: match outcome {
                    Some(ExpectConditionTypeOutcome { conversion }) => conversion,
                    None => todo!(),
                },
            },
        }
    }
}

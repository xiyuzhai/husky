use super::*;
use crate::term::{num::VdBsqNumTerm, prop::VdBsqPropTerm, VdBsqTerm};
use crate::{hypothesis::stashes::VdBsqHypothesisStashes, term::litnum::VdBsqLitnumTerm};
use floated_sequential::db::FloaterDb;
use rustc_hash::FxHashMap;

/// A stack of baseq hypotheses.
///
/// This structure maintains a stack of hypotheses and maps that associate expressions and terms
/// with hypothesis records. The maps may contain outdated information, so all lookups are validated
/// against the current state of the hypothesis stack.
///
/// # Implementation Strategy
/// The maps are intentionally allowed to contain outdated entries as an optimization technique.
/// When hypotheses are removed from the stack (via rollback), we avoid the cost of updating
/// the maps immediately. Instead, we keep the stale entries and validate them at lookup time.
/// This trades slightly slower lookups for much faster rollback operations, which is beneficial
/// when the stack is frequently rolled back.
///
/// # Maps and Validation
/// - `expr_to_hypothesis`: Maps expressions to hypothesis records, but entries may be stale
/// - `term_to_hypothesis`: Maps terms to hypothesis records, but entries may be stale
///
/// Both maps are validated during lookups by checking if the recorded hypothesis still exists
/// at the expected position in the stack. This ensures we only return valid, "live" hypotheses.
pub struct VdBsqHypothesisStack<'sess> {
    active_hypotheses: VdBsqActiveHypotheses<'sess>,
    block_starts: Vec<usize>,
    expr_to_hypothesis_map: FxHashMap<VdBsqExpr<'sess>, VdBsqHypothesisStackRecord<'sess>>,
    term_to_hypothesis_map: FxHashMap<VdBsqTerm<'sess>, VdBsqHypothesisStackRecord<'sess>>,
    stashes: VdBsqHypothesisStashes<'sess>,
}

pub struct VdBsqActiveHypotheses<'sess>(Vec<VdBsqHypothesisIdx<'sess>>);

impl<'sess> VdBsqActiveHypotheses<'sess> {
    fn new() -> Self {
        Self(vec![])
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn data(&self) -> &[VdBsqHypothesisIdx<'sess>] {
        &self.0
    }

    pub fn is_record_active(&self, record: VdBsqHypothesisStackRecord<'sess>) -> bool {
        self.0.get(record.stack_idx) == Some(&record.hypothesis_idx)
    }

    fn push(&mut self, hypothesis_idx: VdBsqHypothesisIdx<'sess>) {
        self.0.push(hypothesis_idx);
    }

    fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VdBsqHypothesisStackRecord<'sess> {
    stack_idx: usize,
    hypothesis_idx: VdBsqHypothesisIdx<'sess>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct VdBsqHypothesisStackRecorded<'sess, T> {
    record: VdBsqHypothesisStackRecord<'sess>,
    value: T,
}

impl<'sess, T> VdBsqHypothesisStackRecorded<'sess, T> {
    pub fn new(record: VdBsqHypothesisStackRecord<'sess>, value: T) -> Self {
        Self { record, value }
    }
}

impl<'sess, T> VdBsqHypothesisStackRecorded<'sess, T> {
    pub fn get_valid_value(&self, active_hypotheses: &VdBsqActiveHypotheses<'sess>) -> Option<&T> {
        active_hypotheses
            .is_record_active(self.record)
            .then_some(&self.value)
    }
}

impl<'sess> VdBsqHypothesisStack<'sess> {
    pub(super) fn new() -> Self {
        Self {
            active_hypotheses: VdBsqActiveHypotheses::new(),
            block_starts: vec![],
            expr_to_hypothesis_map: FxHashMap::default(),
            term_to_hypothesis_map: FxHashMap::default(),
            stashes: VdBsqHypothesisStashes::new(),
        }
    }
}

impl<'sess> VdBsqHypothesisStack<'sess> {
    pub fn len(&self) -> usize {
        self.active_hypotheses.len()
    }

    pub fn active_hypotheses(&self) -> &VdBsqActiveHypotheses<'sess> {
        &self.active_hypotheses
    }

    pub fn stashes(&self) -> &VdBsqHypothesisStashes<'sess> {
        &self.stashes
    }

    pub(crate) fn get_active_hypothesis_with_expr(
        &self,
        expr: VdBsqExpr<'sess>,
    ) -> Option<VdBsqHypothesisIdx<'sess>> {
        let record = self.expr_to_hypothesis_map.get(&expr).copied()?;
        self.is_record_valid(record)
            .then_some(record.hypothesis_idx)
    }

    #[track_caller]
    pub(crate) fn get_active_hypothesis_with_nontrivial_term(
        &self,
        term: VdBsqTerm<'sess>,
    ) -> Option<VdBsqHypothesisIdx<'sess>> {
        assert!(term.is_nontrivial());
        let record = self.term_to_hypothesis_map.get(&term).copied()?;
        self.is_record_valid(record)
            .then_some(record.hypothesis_idx)
    }

    fn is_record_valid(&self, record: VdBsqHypothesisStackRecord<'sess>) -> bool {
        self.active_hypotheses.is_record_active(record)
    }
}

impl<'sess> VdBsqHypothesisStack<'sess> {
    pub fn push(
        &mut self,
        hypothesis_idx: VdBsqHypothesisIdx<'sess>,
        entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
    ) {
        let stack_idx = self.active_hypotheses.len();
        self.active_hypotheses.push(hypothesis_idx);
        let record = VdBsqHypothesisStackRecord {
            stack_idx,
            hypothesis_idx,
        };
        self.add_hypothesis_to_expr_map(record, entry);
        self.add_hypothesis_to_term_map(record, entry);
        self.stashes
            .add_hypothesis(record, entry, db, &self.active_hypotheses);
    }

    fn add_hypothesis_to_expr_map(
        &mut self,
        record: VdBsqHypothesisStackRecord<'sess>,
        entry: &VdBsqHypothesisEntry<'sess>,
    ) {
        let expr = entry.expr();
        // only add the hypothesis to the term map if the term is not already present
        if self.get_active_hypothesis_with_expr(expr).is_none() {
            self.expr_to_hypothesis_map.insert(expr, record);
        }
    }

    fn add_hypothesis_to_term_map(
        &mut self,
        record: VdBsqHypothesisStackRecord<'sess>,
        entry: &VdBsqHypothesisEntry<'sess>,
    ) {
        let term = entry.expr().term();
        // only add the hypothesis to the term map if the term is not already present
        if term.is_nontrivial()
            && self
                .get_active_hypothesis_with_nontrivial_term(term)
                .is_none()
        {
            self.term_to_hypothesis_map.insert(term, record);
        }
    }

    pub fn rollback(&mut self, len: usize) {
        debug_assert!(len <= self.len());
        self.active_hypotheses.truncate(len);
    }

    pub fn enter_block(&mut self) {
        self.block_starts.push(self.active_hypotheses.len());
    }

    pub fn exit_block(&mut self) {
        let block_start = self.block_starts.pop().unwrap();
        self.active_hypotheses.truncate(block_start);
    }
}

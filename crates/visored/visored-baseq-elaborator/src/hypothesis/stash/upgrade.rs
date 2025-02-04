//! one key can map to one unique value, but the value can be upgraded
use super::*;
use crate::hypothesis::{
    stack::{VdBsqActiveHypotheses, VdBsqHypothesisStackRecord},
    VdBsqHypothesisEntry, VdBsqHypothesisIdx,
};
use floated_sequential::db::FloaterDb;
use husky_control_flow_utils::require;
use rustc_hash::FxHashMap;
use smallvec::*;
use std::{cell::RefCell, marker::PhantomData};

pub trait IsVdBsqHypothesisUpgradeStashScheme: IsVdBsqHypothesisStashScheme {
    fn is_new_value_upgrade_of_old<'sess>(
        old: &Self::Value<'sess>,
        new: &Self::Value<'sess>,
    ) -> bool;
    fn key_value_from_hypothesis<'sess>(
        record: VdBsqHypothesisStackRecord<'sess>,
        entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<(Self::Key<'sess>, Self::Value<'sess>)>;
}

pub struct VdBsqHypothesisUpgradeStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    map: FxHashMap<Scheme::Key<'sess>, VdBsqHypothesisUpgradeStashEntry<'sess, Scheme>>,
}

impl<'sess, Scheme> std::fmt::Debug for VdBsqHypothesisUpgradeStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("VdBsqHypothesisUpgradeStash")
            .field("map", &self.map)
            .finish()
    }
}

pub struct VdBsqHypothesisUpgradeStashEntry<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    values: RefCell<SmallVec<[(VdBsqHypothesisStackRecord<'sess>, Scheme::Value<'sess>); 4]>>,
}

impl<'sess, Scheme> std::fmt::Debug for VdBsqHypothesisUpgradeStashEntry<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.values.borrow().iter()).finish()
    }
}

impl<'sess, Scheme> Default for VdBsqHypothesisUpgradeStashEntry<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    fn default() -> Self {
        Self {
            values: RefCell::new(smallvec![]),
        }
    }
}

impl<'sess, Scheme> Default for VdBsqHypothesisUpgradeStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    fn default() -> Self {
        Self {
            map: FxHashMap::default(),
        }
    }
}

impl<'sess, Scheme> VdBsqHypothesisUpgradeStashEntry<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    fn get_active_value<R>(
        &self,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
        f: impl FnOnce(&Scheme::Value<'sess>) -> R,
    ) -> Option<R> {
        self.clear_inactive_values(active_hypotheses);
        self.values.borrow().last().map(|(_, value)| f(value))
    }

    fn clear_inactive_values(&self, active_hypotheses: &VdBsqActiveHypotheses) {
        let mut values = self.values.borrow_mut();
        while let Some(&(stack_record, _)) = values.last()
            && !active_hypotheses.is_record_active(stack_record)
        {
            values.pop();
        }
    }
}

impl<'sess, Scheme> VdBsqHypothesisUpgradeStashEntry<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    fn cache(
        &mut self,
        hypothesis_stack_record: VdBsqHypothesisStackRecord<'sess>,
        active_hypotheses: &VdBsqActiveHypotheses,
        value: Scheme::Value<'sess>,
    ) {
        self.clear_inactive_values(active_hypotheses);
        let mut values = self.values.borrow_mut();
        match values.last() {
            Some((_, last_value)) if Scheme::is_new_value_upgrade_of_old(last_value, &value) => {
                values.push((hypothesis_stack_record, value));
            }
            None => {
                values.push((hypothesis_stack_record, value));
            }
            _ => (),
        }
    }
}

impl<'sess, Scheme> VdBsqHypothesisUpgradeStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    pub fn new() -> Self {
        Self {
            map: FxHashMap::default(),
        }
    }
}

impl<'sess, Scheme> VdBsqHypothesisUpgradeStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    pub fn get_active_value(
        &self,
        key: Scheme::Key<'sess>,
        db: &'sess FloaterDb,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
    ) -> Option<Scheme::Value<'sess>>
    where
        Scheme::Value<'sess>: Copy,
    {
        let entry = self.map.get(&key)?;
        entry.get_active_value(active_hypotheses, |&value| value)
    }

    pub fn get_active_value_with<R>(
        &self,
        key: Scheme::Key<'sess>,
        db: &'sess FloaterDb,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
        f: impl FnOnce(&Scheme::Value<'sess>) -> R,
    ) -> Option<R> {
        self.map.get(&key)?.get_active_value(active_hypotheses, f)
    }
}

impl<'sess, Scheme> VdBsqHypothesisUpgradeStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUpgradeStashScheme,
{
    pub fn add_hypothesis(
        &mut self,
        hypothesis_stack_record: VdBsqHypothesisStackRecord<'sess>,
        hypothesis_entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
    ) {
        require!(let Some((key, value)) =
            Scheme::key_value_from_hypothesis(hypothesis_stack_record, hypothesis_entry, db));
        self.map
            .entry(key)
            .or_default()
            .cache(hypothesis_stack_record, active_hypotheses, value);
    }
}

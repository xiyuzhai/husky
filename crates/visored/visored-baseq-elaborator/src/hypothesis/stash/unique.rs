//! one key can map to one unique value
use super::*;
use crate::{
    hypothesis::{
        stack::{
            VdBsqActiveHypotheses, VdBsqHypothesisStack, VdBsqHypothesisStackRecord,
            VdBsqHypothesisStackRecorded,
        },
        VdBsqHypothesisEntry,
    },
    term::VdBsqTerm,
};
use floated_sequential::db::FloaterDb;
use rustc_hash::FxHashMap;
use std::marker::PhantomData;

pub struct VdBsqHypothesisUniqueStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUniqueStashScheme,
{
    map: FxHashMap<Scheme::Key<'sess>, VdBsqHypothesisStackRecorded<'sess, Scheme::Value<'sess>>>,
}

pub trait IsVdBsqHypothesisUniqueStashScheme: IsVdBsqHypothesisStashScheme {
    fn key_value_from_hypothesis<'sess>(
        record: VdBsqHypothesisStackRecord<'sess>,
        entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
    ) -> Option<(Self::Key<'sess>, Self::Value<'sess>)>;
}

impl<'sess, Scheme> VdBsqHypothesisUniqueStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUniqueStashScheme,
{
    pub(crate) fn new() -> Self {
        Self {
            map: FxHashMap::default(),
        }
    }
}

impl<'sess, Scheme> VdBsqHypothesisUniqueStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUniqueStashScheme,
{
    fn get_recorded(
        &self,
        key: &Scheme::Key<'sess>,
    ) -> Option<&VdBsqHypothesisStackRecorded<'sess, Scheme::Value<'sess>>> {
        self.map.get(key)
    }

    pub fn get_valid_value(
        &self,
        key: &Scheme::Key<'sess>,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
    ) -> Option<&Scheme::Value<'sess>> {
        self.get_recorded(key)
            .map(|recorded| recorded.get_valid_value(active_hypotheses))
            .flatten()
    }
}

impl<'sess, Scheme> VdBsqHypothesisUniqueStash<'sess, Scheme>
where
    Scheme: IsVdBsqHypothesisUniqueStashScheme,
{
    pub(crate) fn add_hypothesis(
        &mut self,
        hypothesis_stack_record: VdBsqHypothesisStackRecord<'sess>,
        hypothesis_entry: &VdBsqHypothesisEntry<'sess>,
        db: &'sess FloaterDb,
        active_hypotheses: &VdBsqActiveHypotheses<'sess>,
    ) {
        let Some((key, value)) =
            Scheme::key_value_from_hypothesis(hypothesis_stack_record, hypothesis_entry, db)
        else {
            return;
        };
        if let Some(existing_value) = self.get_valid_value(&key, active_hypotheses) {
            assert_eq!(existing_value, &value);
        } else {
            debug_assert!(self
                .map
                .insert(
                    key,
                    VdBsqHypothesisStackRecorded::new(hypothesis_stack_record, value)
                )
                .is_none());
        }
    }
}

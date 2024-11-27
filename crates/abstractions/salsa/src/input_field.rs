use crate::ingredient::{fmt_index, Ingredient, IngredientRequiresReset};
use crate::key::DependencyIndex;
use crate::runtime::local_state::QueryOrigin;
use crate::runtime::StampedValue;
use crate::{cycle::CycleRecoveryStrategy, Db};
use crate::{AsId, DatabaseKeyIndex, Durability, Id, IngredientIndex, Revision, Runtime};
use dashmap::mapref::entry::Entry;
use dashmap::DashMap;
use std::fmt;

/// Ingredient used to represent the fields of a `#[salsa::input]`.
///
/// These fields can only be mutated by a call to a setter with an `&mut`
/// reference to the database, and therefore cannot be mutated during a tracked
/// function or in parallel.
/// However for on-demand inputs to work the fields must be able to be set via
/// a shared reference, so some locking is required.
/// Altogether this makes the implementation somewhat simpler than tracked
/// structs.
pub struct InputFieldIngredient<K, V> {
    index: IngredientIndex,
    // value is stored in a box so internal moves in the dashmap don't
    // invalidate the reference to the value inside the box.
    // Values are only removed or altered when we have `&mut self`.
    map: DashMap<Id, Box<StampedValue<V>>>,
    debug_name: &'static str,
    phantom: std::marker::PhantomData<K>,
}

impl<K, V> InputFieldIngredient<K, V>
where
    K: Eq + AsId,
{
    pub fn new(index: IngredientIndex, debug_name: &'static str) -> Self {
        Self {
            index,
            map: Default::default(),
            debug_name,
            phantom: std::marker::PhantomData,
        }
    }

    // why this needs mut?
    pub fn store_mut(
        &mut self,
        runtime: &Runtime,
        key: K,
        value: V,
        durability: Durability,
    ) -> Option<V> {
        runtime.report_store_mut(durability);
        let revision = runtime.current_revision();
        let stamped_value = Box::new(StampedValue {
            value,
            durability,
            changed_at: revision,
        });

        self.map
            .insert(key.as_id(), stamped_value)
            .map(|old_value| old_value.value)
    }

    /// Set the field of a new input.
    ///
    /// This function panics if the field has ever been set before.
    pub fn store_new(&self, runtime: &Runtime, key: K, value: V, durability: Durability) {
        let revision = runtime.current_revision();
        let stamped_value = Box::new(StampedValue {
            value,
            durability,
            changed_at: revision,
        });

        match self.map.entry(key.as_id()) {
            Entry::Occupied(_) => {
                panic!("attempted to set field of existing input using `store_new`, use `store_mut` instead");
            }
            Entry::Vacant(entry) => {
                entry.insert(stamped_value);
            }
        }
    }

    pub fn fetch<'db>(&'db self, runtime: &'db Runtime, key: K) -> &V {
        let StampedValue {
            value,
            durability,
            changed_at,
        } = &**self.map.get(&key.as_id()).unwrap();

        runtime.report_tracked_read(
            self.database_key_index(key).into(),
            *durability,
            *changed_at,
        );

        // SAFETY:
        // The value is stored in a box so internal moves in the dashmap don't
        // invalidate the reference to the value inside the box.
        // Values are only removed or altered when we have `&mut self`.
        unsafe { transmute_lifetime(self, value) }
    }

    fn database_key_index(&self, key: K) -> DatabaseKeyIndex {
        DatabaseKeyIndex {
            ingredient_index: self.index,
            key_index: key.as_id(),
        }
    }
}

// Returns `u` but with the lifetime of `t`.
//
// Safe if you know that data at `u` will remain shared
// until the reference `t` expires.
unsafe fn transmute_lifetime<'t, 'u, T, U>(_t: &'t T, u: &'u U) -> &'t U {
    std::mem::transmute(u)
}

impl<K, V> Ingredient for InputFieldIngredient<K, V>
where
    K: AsId,
{
    fn cycle_recovery_strategy(&self) -> CycleRecoveryStrategy {
        CycleRecoveryStrategy::Panic
    }

    fn maybe_changed_after(&self, _db: &Db, input: DependencyIndex, revision: Revision) -> bool {
        let key = K::from_id(input.key_index.unwrap());
        self.map.get(&key.as_id()).unwrap().changed_at > revision
    }

    fn origin(&self, _key_index: Id) -> Option<QueryOrigin> {
        None
    }

    fn mark_validated_output(
        &self,
        _db: &Db,
        _executor: DatabaseKeyIndex,
        _output_key: Option<Id>,
    ) {
    }

    fn remove_stale_output(
        &self,
        _db: &Db,
        _executor: DatabaseKeyIndex,
        _stale_output_key: Option<Id>,
    ) {
    }

    fn salsa_struct_deleted(&self, _db: &Db, _id: Id) {
        panic!("unexpected call: input fields are never deleted");
    }

    fn reset_for_new_revision(&mut self) {
        panic!("unexpected call: input fields don't register for resets");
    }

    fn fmt_index(&self, index: Option<crate::Id>, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt_index(self.debug_name, index, fmt)
    }
}

impl<K, V> IngredientRequiresReset for InputFieldIngredient<K, V>
where
    K: AsId,
{
    const RESET_ON_NEW_REVISION: bool = false;
}

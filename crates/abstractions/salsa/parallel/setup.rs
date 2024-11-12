use std::{cell::Cell, sync::Arc};

use salsa::test_helpers::Db;

use crate::signal::Signal;

/// Various "knobs" and utilities used by tests to force
/// a certain behavior.
pub(crate) trait Knobs {
    fn knobs(&self) -> &KnobsStruct;

    fn signal(&self, stage: usize);

    fn wait_for(&self, stage: usize);
}

impl Knobs for Db {
    fn knobs(&self) -> &KnobsStruct {
        todo!()
    }

    fn signal(&self, stage: usize) {
        todo!()
    }

    fn wait_for(&self, stage: usize) {
        todo!()
    }
}

/// Various "knobs" that can be used to customize how the queries
/// behave on one specific thread. Note that this state is
/// intentionally thread-local (apart from `signal`).
#[derive(Clone, Default)]
pub(crate) struct KnobsStruct {
    /// A kind of flexible barrier used to coordinate execution across
    /// threads to ensure we reach various weird states.
    pub(crate) signal: Arc<Signal>,

    /// When this database is about to block, send a signal.
    pub(crate) signal_on_will_block: Cell<usize>,
}

#[salsa::db(
    crate::parallel_cycle_one_recover::Jar,
    crate::parallel_cycle_none_recover::Jar,
    crate::parallel_cycle_mid_recover::Jar,
    crate::parallel_cycle_all_recover::Jar
)]
#[derive(Default)]
pub(crate) struct Database {
    storage: salsa::Storage,
    knobs: KnobsStruct,
}

impl Knobs for Database {
    fn knobs(&self) -> &KnobsStruct {
        &self.knobs
    }

    fn signal(&self, stage: usize) {
        self.knobs.signal.signal(stage);
    }

    fn wait_for(&self, stage: usize) {
        self.knobs.signal.wait_for(stage);
    }
}

use husky_linket::linket::Linket;
use husky_linket_impl::linket_impl::{IsLinketImpl, LinketImplFrozenValue};
use husky_vmir::stmt::VmirStmtIdx;
use vec_like::{ordered_vec_map::OrderedVecPairMap, SmallVecPairMap};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VmSnapshotKey {
    Loop { loop_index: usize },
}

#[derive(Debug)]
pub struct VmSnapshot<LinketImpl: IsLinketImpl> {
    linket: Linket,
    variable_frozen_values: Vec<LinketImplFrozenValue<LinketImpl>>,
}

impl<LinketImpl: IsLinketImpl> VmSnapshot<LinketImpl> {
    pub(crate) fn new(
        linket: Linket,
        variable_frozen_values: Vec<LinketImplFrozenValue<LinketImpl>>,
    ) -> Self {
        Self {
            linket,
            variable_frozen_values,
        }
    }
}

impl<LinketImpl: IsLinketImpl> VmSnapshot<LinketImpl> {
    pub fn linket(&self) -> Linket {
        self.linket
    }

    pub fn place_frozen_values(&self) -> &[LinketImplFrozenValue<LinketImpl>] {
        &self.variable_frozen_values
    }
}

pub(crate) type VmSnapshotsData<LinketImpl: IsLinketImpl> = SmallVecPairMap<
    VmirStmtIdx<LinketImpl>,
    OrderedVecPairMap<VmSnapshotKey, VmSnapshot<LinketImpl>>,
    4,
>;

#[derive(Debug)]
pub struct VmSnapshots<LinketImpl: IsLinketImpl> {
    data: VmSnapshotsData<LinketImpl>,
}

impl<LinketImpl: IsLinketImpl> VmSnapshots<LinketImpl> {
    pub fn new(data: VmSnapshotsData<LinketImpl>) -> Self {
        Self { data }
    }
}

impl<LinketImpl: IsLinketImpl> VmSnapshots<LinketImpl> {}

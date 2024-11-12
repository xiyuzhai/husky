use crate::snapshot::{VmSnapshot, VmSnapshotKey, VmSnapshots, VmSnapshotsData};
use husky_linket::linket::Linket;
use husky_linket_impl::{linket_impl::IsLinketImpl, LinketImplVmControlFlowFrozen};
use husky_vmir::{
    expr::{VmirExprIdx, VmirExprMap},
    stmt::{VmirStmtIdx, VmirStmtMap},
};
use std::sync::Mutex;
use vec_like::ordered_vec_map::OrderedVecPairMap;

#[derive(Debug)]
pub struct VmHistory<LinketImpl: IsLinketImpl> {
    linket: Linket,
    expr_control_flows: VmirExprMap<LinketImpl, VmRecord<LinketImpl>>,
    stmt_control_flows: VmirStmtMap<LinketImpl, VmRecord<LinketImpl>>,
    snapshots: Mutex<VmSnapshots<LinketImpl>>,
}

impl<LinketImpl> VmHistory<LinketImpl>
where
    LinketImpl: IsLinketImpl,
{
    pub(crate) fn new(
        linket: Linket,
        expr_control_flows: VmirExprMap<LinketImpl, VmRecord<LinketImpl>>,
        stmt_control_flows: VmirStmtMap<LinketImpl, VmRecord<LinketImpl>>,
        snapshots: VmSnapshotsData<LinketImpl>,
    ) -> Self {
        Self {
            linket,
            expr_control_flows,
            stmt_control_flows,
            snapshots: Mutex::new(VmSnapshots::new(snapshots)),
        }
    }
}

impl<LinketImpl> VmHistory<LinketImpl>
where
    LinketImpl: IsLinketImpl,
{
    pub fn linket(&self) -> Linket {
        self.linket
    }

    pub fn expr_record(&self, expr: VmirExprIdx<LinketImpl>) -> Option<&VmRecord<LinketImpl>> {
        self.expr_control_flows.get(*expr)
    }

    pub fn stmt_record(&self, stmt: VmirStmtIdx<LinketImpl>) -> Option<&VmRecord<LinketImpl>> {
        self.stmt_control_flows.get(*stmt)
    }
}

#[derive(Debug)]
pub struct VmRecord<LinketImpl: IsLinketImpl> {
    control_flow: LinketImplVmControlFlowFrozen<LinketImpl>,
}

impl<LinketImpl: IsLinketImpl> VmRecord<LinketImpl> {
    pub fn new(control_flow: LinketImplVmControlFlowFrozen<LinketImpl>) -> Self {
        Self { control_flow }
    }
}

impl<LinketImpl: IsLinketImpl> VmRecord<LinketImpl> {
    pub fn control_flow(&self) -> &LinketImplVmControlFlowFrozen<LinketImpl> {
        &self.control_flow
    }
}

use super::*;
use husky_linket::linket::Linket;
use husky_trace::trace::TraceData;
use husky_vm::{eval::*, vm::VmMode};
use std::sync::Arc;

impl<Devsoul: IsDevsoul> Devtime<Devsoul> {
    pub fn trace_history(
        &self,
        trace: Trace,
        pedestal: Devsoul::Pedestal,
    ) -> Arc<VmHistory<Devsoul::LinketImpl>> {
        let db = self.db();
        match trace.data(db) {
            TraceData::Submodule(submodule_trace_data) => todo!(),
            TraceData::Val(_) => {
                let key = (trace, pedestal.clone());
                self.eager_trace_cache
                    .entry(key)
                    .or_insert_with(|| Arc::new(self.calc_trace_history(trace, pedestal).1))
                    .value()
                    .clone()
            }
            TraceData::StaticVar(static_var_trace_data) => todo!(),
            TraceData::LazyCall(lazy_call_trace_data) => todo!(),
            TraceData::LazyPattern(lazy_pattern_trace_data) => todo!(),
            TraceData::LazyLoopFrame(lazy_loop_frame_trace_data) => todo!(),
            TraceData::LazyLoopRange(lazy_loop_range_trace_data) => todo!(),
            TraceData::EagerCallInput(eager_call_input_trace_data) => todo!(),
            TraceData::EagerCall(eager_call_trace_data) => todo!(),
            TraceData::EagerPattern(eager_pattern_trace_data) => todo!(),
            TraceData::EagerLoopFrame(eager_loop_frame_trace_data) => todo!(),
            TraceData::EagerLoopRange(eager_loop_range_trace_data) => todo!(),
            TraceData::Place(place_trace_data) => todo!(),
            TraceData::Script(script_trace_data) => todo!(),
            _ => self.trace_history(trace.biological_parent(db).unwrap(), pedestal),
        }
    }

    fn calc_trace_history(
        &self,
        trace: Trace,
        pedestal: Devsoul::Pedestal,
    ) -> (
        DevsoulVmControlFlowFrozen<Devsoul>,
        VmHistory<Devsoul::LinketImpl>,
    ) {
        let db = self.db();
        self.runtime
            .with_default_var_ids(
                trace.history_var_deps(db).unwrap().iter().copied(),
                pedestal.clone(),
                |pedestal, _| self.calc_trace_history_aux(trace, pedestal, db),
            )
            .unwrap_or_else(|_| todo!("Handle error case"))
    }

    fn calc_trace_history_aux(
        &self,
        trace: Trace,
        pedestal: Devsoul::Pedestal,
        db: &::salsa::Db,
    ) -> (
        DevsoulVmControlFlowFrozen<Devsoul>,
        VmHistory<Devsoul::LinketImpl>,
    ) {
        let db = self.db();
        let linktime = self.runtime.comptime().linktime();
        match trace.data(db) {
            TraceData::Val(val) => {
                let path = val.val_path();
                let linket = Linket::new_val(path, db).unwrap();
                let (flow, history) = eval_linket_on_arguments(
                    linket,
                    vec![],
                    VmMode::Record,
                    db,
                    &*self.runtime,
                    &self.vmir_storage,
                )
                .unwrap();
                (flow.freeze(), history)
            }
            TraceData::StaticVar(_) => todo!(),
            TraceData::EagerCallInput(_) => todo!(),
            TraceData::EagerCall(_) => todo!(),
            TraceData::EagerExpr(_) => todo!(),
            TraceData::EagerPattern(_) => todo!(),
            TraceData::EagerStmt(_) => todo!(),
            TraceData::Place(_) => todo!(),
            TraceData::Script(_) => todo!(),
            _ => unreachable!("trace = {:?}", trace.debug(db)),
        }
    }
}

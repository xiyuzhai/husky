use super::*;
use crate::registry::assoc_trace::VoidAssocTraceRegistry;
use husky_hir_eager_expr::HirEagerExprIdx;
use husky_sem_expr::{helpers::range::sem_expr_range_region, SemExprRegion};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EagerCallInputTracePathData {
    biological_parent_path: TracePath,
    // todo: add more?
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EagerCallInputTraceData {
    path: TracePath,
    biological_parent: Trace,
    input_sketch: EagerCallInputSketch,
    #[skip_fmt]
    caller_sem_expr_region: SemExprRegion,
    #[skip_fmt]
    callee_syn_expr_region: SynExprRegion,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EagerCallInputSketch {
    Simple {
        // parameter_syn_pattern_idx: SynPatternIdx,
        argument_sem_expr_idx: SemExprIdx,
        argument_hir_eager_expr_idx: Option<HirEagerExprIdx>,
    },
    Variadic,
    Keyed,
}

impl Trace {
    pub(crate) fn new_eager_call_input(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        input_sketch: EagerCallInputSketch,
        caller_sem_expr_region: SemExprRegion,
        callee_syn_expr_region: SynExprRegion,
        db: &::salsa::Db,
    ) -> Self {
        let path = TracePath::new(
            EagerCallInputTracePathData {
                biological_parent_path: biological_parent_path.into(),
            },
            db,
        );
        Trace::new(
            path,
            EagerCallInputTraceData {
                path,
                biological_parent: biological_parent.into(),
                input_sketch,
                caller_sem_expr_region,
                callee_syn_expr_region,
            }
            .into(),
            db,
        )
    }
}

impl EagerCallInputTraceData {
    pub fn view_lines(&self, db: &::salsa::Db) -> TraceViewLines {
        let caller_sem_expr_region = self.caller_sem_expr_region;
        let caller_sem_expr_range_region = sem_expr_range_region(db, caller_sem_expr_region);
        let caller_sem_expr_range_region_data = caller_sem_expr_range_region.data(db);
        let caller_region_path = caller_sem_expr_region.path(db);
        match self.input_sketch {
            EagerCallInputSketch::Simple {
                argument_sem_expr_idx,
                argument_hir_eager_expr_idx: _,
            } => {
                let argument_regional_token_idx_range =
                    caller_sem_expr_range_region_data[argument_sem_expr_idx];
                let argument_token_idx_range = argument_regional_token_idx_range
                    .token_idx_range(caller_region_path.regional_token_idx_base(db).unwrap());
                TraceViewLines::new(
                    caller_region_path.module_path(db),
                    argument_token_idx_range,
                    VoidAssocTraceRegistry,
                    db,
                )
            }
            EagerCallInputSketch::Variadic => todo!(),
            EagerCallInputSketch::Keyed => todo!(),
        }
    }

    pub fn have_subtraces(&self, _db: &::salsa::Db) -> bool {
        false
    }

    pub fn subtraces(&self) -> Vec<Trace> {
        vec![]
    }

    pub fn ki_repr(&self, _db: &::salsa::Db) -> KiRepr {
        todo!()
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        match self.input_sketch {
            EagerCallInputSketch::Simple {
                argument_sem_expr_idx,
                argument_hir_eager_expr_idx,
            } => {
                let parent = self.biological_parent;
                parent
                    .var_deps_expansion(db)
                    .expr_control_flow_var_deps(argument_sem_expr_idx, db)
                    .clone()
            }
            EagerCallInputSketch::Variadic => todo!(),
            EagerCallInputSketch::Keyed => todo!(),
        }
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        todo!()
    }

    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}

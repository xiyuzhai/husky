use husky_coword::IdentPairMap;
use husky_hir_eager_expr::variable::runtime::HirEagerRuntimeVariableIdx;
use husky_sem_expr::{helpers::range::sem_expr_range_region, SemExprRegion};

use crate::registry::assoc_trace::VoidAssocTraceRegistry;

use super::*;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EagerPatternTracePathData {
    biological_parent_path: TracePath,
    essence: EagerPatternEssence,
    disambiguator: TracePathDisambiguator<EagerPatternEssence>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum EagerPatternEssence {
    Haha,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EagerPatternTrace(Trace);

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EagerPatternTraceData {
    path: TracePath,
    biological_parent: Trace,
    syn_pattern_idx: SynPatternIdx,
    hir_eager_runtime_variable_idxs: IdentPairMap<Option<HirEagerRuntimeVariableIdx>>,
    #[skip_fmt]
    sem_expr_region: SemExprRegion,
}

impl Trace {
    pub(crate) fn new_eager_pattern(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        syn_pattern_idx: SynPatternIdx,
        hir_eager_runtime_variable_idxs: IdentPairMap<Option<HirEagerRuntimeVariableIdx>>,
        sem_expr_region: SemExprRegion,
        eager_pattern_trace_path_registry: &mut TracePathRegistry<EagerPatternEssence>,
        db: &::salsa::Db,
    ) -> Self {
        let essence = EagerPatternEssence::Haha;
        let path = TracePath::new(
            EagerPatternTracePathData {
                biological_parent_path,
                essence: essence.clone(),
                disambiguator: eager_pattern_trace_path_registry.issue(essence),
            },
            db,
        );
        Trace::new(
            path,
            EagerPatternTraceData {
                path,
                biological_parent: biological_parent.into(),
                syn_pattern_idx,
                hir_eager_runtime_variable_idxs,
                sem_expr_region,
            }
            .into(),
            db,
        )
    }
}

impl EagerPatternTraceData {
    pub fn view_lines(&self, db: &::salsa::Db) -> TraceViewLines {
        let sem_expr_region = self.sem_expr_region;
        let sem_expr_range_region = sem_expr_range_region(db, sem_expr_region);
        let sem_expr_range_region_data = sem_expr_range_region.data(db);
        let region_path = sem_expr_region.path(db);
        let regional_token_idx_range = sem_expr_range_region_data[self.syn_pattern_idx];
        let token_idx_range = regional_token_idx_range
            .token_idx_range(region_path.regional_token_idx_base(db).unwrap());
        TraceViewLines::new(
            region_path.module_path(db),
            token_idx_range,
            VoidAssocTraceRegistry,
            db,
        )
    }

    pub fn have_subtraces(&self, _db: &::salsa::Db) -> bool {
        false
    }

    pub fn subtraces(&self) -> Vec<Trace> {
        vec![]
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        // ad hoc
        Default::default()
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        todo!()
    }

    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}

use super::*;
use crate::registry::assoc_trace::VoidAssocTraceRegistry;
use husky_coword::IdentPairMap;
use husky_hir_lazy_expr::{
    variable::HirLazyVariableIdx, HirLazyExprRegion, HirLazyPatternData, HirLazyPatternIdx,
};
use husky_ki_repr::expansion::KiReprExpansion;
use husky_sem_expr::{helpers::range::sem_expr_range_region, SemExprRegion};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LazyPatternTracePath(TracePath);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LazyPatternTracePathData {
    biological_parent_path: TracePath,
    essence: LazyPatternEssence,
    disambiguator: TracePathDisambiguator<LazyPatternEssence>,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum LazyPatternEssence {
    AdHoc,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct LazyPatternTraceData {
    path: TracePath,
    biological_parent: Trace,
    syn_pattern_idx: SynPatternIdx,
    hir_lazy_pattern_idx: Option<HirLazyPatternIdx>,
    hir_lazy_variable_idxs: IdentPairMap<Option<HirLazyVariableIdx>>,
    #[skip_fmt]
    sem_expr_region: SemExprRegion,
    #[skip_fmt]
    hir_lazy_expr_region: HirLazyExprRegion,
}

impl Trace {
    pub(crate) fn new_lazy_pattern(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        syn_pattern_idx: SynPatternIdx,
        hir_lazy_pattern_idx: Option<HirLazyPatternIdx>,
        hir_lazy_variable_idxs: IdentPairMap<Option<HirLazyVariableIdx>>,
        sem_expr_region: SemExprRegion,
        hir_lazy_expr_region: HirLazyExprRegion,
        lazy_expr_trace_path_registry: &mut TracePathRegistry<LazyPatternEssence>,
        db: &::salsa::Db,
    ) -> Self {
        let essence = LazyPatternEssence::AdHoc;
        let path = TracePath::new(
            LazyPatternTracePathData {
                biological_parent_path,
                essence: essence.clone(),
                disambiguator: lazy_expr_trace_path_registry.issue(essence),
            },
            db,
        );
        Trace::new(
            path,
            LazyPatternTraceData {
                path,
                biological_parent: biological_parent.into(),
                syn_pattern_idx,
                hir_lazy_pattern_idx,
                hir_lazy_variable_idxs,
                sem_expr_region,
                hir_lazy_expr_region,
            }
            .into(),
            db,
        )
    }
}

impl LazyPatternTraceData {
    pub fn have_subtraces(&self) -> bool {
        false
    }

    pub fn subtraces(&self) -> Vec<Trace> {
        vec![]
    }

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

    pub fn ki_repr(&self, trace_id: Trace, db: &::salsa::Db) -> Option<KiRepr> {
        let ki_repr_expansion = trace_ki_repr_expansion(db, trace_id);
        match self.hir_lazy_expr_region.hir_lazy_pattern_arena(db)[self.hir_lazy_pattern_idx?] {
            HirLazyPatternData::Literal(_) => todo!(),
            HirLazyPatternData::Ident { .. } => {
                let hir_lazy_variable_idxs = &self.hir_lazy_variable_idxs;
                debug_assert_eq!(hir_lazy_variable_idxs.len(), 1);
                let hir_lazy_variable_idx = hir_lazy_variable_idxs.data()[0].1?;
                Some(ki_repr_expansion.hir_lazy_variable_ki_repr_map(db)[hir_lazy_variable_idx])
            }
            HirLazyPatternData::Unit(_) => todo!(),
            HirLazyPatternData::Tuple { path: _, fields: _ } => todo!(),
            HirLazyPatternData::Props { path: _, fields: _ } => todo!(),
            HirLazyPatternData::OneOf { options: _ } => todo!(),
            HirLazyPatternData::Binding { ident: _, src: _ } => todo!(),
            HirLazyPatternData::Range { start: _, end: _ } => todo!(),
        }
    }

    pub fn ki_repr_expansion(&self, db: &::salsa::Db) -> KiReprExpansion {
        self.biological_parent.ki_repr_expansion(db)
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

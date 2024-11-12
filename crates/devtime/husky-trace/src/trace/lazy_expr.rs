use super::*;
use crate::registry::assoc_trace::VoidAssocTraceRegistry;
use husky_hir_lazy_expr::{
    source_map::{HirLazyExprSourceMap, HirLazyExprSourceMapData},
    HirLazyExprData, HirLazyExprIdx, HirLazyExprRegion,
};
use husky_ki_repr::expansion::KiReprExpansion;
use husky_sem_expr::{
    helpers::range::sem_expr_range_region, SemExprData, SemExprRegion, SemRitchieArgument,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LazyExprTracePathData {
    biological_parent_path: TracePath,
    essence: LazyExprEssence,
    disambiguator: TracePathDisambiguator<LazyExprEssence>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LazyExprEssence {
    Haha,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LazyExprTraceData {
    path: TracePath,
    biological_parent: Trace,
    sem_expr_idx: SemExprIdx,
    hir_lazy_expr_idx: Option<HirLazyExprIdx>,
    #[skip_fmt]
    sem_expr_region: SemExprRegion,
    #[skip_fmt]
    hir_lazy_expr_region: HirLazyExprRegion,
    #[skip_fmt]
    hir_lazy_expr_source_map: HirLazyExprSourceMap,
}

impl Trace {
    pub(crate) fn new_lazy_expr(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        sem_expr_idx: SemExprIdx,
        hir_lazy_expr_idx: Option<HirLazyExprIdx>,
        sem_expr_region: SemExprRegion,
        hir_lazy_expr_region: HirLazyExprRegion,
        hir_lazy_expr_source_map: HirLazyExprSourceMap,
        lazy_expr_trace_path_registry: &mut TracePathRegistry<LazyExprEssence>,
        db: &::salsa::Db,
    ) -> Self {
        let essence = LazyExprEssence::Haha;
        let path = TracePath::new(
            LazyExprTracePathData {
                biological_parent_path,
                essence: essence.clone(),
                disambiguator: lazy_expr_trace_path_registry.issue(essence),
            },
            db,
        );
        Trace::new(
            path,
            LazyExprTraceData {
                path,
                biological_parent: biological_parent.into(),
                sem_expr_idx,
                hir_lazy_expr_idx,
                sem_expr_region,
                hir_lazy_expr_region,
                hir_lazy_expr_source_map,
            }
            .into(),
            db,
        )
    }
}

impl LazyExprTraceData {
    pub fn view_lines(&self, db: &::salsa::Db) -> TraceViewLines {
        let sem_expr_region = self.sem_expr_region;
        let sem_expr_range_region = sem_expr_range_region(db, sem_expr_region);
        let sem_expr_range_region_data = sem_expr_range_region.data(db);
        let region_path = sem_expr_region.path(db);
        let regional_token_idx_range = sem_expr_range_region_data[self.sem_expr_idx];
        let token_idx_range = regional_token_idx_range
            .token_idx_range(region_path.regional_token_idx_base(db).unwrap());
        TraceViewLines::new(
            region_path.module_path(db),
            token_idx_range,
            VoidAssocTraceRegistry,
            db,
        )
    }

    pub fn have_subtraces(&self, db: &::salsa::Db) -> bool {
        use husky_hir_defn::defn::HasHirDefn;
        let Some(hir_eager_expr_idx) = self.hir_lazy_expr_idx else {
            return false;
        };
        match self.hir_lazy_expr_region.hir_lazy_expr_arena(db)[hir_eager_expr_idx] {
            HirLazyExprData::FunctionRitchieItemCall { path, .. } => path.hir_defn(db).is_some(),
            HirLazyExprData::AssocFunctionRitchieCall { path, .. } => path.hir_defn(db).is_some(),
            HirLazyExprData::MethodRitchieCall { path, .. } => path.hir_defn(db).is_some(),
            HirLazyExprData::AssocRitchie { path } => path.hir_defn(db).is_some(),
            HirLazyExprData::Block { stmts: _ } => unreachable!(),
            _ => false,
        }
    }

    pub fn subtraces(&self, trace: Trace, db: &::salsa::Db) -> Vec<Trace> {
        let biological_parent_path = self.path;
        let biological_parent = trace;
        let sem_expr_idx = self.sem_expr_idx;
        let Some(hir_eager_expr_idx) = self.hir_lazy_expr_idx else {
            return vec![];
        };
        let sem_expr_region_data = self.sem_expr_region.data(db);
        let hir_lazy_expr_source_map_data = self.hir_lazy_expr_source_map.data(db);
        match self.hir_lazy_expr_region.hir_lazy_expr_arena(db)[hir_eager_expr_idx] {
            HirLazyExprData::FunctionRitchieItemCall { path, .. } => {
                let SemExprData::FunctionRitchieCall {
                    ref ritchie_parameter_argument_matches,
                    ..
                } = sem_expr_idx.data(sem_expr_region_data.sem_expr_arena())
                else {
                    unreachable!()
                };
                let mut subtraces: Vec<Trace> = fn_call_lazy_expr_trace_input_traces(
                    biological_parent_path,
                    biological_parent,
                    ritchie_parameter_argument_matches,
                    hir_lazy_expr_source_map_data,
                    db,
                );
                subtraces.push(
                    Trace::new_lazy_call(
                        biological_parent_path,
                        biological_parent,
                        path.into(),
                        db,
                    )
                    .into(),
                );
                subtraces
            }
            HirLazyExprData::AssocFunctionRitchieCall { path, .. } => {
                let SemExprData::FunctionRitchieCall {
                    ref ritchie_parameter_argument_matches,
                    ..
                } = sem_expr_idx.data(sem_expr_region_data.sem_expr_arena())
                else {
                    unreachable!()
                };
                let mut subtraces: Vec<Trace> = fn_call_lazy_expr_trace_input_traces(
                    biological_parent_path,
                    biological_parent,
                    ritchie_parameter_argument_matches,
                    hir_lazy_expr_source_map_data,
                    db,
                );
                subtraces.push(
                    Trace::new_lazy_call(
                        biological_parent_path,
                        biological_parent,
                        path.into(),
                        db,
                    )
                    .into(),
                );
                subtraces
            }
            HirLazyExprData::MethodRitchieCall { path, .. } => {
                let SemExprData::FunctionRitchieCall {
                    ref ritchie_parameter_argument_matches,
                    ..
                } = sem_expr_idx.data(sem_expr_region_data.sem_expr_arena())
                else {
                    unreachable!()
                };
                let mut subtraces: Vec<Trace> = fn_call_lazy_expr_trace_input_traces(
                    biological_parent_path,
                    biological_parent,
                    ritchie_parameter_argument_matches,
                    hir_lazy_expr_source_map_data,
                    db,
                );
                subtraces.push(
                    Trace::new_lazy_call(
                        biological_parent_path,
                        biological_parent,
                        path.into(),
                        db,
                    )
                    .into(),
                );
                subtraces
            }
            HirLazyExprData::Block { .. } => unreachable!(),
            HirLazyExprData::FunctionRitchieItemCall { path, .. } => {
                let SemExprData::FunctionRitchieCall {
                    ref ritchie_parameter_argument_matches,
                    ..
                } = sem_expr_idx.data(sem_expr_region_data.sem_expr_arena())
                else {
                    unreachable!()
                };
                let mut subtraces: Vec<Trace> = fn_call_lazy_expr_trace_input_traces(
                    biological_parent_path,
                    biological_parent,
                    ritchie_parameter_argument_matches,
                    hir_lazy_expr_source_map_data,
                    db,
                );
                subtraces.push(
                    Trace::new_lazy_call(
                        biological_parent_path,
                        biological_parent,
                        path.into(),
                        db,
                    )
                    .into(),
                );
                subtraces
            }
            _ => vec![],
        }
    }

    pub fn ki_repr(&self, trace: Trace, db: &::salsa::Db) -> Option<KiRepr> {
        let ki_repr_expansion = trace_ki_repr_expansion(db, trace);
        Some(ki_repr_expansion.hir_lazy_expr_ki_repr_map(db)[self.hir_lazy_expr_idx?])
    }

    pub fn ki_repr_expansion(&self, db: &::salsa::Db) -> KiReprExpansion {
        self.biological_parent.ki_repr_expansion(db)
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        self.var_deps_expansion(db)
            .expr_control_flow_var_deps(self.sem_expr_idx, db)
            .clone()
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        self.biological_parent.var_deps_expansion(db)
    }

    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}

fn fn_call_lazy_expr_trace_input_traces(
    trace_path: TracePath,
    trace: Trace,
    ritchie_parameter_argument_matches: &[SemRitchieArgument],
    hir_lazy_expr_source_map_data: &HirLazyExprSourceMapData,
    db: &::salsa::Db,
) -> Vec<Trace> {
    ritchie_parameter_argument_matches
        .iter()
        .map(|m| {
            let data = match m {
                SemRitchieArgument::Simple(_, list_item) => {
                    let sem_expr_idx = list_item.argument_sem_expr_idx();
                    LazyCallInputSketch::Simple {
                        sem_expr_idx,
                        hir_lazy_expr_idx: hir_lazy_expr_source_map_data
                            .sem_to_hir_lazy_expr_idx(sem_expr_idx),
                    }
                }
                SemRitchieArgument::Variadic(_, _) => {
                    todo!()
                }
                SemRitchieArgument::Keyed(_, _) => {
                    todo!()
                }
            };
            Trace::new_lazy_call_input(trace_path, trace, data, db).into()
        })
        .collect()
}

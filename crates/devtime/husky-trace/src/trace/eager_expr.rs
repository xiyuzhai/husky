use super::*;
use crate::registry::assoc_trace::VoidAssocTraceRegistry;
use husky_hir_eager_expr::{
    HirEagerExprData, HirEagerExprIdx, HirEagerExprRegion, HirEagerExprSourceMap,
    HirEagerExprSourceMapData,
};
use husky_sem_expr::{
    helpers::range::sem_expr_range_region, SemExprData, SemExprRegion, SemRitchieArgument,
};
use husky_syn_decl::decl::HasSynDecl;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EagerExprTracePathData {
    biological_parent_path: TracePath,
    essence: EagerExprEssence,
    disambiguator: TracePathDisambiguator<EagerExprEssence>,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum EagerExprEssence {
    Haha,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct EagerExprTraceData {
    path: TracePath,
    biological_parent: Trace,
    sem_expr_idx: SemExprIdx,
    hir_eager_expr_idx: Option<HirEagerExprIdx>,
    #[skip_fmt]
    sem_expr_region: SemExprRegion,
    #[skip_fmt]
    hir_eager_expr_region: HirEagerExprRegion,
    #[skip_fmt]
    hir_eager_expr_source_map: HirEagerExprSourceMap,
}

impl Trace {
    pub(crate) fn new_eager_expr(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        sem_expr_idx: SemExprIdx,
        hir_eager_expr_idx: Option<HirEagerExprIdx>,
        sem_expr_region: SemExprRegion,
        hir_eager_expr_region: HirEagerExprRegion,
        hir_eager_expr_source_map: HirEagerExprSourceMap,
        eager_expr_trace_path_registry: &mut TracePathRegistry<EagerExprEssence>,
        db: &::salsa::Db,
    ) -> Self {
        let essence = EagerExprEssence::Haha;
        let path = TracePath::new(
            EagerExprTracePathData {
                biological_parent_path,
                essence: essence.clone(),
                disambiguator: eager_expr_trace_path_registry.issue(essence),
            },
            db,
        );
        Trace::new(
            path,
            EagerExprTraceData {
                path,
                biological_parent: biological_parent.into(),
                sem_expr_idx,
                hir_eager_expr_idx,
                sem_expr_region,
                hir_eager_expr_region,
                hir_eager_expr_source_map,
            }
            .into(),
            db,
        )
    }
}

impl EagerExprTraceData {
    pub fn hir_eager_expr_idx(&self) -> Option<HirEagerExprIdx> {
        self.hir_eager_expr_idx
    }

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
        let Some(hir_eager_expr_idx) = self.hir_eager_expr_idx else {
            return false;
        };
        match *self.hir_eager_expr_region.expr_arena(db)[hir_eager_expr_idx].data() {
            HirEagerExprData::FunctionRitchieCall { path, .. } => path.hir_defn(db).is_some(),
            HirEagerExprData::AssocFunctionRitchieCall { path, .. } => path.hir_defn(db).is_some(),
            HirEagerExprData::MethodRitchieCall { path, .. } => path.hir_defn(db).is_some(),
            HirEagerExprData::Block { stmts: _ } => unreachable!(),
            HirEagerExprData::AssocRitchie { assoc_item_path } => {
                assoc_item_path.hir_defn(db).is_some()
            }
            _ => false,
        }
    }

    pub fn subtraces(&self, trace: Trace, db: &::salsa::Db) -> Vec<Trace> {
        let biological_parent_path = self.path;
        let biological_parent = trace;
        let sem_expr_idx = self.sem_expr_idx;
        let Some(hir_eager_expr_idx) = self.hir_eager_expr_idx else {
            return vec![];
        };
        let caller_sem_expr_region = self.sem_expr_region;
        let caller_sem_expr_region_data = caller_sem_expr_region.data(db);
        let hir_eager_expr_source_map_data = self.hir_eager_expr_source_map.data(db);
        match *self.hir_eager_expr_region.expr_arena(db)[hir_eager_expr_idx].data() {
            HirEagerExprData::FunctionRitchieCall { path, .. } => {
                let SemExprData::FunctionRitchieCall {
                    ref ritchie_parameter_argument_matches,
                    ..
                } = sem_expr_idx.data(caller_sem_expr_region_data.sem_expr_arena())
                else {
                    unreachable!()
                };
                let syn_decl = path.syn_decl(db).unwrap();
                let mut subtraces = fn_call_eager_expr_trace_input_traces(
                    biological_parent_path,
                    biological_parent,
                    ritchie_parameter_argument_matches,
                    caller_sem_expr_region,
                    hir_eager_expr_source_map_data,
                    syn_decl.syn_expr_region(db),
                    db,
                );
                subtraces.push(
                    Trace::new_eager_call(
                        biological_parent_path,
                        biological_parent,
                        path.into(),
                        db,
                    )
                    .into(),
                );
                subtraces
            }
            HirEagerExprData::AssocFunctionRitchieCall { path, .. } => {
                let SemExprData::FunctionRitchieCall {
                    ref ritchie_parameter_argument_matches,
                    ..
                } = sem_expr_idx.data(caller_sem_expr_region_data.sem_expr_arena())
                else {
                    unreachable!()
                };
                let syn_decl = path.syn_decl(db).unwrap();
                let mut subtraces = fn_call_eager_expr_trace_input_traces(
                    biological_parent_path,
                    biological_parent,
                    ritchie_parameter_argument_matches,
                    caller_sem_expr_region,
                    hir_eager_expr_source_map_data,
                    syn_decl.syn_expr_region(db),
                    db,
                );
                subtraces.push(
                    Trace::new_eager_call(
                        biological_parent_path,
                        biological_parent,
                        path.into(),
                        db,
                    )
                    .into(),
                );
                subtraces
            }
            HirEagerExprData::MethodRitchieCall { path, .. } => {
                let SemExprData::MethodRitchieCall {
                    ref ritchie_parameter_argument_matches,
                    ..
                } = sem_expr_idx.data(caller_sem_expr_region_data.sem_expr_arena())
                else {
                    unreachable!()
                };
                let syn_decl = path.syn_decl(db).unwrap();
                let mut subtraces = fn_call_eager_expr_trace_input_traces(
                    biological_parent_path,
                    biological_parent,
                    ritchie_parameter_argument_matches,
                    caller_sem_expr_region,
                    hir_eager_expr_source_map_data,
                    syn_decl.syn_expr_region(db),
                    db,
                );
                subtraces.push(
                    Trace::new_eager_call(
                        biological_parent_path,
                        biological_parent,
                        path.into(),
                        db,
                    )
                    .into(),
                );
                subtraces
            }
            HirEagerExprData::Block { .. } => unreachable!(),
            HirEagerExprData::AssocRitchie { assoc_item_path: _ } => todo!(),
            _ => vec![],
        }
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        self.biological_parent
            .var_deps_expansion(db)
            .expr_control_flow_var_deps_table(db)[self.sem_expr_idx]
            .clone()
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        self.biological_parent.var_deps_expansion(db)
    }

    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }
}

fn fn_call_eager_expr_trace_input_traces(
    trace_path: TracePath,
    trace: Trace,
    ritchie_parameter_argument_matches: &[SemRitchieArgument],
    caller_sem_expr_region: SemExprRegion,
    caller_hir_eager_expr_source_map_data: &HirEagerExprSourceMapData,
    callee_syn_expr_region: SynExprRegion,
    db: &::salsa::Db,
) -> Vec<Trace> {
    ritchie_parameter_argument_matches
        .iter()
        .map(|m| {
            let data = match m {
                SemRitchieArgument::Simple(_, list_item) => {
                    let sem_expr_idx = list_item.argument_sem_expr_idx();
                    EagerCallInputSketch::Simple {
                        argument_sem_expr_idx: sem_expr_idx,
                        argument_hir_eager_expr_idx: caller_hir_eager_expr_source_map_data
                            .sem_to_hir_eager_expr_idx(sem_expr_idx),
                    }
                }
                SemRitchieArgument::Variadic(_, _) => {
                    todo!()
                }
                SemRitchieArgument::Keyed(_, _) => {
                    todo!()
                }
            };
            Trace::new_eager_call_input(
                trace_path,
                trace,
                data,
                caller_sem_expr_region,
                callee_syn_expr_region,
                db,
            )
            .into()
        })
        .collect()
}

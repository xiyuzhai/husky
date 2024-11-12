pub mod eager_call;
pub mod eager_call_input;
pub mod eager_expr;
pub mod eager_loop_frame;
pub mod eager_loop_range;
pub mod eager_pattern;
pub mod eager_stmt;
pub mod lazy_call;
pub mod lazy_call_input;
pub mod lazy_expr;
pub mod lazy_loop_frame;
pub mod lazy_loop_range;
pub mod lazy_pattern;
pub mod lazy_stmt;
pub mod place;
pub mod script;
pub mod static_var;
pub mod submodule;
pub mod val;

use self::{
    eager_call::*, eager_call_input::*, eager_expr::*, eager_loop_frame::*, eager_loop_range::*,
    eager_pattern::*, eager_stmt::*, lazy_call::*, lazy_call_input::*, lazy_expr::*,
    lazy_loop_frame::*, lazy_loop_range::*, lazy_pattern::*, lazy_stmt::*, place::*, script::*,
    submodule::*, val::*,
};
use crate::{
    registry::trace_path::{TracePathDisambiguator, TracePathRegistry},
    *,
};
use husky_entity_kind::MajorFormKind;
use husky_entity_path::path::{
    major_item::{form::MajorFormPath, MajorItemPath},
    ItemPath, ItemPathId,
};
use husky_entity_tree::helpers::paths::module_item_paths;
use husky_entity_tree::helpers::tokra_region::HasRegionalTokenIdxBase;
use husky_item_path_interface::ItemPathIdInterface;
use husky_ki_repr::expansion::KiReprExpansion;
use husky_ki_repr::repr::KiRepr;
use husky_sem_expr::SemExprIdx;
use husky_syn_expr::{expr::*, pattern::*, region::*, stmt::*, variable::*};
use husky_trace_protocol::trace_id::TraceId;
use husky_trace_protocol::{
    protocol::{IsTrace, TraceBundle},
    trace_id::TraceKind,
    view::TraceViewData,
};
use husky_vfs::path::crate_path::CrateKind;
use husky_vfs::path::crate_path::CratePath;
use static_var::{StaticVarTraceData, StaticVarTracePathData};
use var_deps::TraceVarDepsExpansion;
use vec_like::VecPairMap;

#[salsa::interned(db = TraceDb, jar = TraceJar, constructor = new_inner)]
pub struct TracePath {
    #[return_ref]
    data: TracePathData,
}

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TracePathData {
    Submodule(SubmoduleTracePathData),
    ValItem(ValTracePathData),
    StaticVarItem(StaticVarTracePathData),
    LazyCallInput(LazyCallInputTracePathData),
    LazyCall(LazyCallTracePathData),
    LazyExpr(LazyExprTracePathData),
    LazyPattern(LazyPatternTracePathData),
    LazyStmt(LazyStmtTracePathData),
    LazyLoopFrame(LazyLoopFrameTracePathData),
    LazyLoopRange(LazyLoopRangeTracePathData),
    EagerCallInput(EagerCallInputTracePathData),
    EagerCall(EagerCallTracePathData),
    EagerExpr(EagerExprTracePathData),
    EagerPattern(EagerPatternTracePathData),
    EagerStmt(EagerStmtTracePathData),
    EagerLoopFrame(EagerLoopFrameTracePathData),
    EagerLoopRange(EagerLoopRangeTracePathData),
    Place(PlaceTracePathData),
    Script(ScriptTracePathData),
}

impl TracePath {
    fn new(data: impl Into<TracePathData>, db: &::salsa::Db) -> Self {
        Self::new_inner(db, data.into())
    }
}

#[salsa::tracked(db = TraceDb, jar = TraceJar, constructor = new_inner)]
pub struct Trace {
    #[id]
    pub path: TracePath,
    #[return_ref]
    pub data: TraceData,
}

impl From<TraceId> for Trace {
    fn from(id: TraceId) -> Self {
        unsafe { std::mem::transmute(id) }
    }
}

impl Into<TraceId> for Trace {
    fn into(self) -> TraceId {
        unsafe { std::mem::transmute(self) }
    }
}

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TraceData {
    Submodule(SubmoduleTraceData),
    Val(ValTraceData),
    StaticVar(StaticVarTraceData),
    LazyCallInput(LazyCallInputTraceData),
    LazyCall(LazyCallTraceData),
    LazyExpr(LazyExprTraceData),
    LazyPattern(LazyPatternTraceData),
    LazyStmt(LazyStmtTraceData),
    LazyLoopFrame(LazyLoopFrameTraceData),
    LazyLoopRange(LazyLoopRangeTraceData),
    EagerCallInput(EagerCallInputTraceData),
    EagerCall(EagerCallTraceData),
    EagerExpr(EagerExprTraceData),
    EagerPattern(EagerPatternTraceData),
    EagerStmt(EagerStmtTraceData),
    EagerLoopFrame(EagerLoopFrameTraceData),
    EagerLoopRange(EagerLoopRangeTraceData),
    Place(PlaceTraceData),
    Script(ScriptTraceData),
}

impl Trace {
    pub(crate) fn new(path: TracePath, data: TraceData, db: &::salsa::Db) -> Self {
        Self::new_inner(db, path.into(), data.into())
    }

    fn from_item_path(item_path: ItemPath, db: &::salsa::Db) -> Option<Self> {
        match item_path {
            ItemPath::Submodule(_, submodule_path) => {
                Trace::new_submodule(submodule_path, db).map(Into::into)
            }
            ItemPath::MajorItem(major_item_path) => Self::from_major_item_path(major_item_path, db),
            _ => None,
        }
    }

    fn from_major_item_path(major_item_path: MajorItemPath, db: &::salsa::Db) -> Option<Self> {
        match major_item_path {
            MajorItemPath::Form(form_path) => Self::from_form_path(form_path, db),
            _ => None,
        }
    }

    fn from_form_path(form_path: MajorFormPath, db: &::salsa::Db) -> Option<Self> {
        match form_path.kind(db) {
            MajorFormKind::Val => Some(Trace::from_major_val_form_path(form_path, db).into()),
            MajorFormKind::StaticVar => {
                Some(Trace::from_major_static_var_form_path(form_path, db).into())
            }
            MajorFormKind::Compterm
            | MajorFormKind::Ritchie(_)
            | MajorFormKind::TypeAlias
            | MajorFormKind::TypeVar
            | MajorFormKind::Conceptual => None,
            MajorFormKind::StaticMut => todo!(),
        }
    }
}

impl Trace {
    pub fn biological_parent(self, db: &::salsa::Db) -> Option<Trace> {
        self.data(db).biological_parent()
    }

    #[cfg(test)]
    fn assoc_traces(self, db: &::salsa::Db) -> Vec<Trace> {
        self.view_data(db)
            .assoc_trace_ids()
            .into_iter()
            .map(Into::into)
            .collect()
    }

    pub fn view_data(self, db: &::salsa::Db) -> TraceViewData {
        TraceViewData::new(
            self.trace_kind(db),
            trace_view_lines(db, self).data(),
            self.have_subtraces(db),
        )
    }

    pub fn trace_kind(self, db: &::salsa::Db) -> TraceKind {
        self.data(db).trace_kind()
    }

    pub fn have_subtraces(self, db: &::salsa::Db) -> bool {
        trace_have_subtraces(db, self)
    }

    pub fn subtraces(self, db: &::salsa::Db) -> &[Trace] {
        trace_subtraces(db, self)
    }

    pub fn ki_repr(self, db: &::salsa::Db) -> Option<KiRepr> {
        self.data(db).ki_repr(self, db)
    }

    pub fn ki_repr_expansion(self, db: &::salsa::Db) -> KiReprExpansion {
        trace_ki_repr_expansion(db, self)
    }

    pub fn var_deps(self, db: &::salsa::Db) -> &[ItemPathIdInterface] {
        trace_var_deps(db, self)
    }

    pub fn history_var_deps(self, db: &::salsa::Db) -> Option<&[ItemPathIdInterface]> {
        trace_history_var_deps(db, self)
            .as_ref()
            .map(|history_var_deps| history_var_deps as &[_])
    }

    pub fn var_deps_expansion(self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        trace_var_deps_expansion(db, self)
    }
}

impl TraceData {
    pub fn biological_parent(&self) -> Option<Trace> {
        match self {
            TraceData::Submodule(slf) => None,
            TraceData::Val(slf) => None,
            TraceData::StaticVar(slf) => None,
            TraceData::LazyCallInput(slf) => Some(slf.biological_parent()),
            TraceData::LazyCall(slf) => Some(slf.biological_parent()),
            TraceData::LazyExpr(slf) => Some(slf.biological_parent()),
            TraceData::LazyPattern(slf) => Some(slf.biological_parent()),
            TraceData::LazyStmt(slf) => Some(slf.biological_parent()),
            TraceData::LazyLoopFrame(slf) => Some(slf.biological_parent()),
            TraceData::LazyLoopRange(slf) => Some(slf.biological_parent()),
            TraceData::EagerCallInput(slf) => Some(slf.biological_parent()),
            TraceData::EagerCall(slf) => Some(slf.biological_parent()),
            TraceData::EagerExpr(slf) => Some(slf.biological_parent()),
            TraceData::EagerPattern(slf) => Some(slf.biological_parent()),
            TraceData::EagerStmt(slf) => Some(slf.biological_parent()),
            TraceData::EagerLoopFrame(slf) => Some(slf.biological_parent()),
            TraceData::EagerLoopRange(slf) => Some(slf.biological_parent()),
            TraceData::Place(slf) => Some(slf.biological_parent()),
            TraceData::Script(slf) => Some(slf.biological_parent()),
        }
    }

    pub fn trace_kind(&self) -> TraceKind {
        match self {
            TraceData::Submodule(_) => TraceKind::Submodule,
            TraceData::Val(_) => TraceKind::Val,
            TraceData::StaticVar(_) => TraceKind::StaticVar,
            TraceData::LazyCallInput(_) => TraceKind::LazyCallInput,
            TraceData::LazyCall(_) => TraceKind::LazyCall,
            TraceData::LazyExpr(_) => TraceKind::LazyExpr,
            TraceData::LazyPattern(_) => TraceKind::LazyPattern,
            TraceData::LazyStmt(_) => TraceKind::LazyStmt,
            TraceData::LazyLoopFrame(_) => TraceKind::LazyLoopFrame,
            TraceData::LazyLoopRange(_) => TraceKind::LazyLoopRange,
            TraceData::EagerCallInput(_) => TraceKind::EagerCallInput,
            TraceData::EagerCall(_) => TraceKind::EagerCall,
            TraceData::EagerExpr(_) => TraceKind::EagerExpr,
            TraceData::EagerPattern(_) => TraceKind::EagerPattern,
            TraceData::EagerStmt(_) => TraceKind::EagerStmt,
            TraceData::EagerLoopFrame(_) => TraceKind::EagerLoopFrame,
            TraceData::EagerLoopRange(_) => TraceKind::EagerLoopRange,
            TraceData::Place(_) => TraceKind::Value,
            TraceData::Script(_) => TraceKind::Repl,
        }
    }

    pub fn ki_repr(&self, trace_id: Trace, db: &::salsa::Db) -> Option<KiRepr> {
        match self {
            TraceData::Val(slf) => Some(slf.ki_repr(db)),
            TraceData::StaticVar(slf) => Some(slf.ki_repr(db)),
            TraceData::LazyExpr(slf) => slf.ki_repr(trace_id, db),
            TraceData::LazyPattern(slf) => slf.ki_repr(trace_id, db),
            TraceData::LazyCall(slf) => Some(slf.ki_repr(db)),
            TraceData::LazyCallInput(slf) => Some(slf.ki_repr(db)),
            TraceData::LazyStmt(slf) => slf.ki_repr(trace_id, db),
            TraceData::LazyLoopFrame(_) => todo!(),
            TraceData::LazyLoopRange(_) => todo!(),
            TraceData::Submodule(_) => None,
            TraceData::EagerExpr(_) => None,
            TraceData::EagerPattern(_) => None,
            TraceData::EagerCallInput(_) => None,
            TraceData::EagerCall(_) => None,
            TraceData::EagerStmt(_) => None,
            TraceData::EagerLoopFrame(_) => todo!(),
            TraceData::EagerLoopRange(_) => todo!(),
            TraceData::Place(_) => todo!(),
            TraceData::Script(_) => todo!(),
        }
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        match self {
            TraceData::Submodule(slf) => slf.var_deps(trace, db),
            TraceData::Val(slf) => slf.var_deps(trace, db),
            TraceData::StaticVar(slf) => slf.var_deps(trace, db),
            TraceData::LazyCallInput(slf) => slf.var_deps(trace, db),
            TraceData::LazyCall(slf) => slf.var_deps(trace, db),
            TraceData::LazyExpr(slf) => slf.var_deps(trace, db),
            TraceData::LazyPattern(slf) => slf.var_deps(trace, db),
            TraceData::LazyStmt(slf) => slf.var_deps(trace, db),
            TraceData::LazyLoopFrame(_) => todo!(),
            TraceData::LazyLoopRange(_) => todo!(),
            TraceData::EagerCallInput(slf) => slf.var_deps(trace, db),
            TraceData::EagerCall(slf) => slf.var_deps(trace, db),
            TraceData::EagerExpr(slf) => slf.var_deps(trace, db),
            TraceData::EagerPattern(slf) => slf.var_deps(trace, db),
            TraceData::EagerStmt(slf) => slf.var_deps(trace, db),
            TraceData::EagerLoopFrame(_) => todo!(),
            TraceData::EagerLoopRange(_) => todo!(),
            TraceData::Place(_) => todo!(),
            TraceData::Script(_) => todo!(),
        }
    }

    pub fn history_var_deps(&self, trace: Trace, db: &::salsa::Db) -> Option<TraceVarDeps> {
        match self {
            TraceData::Val(slf) => slf.history_var_deps(trace, db),
            TraceData::EagerCall(slf) => slf.history_var_deps(trace, db),
            TraceData::EagerLoopFrame(slf) => todo!(),
            TraceData::EagerLoopRange(slf) => todo!(),
            _ => None,
        }
    }

    fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        match self {
            TraceData::Submodule(slf) => slf.var_deps_expansion(db),
            TraceData::Val(slf) => slf.var_deps_expansion(db),
            TraceData::StaticVar(slf) => slf.var_deps_expansion(db),
            TraceData::LazyCallInput(slf) => slf.var_deps_expansion(db),
            TraceData::LazyCall(slf) => slf.var_deps_expansion(db),
            TraceData::LazyExpr(slf) => slf.var_deps_expansion(db),
            TraceData::LazyPattern(slf) => slf.var_deps_expansion(db),
            TraceData::LazyStmt(slf) => slf.var_deps_expansion(db),
            TraceData::LazyLoopFrame(_) => todo!(),
            TraceData::LazyLoopRange(_) => todo!(),
            TraceData::EagerCallInput(slf) => slf.var_deps_expansion(db),
            TraceData::EagerCall(slf) => slf.var_deps_expansion(db),
            TraceData::EagerExpr(slf) => slf.var_deps_expansion(db),
            TraceData::EagerPattern(slf) => slf.var_deps_expansion(db),
            TraceData::EagerStmt(slf) => slf.var_deps_expansion(db),
            TraceData::EagerLoopFrame(_) => todo!(),
            TraceData::EagerLoopRange(_) => todo!(),
            TraceData::Place(_) => todo!(),
            TraceData::Script(_) => todo!(),
        }
    }
}

#[salsa::tracked(jar = TraceJar)]
fn trace_view_lines(db: &::salsa::Db, trace_id: Trace) -> TraceViewLines {
    trace_id.data(db).view_lines(trace_id, db)
}

#[salsa::tracked(jar = TraceJar)]
fn trace_have_subtraces(db: &::salsa::Db, trace_id: Trace) -> bool {
    trace_id.data(db).have_subtraces(db)
}

#[salsa::tracked(jar = TraceJar, return_ref)]
fn trace_subtraces(db: &::salsa::Db, trace_id: Trace) -> Vec<Trace> {
    trace_id.data(db).subtraces(trace_id, db)
}

#[salsa::tracked(jar = TraceJar)]
fn trace_ki_repr_expansion(db: &::salsa::Db, trace_id: Trace) -> KiReprExpansion {
    trace_id.data(db).ki_repr_expansion(trace_id, db)
}

impl TraceData {
    fn view_lines(&self, trace_id: Trace, db: &::salsa::Db) -> TraceViewLines {
        match self {
            TraceData::Submodule(slf) => slf.view_lines(db),
            TraceData::Val(slf) => slf.view_lines(db),
            TraceData::StaticVar(slf) => slf.view_lines(db),
            TraceData::LazyCallInput(slf) => slf.view_lines(db),
            TraceData::LazyCall(slf) => slf.view_lines(db),
            TraceData::LazyExpr(slf) => slf.view_lines(db),
            TraceData::LazyPattern(slf) => slf.view_lines(db),
            TraceData::LazyStmt(slf) => slf.view_lines(trace_id, db),
            TraceData::LazyLoopFrame(_) => todo!(),
            TraceData::LazyLoopRange(_) => todo!(),
            TraceData::EagerCallInput(slf) => slf.view_lines(db),
            TraceData::EagerCall(slf) => slf.calc_view_lines(db),
            TraceData::EagerExpr(slf) => slf.view_lines(db),
            TraceData::EagerPattern(slf) => slf.view_lines(db),
            TraceData::EagerStmt(slf) => slf.view_lines(trace_id, db),
            TraceData::EagerLoopFrame(_) => todo!(),
            TraceData::EagerLoopRange(_) => todo!(),
            TraceData::Place(_) => todo!(),
            TraceData::Script(_) => todo!(),
        }
    }

    fn have_subtraces(&self, db: &::salsa::Db) -> bool {
        match self {
            TraceData::Submodule(slf) => slf.have_subtraces(),
            TraceData::Val(slf) => slf.have_subtraces(db),
            TraceData::StaticVar(slf) => slf.have_subtraces(db),
            TraceData::LazyCallInput(slf) => slf.have_subtraces(),
            TraceData::LazyCall(slf) => slf.have_subtraces(db),
            TraceData::LazyExpr(slf) => slf.have_subtraces(db),
            TraceData::LazyPattern(slf) => slf.have_subtraces(),
            TraceData::LazyStmt(slf) => slf.have_subtraces(db),
            TraceData::LazyLoopFrame(_) => todo!(),
            TraceData::LazyLoopRange(_) => todo!(),
            TraceData::EagerCallInput(slf) => slf.have_subtraces(db),
            TraceData::EagerCall(slf) => slf.have_subtraces(db),
            TraceData::EagerExpr(slf) => slf.have_subtraces(db),
            TraceData::EagerPattern(slf) => slf.have_subtraces(db),
            TraceData::EagerStmt(slf) => slf.have_subtraces(db),
            TraceData::EagerLoopFrame(_) => todo!(),
            TraceData::EagerLoopRange(_) => todo!(),
            TraceData::Place(_) => todo!(),
            TraceData::Script(_) => todo!(),
        }
    }

    fn subtraces(&self, trace_id: Trace, db: &::salsa::Db) -> Vec<Trace> {
        match self {
            TraceData::Submodule(slf) => slf.subtraces(db),
            TraceData::Val(slf) => slf.subtraces(trace_id, db),
            TraceData::StaticVar(slf) => slf.subtraces(trace_id, db),
            TraceData::LazyCallInput(slf) => slf.subtraces(),
            TraceData::LazyCall(slf) => slf.subtraces(trace_id, db),
            TraceData::LazyExpr(slf) => slf.subtraces(trace_id, db),
            TraceData::LazyPattern(slf) => slf.subtraces(),
            TraceData::LazyStmt(slf) => slf.subtraces(trace_id, db),
            TraceData::LazyLoopFrame(_) => todo!(),
            TraceData::LazyLoopRange(_) => todo!(),
            TraceData::EagerCallInput(slf) => slf.subtraces(),
            TraceData::EagerCall(slf) => slf.subtraces(trace_id, db),
            TraceData::EagerExpr(slf) => slf.subtraces(trace_id, db),
            TraceData::EagerPattern(slf) => slf.subtraces(),
            TraceData::EagerStmt(slf) => slf.subtraces(trace_id, db),
            TraceData::EagerLoopFrame(_) => todo!(),
            TraceData::EagerLoopRange(_) => todo!(),
            TraceData::Place(_) => todo!(),
            TraceData::Script(_) => todo!(),
        }
    }

    fn ki_repr_expansion(&self, trace: Trace, db: &::salsa::Db) -> KiReprExpansion {
        match self {
            TraceData::Submodule(_) => unreachable!("no subtraces, thus no expansion"),
            TraceData::Val(slf) => slf.ki_repr_expansion(trace, db),
            TraceData::StaticVar(slf) => unreachable!("no subtraces, thus no expansion"),
            TraceData::LazyCallInput(_) => todo!(),
            TraceData::LazyCall(_) => todo!(),
            TraceData::LazyExpr(slf) => slf.ki_repr_expansion(db),
            TraceData::LazyPattern(slf) => slf.ki_repr_expansion(db),
            TraceData::LazyStmt(slf) => slf.ki_repr_expansion(db),
            TraceData::LazyLoopFrame(_) => todo!(),
            TraceData::LazyLoopRange(_) => todo!(),
            TraceData::EagerCallInput(_) => todo!(),
            TraceData::EagerCall(_) => todo!(),
            TraceData::EagerExpr(_) => todo!(),
            TraceData::EagerPattern(_) => todo!(),
            TraceData::EagerStmt(_) => todo!(),
            TraceData::EagerLoopFrame(_) => todo!(),
            TraceData::EagerLoopRange(_) => todo!(),
            TraceData::Place(_) => todo!(),
            TraceData::Script(_) => todo!(),
        }
    }
}

impl IsTrace for Trace {}

#[salsa::tracked(jar = TraceJar, return_ref)]
fn root_traces(db: &::salsa::Db, crate_path: CratePath) -> Vec<Trace> {
    match crate_path.kind(db) {
        CrateKind::Lib | CrateKind::Main => (),
        CrateKind::Task | CrateKind::Requirements => return vec![],
        CrateKind::Bin(_) => todo!(),
        CrateKind::IntegratedTest(_) => todo!(),
        CrateKind::Example => todo!(),
    }
    let root_module_path = crate_path.root_module_path(db);
    module_item_paths(db, root_module_path)
        .iter()
        .filter_map(|&item_path| Trace::from_item_path(item_path, db))
        .collect()
}

/// the order is to put parent first
#[salsa::tracked(return_ref)]
pub fn trace_bundles(db: &::salsa::Db, target_path: CratePath) -> Vec<TraceBundle<Trace>> {
    use husky_manifest::manifest::HasManifest;
    target_path
        .package_path(db)
        .full_dependencies(db)
        .unwrap()
        .iter()
        .rev()
        .filter_map(|package_path| {
            let crate_path = package_path
                .lib_crate_path(db)
                .or(package_path.main_crate_path(db))
                .unwrap();
            let root_traces = root_traces(db, crate_path);
            if root_traces.is_empty() {
                return None;
            }
            Some(TraceBundle::new(
                crate_path.root_module_path(db).abs_path(db).unwrap(),
                root_traces.clone(),
            ))
        })
        .collect()
}

#[test]
fn root_traces_works() {
    DB::ast_rich_test_debug_with_db(
        |db, crate_path| root_traces(db, crate_path),
        &AstTestConfig::new(
            "root_traces",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::DEVTIME,
        ),
    )
}

// utility function for finding all traces under a crate within certain depth
#[cfg(test)]
fn find_traces<R>(
    crate_path: CratePath,
    max_depth: u8,
    db: &::salsa::Db,
    f: impl Fn(Trace) -> R,
) -> Vec<(Trace, R)> {
    match crate_path.kind(db) {
        CrateKind::Lib | CrateKind::Main => (),
        CrateKind::Task | CrateKind::Requirements => return vec![],
        CrateKind::Bin(_) => todo!(),
        CrateKind::IntegratedTest(_) => todo!(),
        CrateKind::Example => todo!(),
    }
    let mut traces: Vec<(Trace, R)> = vec![];
    for &root_trace in root_traces(db, crate_path) {
        find_traces_aux(root_trace, max_depth - 1, &f, &mut traces, db)
    }
    traces
}

#[cfg(test)]
fn find_traces_aux<R>(
    trace: Trace,
    max_depth: u8,
    f: &impl Fn(Trace) -> R,
    traces: &mut Vec<(Trace, R)>,
    db: &::salsa::Db,
) {
    traces.push((trace, f(trace)));
    if max_depth == 0 {
        return;
    }
    for &subtrace in trace.subtraces(db) {
        find_traces_aux(subtrace, max_depth - 1, f, traces, db)
    }
    for assoc_trace in trace.assoc_traces(db) {
        find_traces_aux(assoc_trace, max_depth - 1, f, traces, db)
    }
}

#[test]
fn find_traces_works() {
    DB::ast_rich_test_debug_with_db(
        |db, crate_path| find_traces(crate_path, 5, db, |_| ()),
        &AstTestConfig::new(
            "find_traces",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::DEVTIME,
        ),
    )
}

#[test]
fn trace_view_data_works() {
    DB::ast_rich_test_debug(
        |db, crate_path| find_traces(crate_path, 5, db, |trace| trace.view_data(db)),
        &AstTestConfig::new(
            "trace_view_data",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::DEVTIME,
        ),
    )
}

#[test]
fn trace_ki_repr_works() {
    DB::ast_rich_test_debug_with_db(
        |db, crate_path| find_traces(crate_path, 5, db, |trace| trace.ki_repr(db)),
        &AstTestConfig::new(
            "trace_ki_repr",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::DEVTIME,
        ),
    )
}

#[salsa::tracked(return_ref)]
fn trace_var_deps(db: &::salsa::Db, trace: Trace) -> TraceVarDeps {
    trace.data(db).var_deps(trace, db)
}

#[salsa::tracked(return_ref)]
fn trace_history_var_deps(db: &::salsa::Db, trace: Trace) -> Option<TraceVarDeps> {
    trace.data(db).history_var_deps(trace, db)
}

#[salsa::tracked]
fn trace_var_deps_expansion(db: &::salsa::Db, trace: Trace) -> TraceVarDepsExpansion {
    trace.data(db).var_deps_expansion(db)
}

#[test]
fn trace_var_deps_works() {
    DB::ast_rich_test_debug_with_db(
        |db, crate_path| {
            find_traces(crate_path, 5, db, |trace| {
                trace
                    .var_deps(db)
                    .iter()
                    .map(|&id_interface| {
                        let path_id: ItemPathId = id_interface.into();
                        path_id.item_path(db)
                    })
                    .collect::<Vec<_>>()
            })
        },
        &AstTestConfig::new(
            "trace_var_deps",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::DEVTIME,
        ),
    )
}

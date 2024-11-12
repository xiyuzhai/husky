use super::*;
use crate::registry::assoc_trace::IsAssocTraceRegistry;
use husky_entity_path::path::PrincipalEntityPath;
use husky_hir_eager_expr::{
    builder::hir_eager_expr_region_with_source_map,
    helpers::region::hir_eager_expr_source_map_from_sem, HirEagerExprIdx, HirEagerExprRegion,
    HirEagerExprSourceMap, HirEagerExprSourceMapData, HirEagerStmtIdx,
};
use husky_regional_token::{
    ElifRegionalToken, ElseRegionalToken, EolColonRegionalToken, EolRegionalToken, IfRegionalToken,
    RegionalTokenIdxRange, StmtForRegionalToken,
};
use husky_sem_expr::{
    helpers::range::sem_expr_range_region, stmt::condition::SemCondition, SemExprData, SemExprDb,
    SemExprRegion, SemStmtData, SemStmtIdx, SemStmtIdxRange,
};
use husky_syn_defn::ItemSynDefn;
use husky_token_info::TokenInfoSource;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct EagerStmtTracePathData {
    biological_parent_path: TracePath,
    essence: EagerStmtEssence,
    disambiguator: TracePathDisambiguator<EagerStmtEssence>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum EagerStmtEssence {
    Let,
    Return,
    Require,
    Assert,
    Break,
    Eval,
    IfBranch,
    ElifBranch { elif_branch_idx: u8 },
    ElseBranch,
    ForIn,
    ForBetween,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EagerStmtTraceData {
    pub path: TracePath,
    pub biological_parent: Trace,
    pub sem_stmt_idx: SemStmtIdx,
    pub hir_eager_stmt_idx: Option<HirEagerStmtIdx>,
    pub eager_stmt_sketch: EagerStmtSketch,
    #[skip_fmt]
    pub sem_expr_region: SemExprRegion,
    #[skip_fmt]
    pub hir_eager_expr_region: HirEagerExprRegion,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EagerStmtSketch {
    Let {
        initial_value: SemExprIdx,
        initial_value_hir_eager_expr_idx: Option<HirEagerExprIdx>,
    },
    Return {
        result: SemExprIdx,
    },
    Require {
        condition: SemCondition,
    },
    Assert {
        condition: SemCondition,
    },
    Break,
    Eval {
        expr: SemExprIdx,
    },
    IfBranch {
        if_regional_token: IfRegionalToken,
        eol_colon_regional_token: EolColonRegionalToken,
        stmts: SemStmtIdxRange,
    },
    ElifBranch {
        elif_branch_idx: u8,
        elif_regional_token: ElifRegionalToken,
        eol_colon_regional_token: EolColonRegionalToken,
        stmts: SemStmtIdxRange,
    },
    ElseBranch {
        else_regional_token: ElseRegionalToken,
        eol_colon_regional_token: EolColonRegionalToken,
        stmts: SemStmtIdxRange,
    },
    ForIn {
        for_regional_token: StmtForRegionalToken,
        eol_colon_regional_token: EolRegionalToken,
        stmts: SemStmtIdxRange,
    },
    ForBetween {
        for_regional_token: StmtForRegionalToken,
        eol_colon_regional_token: EolRegionalToken,
        stmts: SemStmtIdxRange,
    },
    Match {
        opd: SemExprIdx,
    },
    Narrate,
}

impl Trace {
    pub(crate) fn new_eager_stmt(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        essence: EagerStmtEssence,
        registry: &mut crate::registry::trace_path::TracePathRegistry<EagerStmtEssence>,
        sem_stmt_idx: SemStmtIdx,
        eager_stmt_sketch: EagerStmtSketch,
        sem_expr_region: SemExprRegion,
        db: &::salsa::Db,
    ) -> Self {
        let path = TracePath::new(
            EagerStmtTracePathData {
                biological_parent_path: biological_parent_path.into(),
                essence,
                disambiguator: registry.issue(essence),
            },
            db,
        );
        let (hir_eager_expr_region, hir_eager_expr_source_map) =
            hir_eager_expr_region_with_source_map(db, sem_expr_region);
        let hir_eager_stmt_idx = hir_eager_expr_source_map
            .data(db)
            .sem_to_hir_eager_stmt_idx(sem_stmt_idx);
        Trace::new(
            path,
            EagerStmtTraceData {
                path,
                biological_parent: biological_parent.into(),
                sem_stmt_idx,
                hir_eager_stmt_idx,
                eager_stmt_sketch,
                sem_expr_region,
                hir_eager_expr_region,
            }
            .into(),
            db,
        )
    }

    pub(crate) fn new_eager_stmts_from_syn_body_with_syn_expr_region(
        parent_trace_path: TracePath,
        parent_trace: Trace,
        syn_defn: Option<ItemSynDefn>,
        db: &::salsa::Db,
    ) -> Vec<Trace> {
        let Some(ItemSynDefn {
            body,
            syn_expr_region,
        }) = syn_defn
        else {
            return vec![];
        };
        let sem_expr_region = db.sem_expr_region(syn_expr_region);
        let sem_expr_region_data = sem_expr_region.data(db);
        let body = sem_expr_region_data.syn_root_to_sem_expr_idx(body);
        let SemExprData::Block { stmts } = *body.data(sem_expr_region_data.sem_expr_arena()) else {
            unreachable!()
        };
        Self::new_eager_stmts(parent_trace_path, parent_trace, stmts, sem_expr_region, db)
    }

    pub(crate) fn new_eager_stmts(
        parent_trace_path: TracePath,
        parent_trace: Trace,
        stmts: husky_sem_expr::SemStmtIdxRange,
        sem_expr_region: husky_sem_expr::SemExprRegion,
        db: &::salsa::Db,
    ) -> Vec<Trace> {
        let mut registry = TracePathRegistry::<EagerStmtEssence>::default();
        let mut subtraces: Vec<Trace> = vec![];
        let sem_stmt_arena = sem_expr_region.data(db).sem_stmt_arena();
        for stmt in stmts {
            match *stmt.data(sem_stmt_arena) {
                SemStmtData::Let { initial_value, .. } => {
                    let source_map = hir_eager_expr_source_map_from_sem(sem_expr_region, db);
                    let essence = EagerStmtEssence::Let {};
                    let eager_stmt_trace = Trace::new_eager_stmt(
                        parent_trace_path,
                        parent_trace,
                        essence,
                        &mut registry,
                        stmt,
                        EagerStmtSketch::Let {
                            initial_value,
                            initial_value_hir_eager_expr_idx: source_map
                                .data(db)
                                .sem_to_hir_eager_expr_idx(initial_value),
                        },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(eager_stmt_trace.into())
                }
                SemStmtData::Return { result, .. } => {
                    let essence = EagerStmtEssence::Return {};
                    let eager_stmt_trace = Trace::new_eager_stmt(
                        parent_trace_path,
                        parent_trace,
                        essence,
                        &mut registry,
                        stmt,
                        EagerStmtSketch::Return { result },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(eager_stmt_trace.into())
                }
                SemStmtData::Require { condition, .. } => {
                    let path_data = EagerStmtEssence::Require {};
                    let eager_stmt_trace = Trace::new_eager_stmt(
                        parent_trace_path,
                        parent_trace,
                        path_data,
                        &mut registry,
                        stmt,
                        EagerStmtSketch::Require { condition },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(eager_stmt_trace.into())
                }
                SemStmtData::Assert { condition, .. } => {
                    let path_data = EagerStmtEssence::Assert {};
                    let eager_stmt_trace = Trace::new_eager_stmt(
                        parent_trace_path,
                        parent_trace,
                        path_data,
                        &mut registry,
                        stmt,
                        EagerStmtSketch::Assert { condition },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(eager_stmt_trace.into())
                }
                SemStmtData::Break { .. } => {
                    let path_data = EagerStmtEssence::Break {};
                    let eager_stmt_trace = Trace::new_eager_stmt(
                        parent_trace_path,
                        parent_trace,
                        path_data,
                        &mut registry,
                        stmt,
                        EagerStmtSketch::Break,
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(eager_stmt_trace.into())
                }
                SemStmtData::Eval { expr, .. } => {
                    let path_data = EagerStmtEssence::Eval {};
                    let eager_stmt_trace = Trace::new_eager_stmt(
                        parent_trace_path,
                        parent_trace,
                        path_data,
                        &mut registry,
                        stmt,
                        EagerStmtSketch::Eval { expr },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(eager_stmt_trace.into())
                }
                SemStmtData::ForBetween {
                    for_token,
                    eol_colon,
                    stmts: block,
                    ..
                } => subtraces.push(
                    Trace::new_eager_stmt(
                        parent_trace_path,
                        parent_trace,
                        EagerStmtEssence::ForBetween,
                        &mut registry,
                        stmt,
                        EagerStmtSketch::ForBetween {
                            for_regional_token: for_token,
                            eol_colon_regional_token: eol_colon,
                            stmts: block,
                        },
                        sem_expr_region,
                        db,
                    )
                    .into(),
                ),
                SemStmtData::ForIn {
                    for_token,
                    range: _,
                    eol_colon,
                    stmts: block,
                } => subtraces.push(
                    Trace::new_eager_stmt(
                        parent_trace_path,
                        parent_trace,
                        EagerStmtEssence::ForIn,
                        &mut registry,
                        stmt,
                        EagerStmtSketch::ForIn {
                            for_regional_token: for_token,
                            eol_colon_regional_token: eol_colon,
                            stmts: block,
                        },
                        sem_expr_region,
                        db,
                    )
                    .into(),
                ),
                SemStmtData::Forext {
                    forext_token: _,
                    particulars: _,
                    eol_colon: _,
                    stmts: _,
                } => todo!(),
                SemStmtData::While {
                    while_token: _,
                    condition: _,
                    eol_colon: _,
                    stmts: _,
                } => todo!(),
                SemStmtData::DoWhile {
                    do_token: _,
                    while_token: _,
                    condition: _,
                    eol_colon: _,
                    stmts: _,
                } => todo!(),
                SemStmtData::IfElse {
                    ref if_branch,
                    ref elif_branches,
                    ref else_branch,
                } => {
                    subtraces.push(
                        Trace::new_eager_stmt(
                            parent_trace_path,
                            parent_trace,
                            EagerStmtEssence::IfBranch,
                            &mut registry,
                            stmt,
                            EagerStmtSketch::IfBranch {
                                if_regional_token: if_branch.if_token(),
                                eol_colon_regional_token: if_branch.eol_colon_token(),
                                stmts: if_branch.stmts(),
                            },
                            sem_expr_region,
                            db,
                        )
                        .into(),
                    );
                    for (elif_branch_idx, sem_elif_branch) in elif_branches.iter().enumerate() {
                        let elif_branch_idx = elif_branch_idx.try_into().unwrap();
                        subtraces.push(
                            Trace::new_eager_stmt(
                                parent_trace_path,
                                parent_trace,
                                EagerStmtEssence::ElifBranch { elif_branch_idx },
                                &mut registry,
                                stmt,
                                EagerStmtSketch::ElifBranch {
                                    elif_branch_idx,
                                    elif_regional_token: sem_elif_branch.elif_regional_token(),
                                    eol_colon_regional_token: sem_elif_branch.eol_colon_token(),
                                    stmts: sem_elif_branch.stmts(),
                                },
                                sem_expr_region,
                                db,
                            )
                            .into(),
                        );
                    }
                    if let Some(sem_else_branch) = else_branch {
                        subtraces.push(
                            Trace::new_eager_stmt(
                                parent_trace_path,
                                parent_trace,
                                EagerStmtEssence::ElseBranch,
                                &mut registry,
                                stmt,
                                EagerStmtSketch::ElseBranch {
                                    else_regional_token: sem_else_branch.else_regional_token(),
                                    eol_colon_regional_token: sem_else_branch
                                        .eol_colon_regional_token(),
                                    stmts: sem_else_branch.stmts(),
                                },
                                sem_expr_region,
                                db,
                            )
                            .into(),
                        );
                    }
                }
                SemStmtData::Match { .. } => todo!(),
                SemStmtData::Narrate { narrate_token } => todo!(),
            }
        }
        subtraces
    }
}

impl EagerStmtTraceData {
    pub fn view_lines(&self, trace_id: Trace, db: &::salsa::Db) -> TraceViewLines {
        let sem_stmt_idx = self.sem_stmt_idx;
        let sem_expr_region = self.sem_expr_region;
        let sem_expr_range_region = sem_expr_range_region(db, sem_expr_region);
        let region_path = sem_expr_region.path(db);
        let regional_token_idx_range = match self.eager_stmt_sketch {
            EagerStmtSketch::Let { .. }
            | EagerStmtSketch::Return { .. }
            | EagerStmtSketch::Require { .. }
            | EagerStmtSketch::Assert { .. }
            | EagerStmtSketch::Break
            | EagerStmtSketch::Eval { .. }
            | EagerStmtSketch::Narrate => sem_expr_range_region.data(db)[sem_stmt_idx],
            EagerStmtSketch::IfBranch {
                if_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                if_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
            EagerStmtSketch::ElifBranch {
                elif_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                elif_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
            EagerStmtSketch::ElseBranch {
                else_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                else_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
            EagerStmtSketch::ForBetween {
                for_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                for_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
            EagerStmtSketch::ForIn {
                for_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                for_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
            EagerStmtSketch::Match { .. } => todo!(),
        };
        let token_idx_range = regional_token_idx_range
            .token_idx_range(region_path.regional_token_idx_base(db).unwrap());
        let registry = EagerStmtAssocTraceRegistry::new(trace_id, sem_expr_region, db);
        TraceViewLines::new(region_path.module_path(db), token_idx_range, registry, db)
    }

    pub fn have_subtraces(&self, _db: &::salsa::Db) -> bool {
        match self.eager_stmt_sketch {
            EagerStmtSketch::Let { .. }
            | EagerStmtSketch::Return { .. }
            | EagerStmtSketch::Require { .. }
            | EagerStmtSketch::Assert { .. }
            | EagerStmtSketch::Break
            | EagerStmtSketch::Eval { .. }
            | EagerStmtSketch::Narrate => false,
            EagerStmtSketch::IfBranch { .. } => true,
            EagerStmtSketch::ElifBranch { .. } => true,
            EagerStmtSketch::ElseBranch { .. } => true,
            EagerStmtSketch::ForBetween { .. } => true,
            EagerStmtSketch::ForIn { .. } => true,
            EagerStmtSketch::Match { .. } => true,
        }
    }

    pub fn subtraces(&self, trace: Trace, db: &::salsa::Db) -> Vec<Trace> {
        match self.eager_stmt_sketch {
            EagerStmtSketch::Let { .. }
            | EagerStmtSketch::Return { .. }
            | EagerStmtSketch::Require { .. }
            | EagerStmtSketch::Assert { .. }
            | EagerStmtSketch::Break
            | EagerStmtSketch::Eval { .. }
            | EagerStmtSketch::Narrate => vec![],
            EagerStmtSketch::IfBranch { stmts, .. }
            | EagerStmtSketch::ElifBranch { stmts, .. }
            | EagerStmtSketch::ElseBranch { stmts, .. }
            | EagerStmtSketch::ForIn { stmts, .. }
            | EagerStmtSketch::ForBetween { stmts, .. } => {
                Trace::new_eager_stmts(self.path, trace, stmts, self.sem_expr_region, db)
            }
            EagerStmtSketch::Match { .. } => todo!(),
        }
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        match self.eager_stmt_sketch {
            EagerStmtSketch::Let { initial_value, .. } => self
                .biological_parent
                .var_deps_expansion(db)
                .expr_control_flow_var_deps(initial_value, db)
                .clone(),
            _ => self
                .biological_parent
                .var_deps_expansion(db)
                .stmt_control_flow_var_deps(self.sem_stmt_idx, db)
                .clone(),
        }
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        self.biological_parent.var_deps_expansion(db)
    }

    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }

    pub fn eager_stmt_sketch(&self) -> EagerStmtSketch {
        self.eager_stmt_sketch
    }
}

struct EagerStmtAssocTraceRegistry<'a> {
    parent_trace: Trace,
    sem_expr_region: SemExprRegion,
    hir_eager_expr_region: HirEagerExprRegion,
    syn_expr_region_data: &'a SynExprRegionData,
    hir_eager_expr_source_map: HirEagerExprSourceMap,
    hir_eager_expr_source_map_data: &'a HirEagerExprSourceMapData,
    eager_expr_trace_path_registry: TracePathRegistry<EagerExprEssence>,
    eager_expr_traces_issued: VecPairMap<SemExprIdx, Trace>,
    eager_pattern_trace_path_registry: TracePathRegistry<EagerPatternEssence>,
    eager_pattern_traces_issued: VecPairMap<SynPatternIdx, Trace>,
}

impl<'a> EagerStmtAssocTraceRegistry<'a> {
    fn new(parent_trace: Trace, sem_expr_region: SemExprRegion, db: &'a ::salsa::Db) -> Self {
        let (hir_eager_expr_region, hir_eager_expr_source_map) =
            hir_eager_expr_region_with_source_map(db, sem_expr_region);
        EagerStmtAssocTraceRegistry {
            parent_trace,
            sem_expr_region,
            syn_expr_region_data: sem_expr_region.syn_expr_region(db).data(db),
            hir_eager_expr_region,
            hir_eager_expr_source_map,
            hir_eager_expr_source_map_data: hir_eager_expr_source_map.data(db),
            eager_expr_trace_path_registry: Default::default(),
            eager_expr_traces_issued: Default::default(),
            eager_pattern_trace_path_registry: Default::default(),
            eager_pattern_traces_issued: Default::default(),
        }
    }
}

impl<'a> IsAssocTraceRegistry for EagerStmtAssocTraceRegistry<'a> {
    fn get_or_issue_assoc_trace(
        &mut self,
        source: TokenInfoSource,
        db: &::salsa::Db,
    ) -> Option<Trace> {
        match source {
            TokenInfoSource::UseExpr(_) => None,
            TokenInfoSource::SemExpr(_, expr) => Some(
                self.eager_expr_traces_issued
                    .get_value_copied_or_insert_with(expr, || {
                        let hir_eager_expr_idx = self
                            .hir_eager_expr_source_map_data
                            .sem_to_hir_eager_expr_idx(expr);
                        Trace::new_eager_expr(
                            self.parent_trace.path(db),
                            self.parent_trace,
                            expr,
                            hir_eager_expr_idx,
                            self.sem_expr_region,
                            self.hir_eager_expr_region,
                            self.hir_eager_expr_source_map,
                            &mut self.eager_expr_trace_path_registry,
                            db,
                        )
                    })
                    .into(),
            ),
            TokenInfoSource::SynPrincipalEntityPathExpr(
                _syn_principal_entity_path_expr_idx,
                syn_principal_entity_path,
            ) => match syn_principal_entity_path {
                PrincipalEntityPath::Module(_) => None,
                PrincipalEntityPath::MajorItem(major_item_path) => {
                    Trace::from_major_item_path(major_item_path, db)
                }
                PrincipalEntityPath::TypeVariant(_) => None,
            },
            TokenInfoSource::Pattern(_, pattern) => Some(
                self.eager_pattern_traces_issued
                    .get_value_copied_or_insert_with(pattern, || {
                        Trace::new_eager_pattern(
                            self.parent_trace.path(db),
                            self.parent_trace,
                            pattern,
                            self.syn_expr_region_data
                                .syn_pattern_current_variables_mapped(
                                    pattern,
                                    |current_variable_idx| {
                                        self.hir_eager_expr_source_map_data
                                            .current_variable_to_hir_eager_runtime_variable(
                                                current_variable_idx,
                                            )
                                    },
                                ),
                            self.sem_expr_region,
                            &mut self.eager_pattern_trace_path_registry,
                            db,
                        )
                    })
                    .into(),
            ),
            TokenInfoSource::TemplateParameter(_) => None,
            TokenInfoSource::AstIdentifiable => None,
        }
    }
}

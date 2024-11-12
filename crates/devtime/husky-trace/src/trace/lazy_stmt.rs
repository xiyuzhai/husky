use super::*;
use crate::registry::{
    assoc_trace::IsAssocTraceRegistry,
    trace_path::{TracePathDisambiguator, TracePathRegistry},
};
use husky_entity_path::path::PrincipalEntityPath;
use husky_hir_lazy_expr::{
    builder::hir_lazy_expr_region_with_source_map, helpers::hir_lazy_expr_source_map_from_sem,
    source_map::HirLazyExprSourceMap, HirLazyExprIdx, HirLazyExprRegion,
};
use husky_hir_lazy_expr::{source_map::HirLazyExprSourceMapData, HirLazyStmtIdx};
use husky_ki_repr::expansion::KiReprExpansion;
use husky_regional_token::{
    ElifRegionalToken, ElseRegionalToken, EolColonRegionalToken, EolRegionalToken, IfRegionalToken,
    NarrateRegionalToken, RegionalTokenIdxRange, StmtForRegionalToken,
};
use husky_sem_expr::{
    helpers::range::sem_expr_range_region, stmt::condition::SemCondition, SemExprData, SemExprDb,
    SemExprIdx, SemExprRegion, SemStmtData, SemStmtIdx, SemStmtIdxRange,
};
use husky_syn_defn::ItemSynDefn;
use husky_token_info::TokenInfoSource;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LazyStmtTracePathData {
    biological_parent_path: TracePath,
    essence: LazyStmtEssence,
    disambiguator: TracePathDisambiguator<LazyStmtEssence>,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum LazyStmtEssence {
    Let,
    Return,
    Require,
    Assert,
    Break,
    Eval,
    IfBranch,
    ElifBranch { elif_branch_idx: u8 },
    ElseBranch,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LazyStmtTraceData {
    path: TracePath,
    biological_parent: Trace,
    sem_stmt_idx: SemStmtIdx,
    hir_lazy_stmt_idx: Option<HirLazyStmtIdx>,
    lazy_stmt_sketch: LazyStmtSketch,
    #[skip_fmt]
    sem_expr_region: SemExprRegion,
    #[skip_fmt]
    hir_lazy_expr_region: HirLazyExprRegion,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LazyStmtSketch {
    Let {
        initial_value: SemExprIdx,
        initial_value_hir_lazy_expr_idx: Option<HirLazyExprIdx>,
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
    Narrate {
        narrate_token: NarrateRegionalToken,
    },
}

impl Trace {
    pub(crate) fn new_lazy_stmt(
        biological_parent_path: TracePath,
        biological_parent: Trace,
        essence: LazyStmtEssence,
        registry: &mut crate::registry::trace_path::TracePathRegistry<LazyStmtEssence>,
        sem_stmt_idx: SemStmtIdx,
        lazy_stmt_sketch: LazyStmtSketch,
        sem_expr_region: SemExprRegion,
        db: &::salsa::Db,
    ) -> Self {
        let path = TracePath::new(
            LazyStmtTracePathData {
                biological_parent_path: biological_parent_path.into(),
                essence,
                disambiguator: registry.issue(essence),
            },
            db,
        );
        let (hir_lazy_expr_region, hir_lazy_expr_source_map) =
            hir_lazy_expr_region_with_source_map(db, sem_expr_region);
        let hir_lazy_stmt_idx = hir_lazy_expr_source_map
            .data(db)
            .sem_to_hir_lazy_stmt_idx(sem_stmt_idx);
        Trace::new(
            path,
            LazyStmtTraceData {
                path,
                biological_parent: biological_parent.into(),
                sem_stmt_idx,
                hir_lazy_stmt_idx,
                lazy_stmt_sketch,
                sem_expr_region,
                hir_lazy_expr_region,
            }
            .into(),
            db,
        )
    }
}

impl LazyStmtTraceData {
    pub fn biological_parent(&self) -> Trace {
        self.biological_parent
    }

    pub fn view_lines(&self, trace: Trace, db: &::salsa::Db) -> TraceViewLines {
        let sem_stmt_idx = self.sem_stmt_idx;
        let sem_expr_region = self.sem_expr_region;
        let sem_expr_range_region = sem_expr_range_region(db, sem_expr_region);
        let region_path = sem_expr_region.path(db);
        let regional_token_idx_range = match self.lazy_stmt_sketch {
            LazyStmtSketch::Let { .. }
            | LazyStmtSketch::Return { .. }
            | LazyStmtSketch::Require { .. }
            | LazyStmtSketch::Assert { .. }
            | LazyStmtSketch::Break
            | LazyStmtSketch::Eval { .. }
            | LazyStmtSketch::Match { .. }
            | LazyStmtSketch::Narrate { .. } => sem_expr_range_region.data(db)[sem_stmt_idx],
            LazyStmtSketch::IfBranch {
                if_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                if_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
            LazyStmtSketch::ElifBranch {
                elif_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                elif_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
            LazyStmtSketch::ElseBranch {
                else_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                else_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
            LazyStmtSketch::ForIn {
                for_regional_token,
                eol_colon_regional_token,
                ..
            }
            | LazyStmtSketch::ForBetween {
                for_regional_token,
                eol_colon_regional_token,
                ..
            } => RegionalTokenIdxRange::new_closed(
                for_regional_token.regional_token_idx(),
                eol_colon_regional_token.regional_token_idx(),
            ),
        };
        let token_idx_range = regional_token_idx_range
            .token_idx_range(region_path.regional_token_idx_base(db).unwrap());
        let registry = LazyStmtAssocTraceRegistry::new(self.path, trace, sem_expr_region, db);
        TraceViewLines::new(region_path.module_path(db), token_idx_range, registry, db)
    }

    pub fn have_subtraces(&self, _db: &::salsa::Db) -> bool {
        match self.lazy_stmt_sketch {
            LazyStmtSketch::Let { .. }
            | LazyStmtSketch::Return { .. }
            | LazyStmtSketch::Require { .. }
            | LazyStmtSketch::Assert { .. }
            | LazyStmtSketch::Break
            | LazyStmtSketch::Eval { .. }
            | LazyStmtSketch::Narrate { .. } => false,
            LazyStmtSketch::IfBranch { .. }
            | LazyStmtSketch::ElifBranch { .. }
            | LazyStmtSketch::ElseBranch { .. }
            | LazyStmtSketch::ForIn { .. }
            | LazyStmtSketch::ForBetween { .. }
            | LazyStmtSketch::Match { .. } => true,
        }
    }

    pub fn subtraces(&self, trace_id: Trace, db: &::salsa::Db) -> Vec<Trace> {
        let biological_parent_path = self.path;
        let biological_parent = trace_id;
        match self.lazy_stmt_sketch {
            LazyStmtSketch::Let { .. }
            | LazyStmtSketch::Return { .. }
            | LazyStmtSketch::Require { .. }
            | LazyStmtSketch::Assert { .. }
            | LazyStmtSketch::Break
            | LazyStmtSketch::Eval { .. }
            | LazyStmtSketch::Narrate { .. } => vec![],
            LazyStmtSketch::IfBranch { stmts, .. }
            | LazyStmtSketch::ElifBranch { stmts, .. }
            | LazyStmtSketch::ElseBranch { stmts, .. }
            | LazyStmtSketch::ForIn { stmts, .. }
            | LazyStmtSketch::ForBetween { stmts, .. } => Trace::new_lazy_stmts(
                biological_parent_path,
                biological_parent,
                stmts,
                self.sem_expr_region,
                db,
            ),
            LazyStmtSketch::Match { .. } => todo!(), // Implement match subtraces
        }
    }

    pub fn ki_repr(&self, trace: Trace, db: &::salsa::Db) -> Option<KiRepr> {
        let ki_repr_expansion = trace_ki_repr_expansion(db, trace);
        match self.lazy_stmt_sketch {
            LazyStmtSketch::Let {
                initial_value_hir_lazy_expr_idx,
                ..
            } => ki_repr_expansion
                .hir_lazy_expr_ki_repr_map(db)
                .get(initial_value_hir_lazy_expr_idx?)
                .copied(),
            _ => ki_repr_expansion
                .hir_lazy_stmt_ki_repr_map(db)
                .get(self.hir_lazy_stmt_idx?)
                .copied(),
        }
    }

    pub fn ki_repr_expansion(&self, db: &::salsa::Db) -> KiReprExpansion {
        // todo: handle loops
        self.biological_parent.ki_repr_expansion(db)
    }

    pub fn var_deps(&self, trace: Trace, db: &::salsa::Db) -> TraceVarDeps {
        match self.lazy_stmt_sketch {
            LazyStmtSketch::Let { initial_value, .. } => self
                .var_deps_expansion(db)
                .expr_control_flow_var_deps(initial_value, db)
                .clone(),
            _ => self
                .var_deps_expansion(db)
                .stmt_control_flow_var_deps(self.sem_stmt_idx, db)
                .clone(),
        }
    }

    pub fn var_deps_expansion(&self, db: &::salsa::Db) -> TraceVarDepsExpansion {
        self.biological_parent.var_deps_expansion(db)
    }

    pub fn lazy_stmt_sketch(&self) -> LazyStmtSketch {
        self.lazy_stmt_sketch
    }
}

struct LazyStmtAssocTraceRegistry<'a> {
    biological_parent_path: TracePath,
    biological_parent: Trace,
    sem_expr_region: SemExprRegion,
    hir_lazy_expr_region: HirLazyExprRegion,
    syn_expr_region_data: &'a SynExprRegionData,
    hir_lazy_expr_source_map: HirLazyExprSourceMap,
    hir_lazy_expr_source_map_data: &'a HirLazyExprSourceMapData,
    lazy_expr_trace_path_registry: TracePathRegistry<LazyExprEssence>,
    lazy_expr_traces_issued: VecPairMap<SemExprIdx, Trace>,
    lazy_pattern_trace_path_registry: TracePathRegistry<LazyPatternEssence>,
    lazy_pattern_traces_issued: VecPairMap<SynPatternIdx, Trace>,
}

impl<'a> LazyStmtAssocTraceRegistry<'a> {
    fn new(
        parent_trace_path: TracePath,
        parent_trace: Trace,
        sem_expr_region: SemExprRegion,
        db: &'a ::salsa::Db,
    ) -> Self {
        let (hir_lazy_expr_region, hir_lazy_expr_source_map) =
            hir_lazy_expr_region_with_source_map(db, sem_expr_region);
        LazyStmtAssocTraceRegistry {
            biological_parent_path: parent_trace_path,
            biological_parent: parent_trace,
            sem_expr_region,
            hir_lazy_expr_region,
            syn_expr_region_data: sem_expr_region.syn_expr_region(db).data(db),
            hir_lazy_expr_source_map,
            hir_lazy_expr_source_map_data: hir_lazy_expr_source_map.data(db),
            lazy_expr_trace_path_registry: Default::default(),
            lazy_expr_traces_issued: Default::default(),
            lazy_pattern_trace_path_registry: Default::default(),
            lazy_pattern_traces_issued: Default::default(),
        }
    }
}

impl<'a> IsAssocTraceRegistry for LazyStmtAssocTraceRegistry<'a> {
    fn get_or_issue_assoc_trace(
        &mut self,
        source: TokenInfoSource,
        db: &::salsa::Db,
    ) -> Option<Trace> {
        match source {
            TokenInfoSource::UseExpr(_) => None,
            TokenInfoSource::SemExpr(_, expr) => Some(
                self.lazy_expr_traces_issued
                    .get_value_copied_or_insert_with(expr, || {
                        let hir_lazy_expr_idx = self
                            .hir_lazy_expr_source_map_data
                            .sem_to_hir_lazy_expr_idx(expr);
                        Trace::new_lazy_expr(
                            self.biological_parent_path,
                            self.biological_parent,
                            expr,
                            hir_lazy_expr_idx,
                            self.sem_expr_region,
                            self.hir_lazy_expr_region,
                            self.hir_lazy_expr_source_map,
                            &mut self.lazy_expr_trace_path_registry,
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
                self.lazy_pattern_traces_issued
                    .get_value_copied_or_insert_with(pattern, || {
                        Trace::new_lazy_pattern(
                            self.biological_parent_path,
                            self.biological_parent,
                            pattern,
                            self.hir_lazy_expr_source_map_data
                                .syn_to_hir_lazy_pattern_idx(pattern),
                            self.syn_expr_region_data
                                .syn_pattern_current_variables_mapped(
                                    pattern,
                                    |current_variable_idx| {
                                        self.hir_lazy_expr_source_map_data
                                            .current_to_hir_lazy_variable(current_variable_idx)
                                    },
                                ),
                            self.sem_expr_region,
                            self.hir_lazy_expr_region,
                            &mut self.lazy_pattern_trace_path_registry,
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

impl Trace {
    pub(crate) fn new_lazy_stmts_from_syn_body_with_syn_expr_region(
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
        Self::new_lazy_stmts(parent_trace_path, parent_trace, stmts, sem_expr_region, db)
    }

    pub(crate) fn new_lazy_stmts(
        parent_trace_path: TracePath,
        parent_trace: Trace,
        stmts: husky_sem_expr::SemStmtIdxRange,
        sem_expr_region: husky_sem_expr::SemExprRegion,
        db: &::salsa::Db,
    ) -> Vec<Trace> {
        let mut registry = TracePathRegistry::<LazyStmtEssence>::default();
        let mut subtraces: Vec<Trace> = vec![];
        let sem_stmt_arena = sem_expr_region.data(db).sem_stmt_arena();
        for stmt in stmts {
            match *stmt.data(sem_stmt_arena) {
                SemStmtData::Let { initial_value, .. } => {
                    let source_map = hir_lazy_expr_source_map_from_sem(sem_expr_region, db);
                    let essence = LazyStmtEssence::Let {};
                    let lazy_stmt_trace = Trace::new_lazy_stmt(
                        parent_trace_path,
                        parent_trace,
                        essence,
                        &mut registry,
                        stmt,
                        LazyStmtSketch::Let {
                            initial_value,
                            initial_value_hir_lazy_expr_idx: source_map
                                .data(db)
                                .sem_to_hir_lazy_expr_idx(initial_value),
                        },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(lazy_stmt_trace.into())
                }
                SemStmtData::Return { result, .. } => {
                    let essence = LazyStmtEssence::Return {};
                    let lazy_stmt_trace = Trace::new_lazy_stmt(
                        parent_trace_path,
                        parent_trace,
                        essence,
                        &mut registry,
                        stmt,
                        LazyStmtSketch::Return { result },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(lazy_stmt_trace.into())
                }
                SemStmtData::Require { condition, .. } => {
                    let essence = LazyStmtEssence::Require {};
                    let lazy_stmt_trace = Trace::new_lazy_stmt(
                        parent_trace_path,
                        parent_trace,
                        essence,
                        &mut registry,
                        stmt,
                        LazyStmtSketch::Require { condition },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(lazy_stmt_trace.into())
                }
                SemStmtData::Assert { condition, .. } => {
                    let path_data = LazyStmtEssence::Assert {};
                    let lazy_stmt_trace = Trace::new_lazy_stmt(
                        parent_trace_path,
                        parent_trace,
                        path_data,
                        &mut registry,
                        stmt,
                        LazyStmtSketch::Assert { condition },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(lazy_stmt_trace.into())
                }
                SemStmtData::Break { .. } => {
                    let path_data = LazyStmtEssence::Break {};
                    let lazy_stmt_trace = Trace::new_lazy_stmt(
                        parent_trace_path,
                        parent_trace,
                        path_data,
                        &mut registry,
                        stmt,
                        LazyStmtSketch::Break,
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(lazy_stmt_trace.into())
                }
                SemStmtData::Eval { expr, .. } => {
                    let path_data = LazyStmtEssence::Eval {};
                    let lazy_stmt_trace = Trace::new_lazy_stmt(
                        parent_trace_path,
                        parent_trace,
                        path_data,
                        &mut registry,
                        stmt,
                        LazyStmtSketch::Eval { expr },
                        sem_expr_region,
                        db,
                    );
                    subtraces.push(lazy_stmt_trace.into())
                }
                SemStmtData::ForBetween {
                    for_token: _,
                    particulars: _,
                    for_loop_varible_idx: _,
                    eol_colon: _,
                    stmts: _,
                } => todo!(),
                SemStmtData::ForIn {
                    for_token: _,
                    range: _,
                    eol_colon: _,
                    stmts: _,
                } => todo!(),
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
                        Trace::new_lazy_stmt(
                            parent_trace_path,
                            parent_trace,
                            LazyStmtEssence::IfBranch,
                            &mut registry,
                            stmt,
                            LazyStmtSketch::IfBranch {
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
                            Trace::new_lazy_stmt(
                                parent_trace_path,
                                parent_trace,
                                LazyStmtEssence::ElifBranch { elif_branch_idx },
                                &mut registry,
                                stmt,
                                LazyStmtSketch::ElifBranch {
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
                            Trace::new_lazy_stmt(
                                parent_trace_path,
                                parent_trace,
                                LazyStmtEssence::ElseBranch,
                                &mut registry,
                                stmt,
                                LazyStmtSketch::ElseBranch {
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

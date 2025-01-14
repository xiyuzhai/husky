use crate::{
    destroyer::{VmirDestroyerArena, VmirDestroyerData, VmirDestroyerIdxRange},
    expr::{VmirExprArena, VmirExprData, VmirExprIdx, VmirExprIdxRange},
    pattern::{
        destructive::{
            VmirDestructivePatternArena, VmirDestructivePatternData, VmirDestructivePatternIdx,
            VmirDestructivePatternIdxRange,
        },
        restructive::{
            VmirRestructivePatternArena, VmirRestructivePatternData, VmirRestructivePatternIdx,
            VmirRestructivePatternIdxRange,
        },
    },
    region::VmirRegion,
    stmt::{VmirStmtArena, VmirStmtData, VmirStmtIdx},
};
use husky_hir_eager_expr::{
    variable::runtime::HirEagerRuntimeVariableRegionData, HirEagerExprArena, HirEagerExprIdx,
    HirEagerExprMap, HirEagerPatternArena, HirEagerStmtArena, HirEagerStmtIdx,
    HirEagerStmtIdxRange, HirEagerStmtMap,
};
use husky_hir_expr::{HirExprIdx, HirExprRegion};
use husky_linket::{instantiation::LinInstantiation, linket::Linket};
use husky_linktime::IsLinktime;
use idx_arena::{ArenaIdx, ArenaIdxRange};

pub(crate) struct VmirBuilder<'comptime, Linktime: IsLinktime> {
    db: &'comptime ::salsa::Db,
    hir_eager_expr_arena: &'comptime HirEagerExprArena,
    hir_eager_stmt_arena: &'comptime HirEagerStmtArena,
    hir_eager_pattern_arena: &'comptime HirEagerPatternArena,
    hir_eager_runtime_variable_region_data: &'comptime HirEagerRuntimeVariableRegionData,
    instantiation: &'comptime LinInstantiation,
    linktime: &'comptime Linktime,
    vmir_expr_arena: VmirExprArena<Linktime::LinketImpl>,
    vmir_stmt_arena: VmirStmtArena<Linktime::LinketImpl>,
    vmir_restructive_pattern_arena: VmirRestructivePatternArena<Linktime::LinketImpl>,
    vmir_destructive_pattern_arena: VmirDestructivePatternArena<Linktime::LinketImpl>,
    vmir_destroyer_arena: VmirDestroyerArena,
    hir_eager_to_vmir_expr_map: HirEagerExprMap<VmirExprIdx<Linktime::LinketImpl>>,
    hir_eager_to_vmir_stmt_map: HirEagerStmtMap<VmirStmtIdx<Linktime::LinketImpl>>,
}

/// # constructor
impl<'db, Linktime: IsLinktime> VmirBuilder<'db, Linktime> {
    pub(crate) fn new(
        linket: Linket,
        db: &'db ::salsa::Db,
        linktime: &'db Linktime,
    ) -> Option<(HirEagerExprIdx, Self)> {
        use husky_hir_defn::defn::HasHirDefn;

        let (path, instantiation) = linket.path_and_instantiation_for_definition(db)?;
        let hir_defn = path.hir_defn(db).unwrap();
        let (HirExprIdx::Eager(body), HirExprRegion::Eager(hir_eager_expr_region)) =
            hir_defn.hir_expr_body_and_region(db)?
        else {
            return None;
        };
        let hir_eager_expr_arena = hir_eager_expr_region.expr_arena(db);
        let hir_eager_stmt_arena = hir_eager_expr_region.stmt_arena(db);
        let hir_eager_runtime_variable_region_data =
            hir_eager_expr_region.runtime_variable_region_data(db);
        Some((
            body,
            Self {
                db,
                hir_eager_expr_arena,
                hir_eager_stmt_arena,
                hir_eager_pattern_arena: hir_eager_expr_region.pattern_arena(db),
                hir_eager_runtime_variable_region_data,
                instantiation,
                linktime,
                vmir_expr_arena: Default::default(),
                vmir_stmt_arena: Default::default(),
                vmir_restructive_pattern_arena: Default::default(),
                vmir_destructive_pattern_arena: Default::default(),
                vmir_destroyer_arena: Default::default(),
                hir_eager_to_vmir_expr_map: HirEagerExprMap::new(hir_eager_expr_arena),
                hir_eager_to_vmir_stmt_map: HirEagerStmtMap::new(hir_eager_stmt_arena),
            },
        ))
    }
}

/// # getters
impl<'comptime, Linktime: IsLinktime> VmirBuilder<'comptime, Linktime> {
    pub(crate) fn db(&self) -> &'comptime ::salsa::Db {
        self.db
    }

    pub(crate) fn hir_eager_expr_arena(&self) -> &'comptime HirEagerExprArena {
        self.hir_eager_expr_arena
    }

    pub(crate) fn hir_eager_stmt_arena(&self) -> &'comptime HirEagerStmtArena {
        self.hir_eager_stmt_arena
    }

    pub(crate) fn hir_eager_pattern_arena(&self) -> &'comptime HirEagerPatternArena {
        self.hir_eager_pattern_arena
    }

    pub(crate) fn hir_eager_runtime_variable_region_data(
        &self,
    ) -> &'comptime HirEagerRuntimeVariableRegionData {
        self.hir_eager_runtime_variable_region_data
    }

    pub(crate) fn lin_instantiation(&self) -> &'comptime LinInstantiation {
        self.instantiation
    }

    pub(crate) fn linket_impl(&self, linket: Linket) -> Linktime::LinketImpl {
        self.linktime.linket_impl(linket, self.db)
    }
}

/// # actions
impl<'db, Linktime: IsLinktime> VmirBuilder<'db, Linktime> {
    pub(crate) fn alloc_expr(
        &mut self,
        hir_eager_expr: HirEagerExprIdx,
        expr: VmirExprData<Linktime::LinketImpl>,
    ) -> VmirExprIdx<Linktime::LinketImpl> {
        let expr = self.vmir_expr_arena.alloc_one(expr);
        self.hir_eager_to_vmir_expr_map
            .insert_new(hir_eager_expr, VmirExprIdx(expr));
        VmirExprIdx(expr)
    }

    pub(crate) fn alloc_exprs(
        &mut self,
        hir_eager_exprs: &[HirEagerExprIdx],
        exprs: Vec<VmirExprData<Linktime::LinketImpl>>,
    ) -> VmirExprIdxRange<Linktime::LinketImpl> {
        let exprs = self.vmir_expr_arena.alloc_many(exprs);
        for (hir_eager_expr, expr) in hir_eager_exprs.iter().copied().zip(exprs) {
            self.hir_eager_to_vmir_expr_map
                .insert_new(hir_eager_expr, VmirExprIdx(expr));
        }
        VmirExprIdxRange(exprs)
    }

    pub(crate) fn alloc_stmts(
        &mut self,
        hir_eager_stmts: HirEagerStmtIdxRange,
        stmts: Vec<VmirStmtData<Linktime::LinketImpl>>,
    ) -> ArenaIdxRange<VmirStmtData<Linktime::LinketImpl>> {
        let stmts = self.vmir_stmt_arena.alloc_many(stmts);
        for (hir_eager_stmt, stmt) in hir_eager_stmts.into_iter().zip(stmts) {
            self.hir_eager_to_vmir_stmt_map
                .insert_new(hir_eager_stmt, VmirStmtIdx(stmt));
        }
        stmts
    }

    pub(crate) fn alloc_restructive_pattern(
        &mut self,
        pattern: VmirRestructivePatternData<Linktime::LinketImpl>,
    ) -> VmirRestructivePatternIdx<Linktime::LinketImpl> {
        self.vmir_restructive_pattern_arena.alloc_one(pattern)
    }

    pub(crate) fn alloc_restructive_patterns(
        &mut self,
        patterns: Vec<VmirRestructivePatternData<Linktime::LinketImpl>>,
    ) -> VmirRestructivePatternIdxRange<Linktime::LinketImpl> {
        self.vmir_restructive_pattern_arena.alloc_many(patterns)
    }

    pub(crate) fn alloc_destructive_pattern(
        &mut self,
        pattern: VmirDestructivePatternData<Linktime::LinketImpl>,
    ) -> VmirDestructivePatternIdx<Linktime::LinketImpl> {
        self.vmir_destructive_pattern_arena.alloc_one(pattern)
    }

    pub(crate) fn alloc_destructive_patterns(
        &mut self,
        patterns: Vec<VmirDestructivePatternData<Linktime::LinketImpl>>,
    ) -> VmirDestructivePatternIdxRange<Linktime::LinketImpl> {
        self.vmir_destructive_pattern_arena.alloc_many(patterns)
    }

    pub(crate) fn alloc_destroyers(
        &mut self,
        destroyer_datas: Vec<VmirDestroyerData>,
    ) -> VmirDestroyerIdxRange {
        self.vmir_destroyer_arena.alloc_many(destroyer_datas)
    }

    pub(crate) fn finish(
        self,
        linket: Linket,
        root_expr: VmirExprIdx<Linktime::LinketImpl>,
    ) -> VmirRegion<Linktime::LinketImpl> {
        VmirRegion::new(
            linket,
            root_expr,
            self.vmir_expr_arena,
            self.vmir_stmt_arena,
            self.vmir_restructive_pattern_arena,
            self.vmir_destructive_pattern_arena,
            self.vmir_destroyer_arena,
            self.hir_eager_to_vmir_expr_map,
            self.hir_eager_to_vmir_stmt_map,
        )
    }
}

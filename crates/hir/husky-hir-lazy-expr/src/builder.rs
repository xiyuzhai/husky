use crate::{source_map::HirLazyExprSourceMap, *};
use husky_fly_term::{FlyTerm, FlyTermBase, FlyTerms};
use husky_hir_ty::HirType;
use husky_sem_expr::{
    SemExprArenaRef, SemExprIdx, SemExprMap, SemExprRegion, SemExprRegionData, SemStmtArenaRef,
    SemStmtIdx, SemStmtMap,
};
use husky_sem_place_contract::region::{sem_place_contract_region, SemPlaceContractRegion};
use husky_syn_expr::{
    context::{SynExprRootKind, SynPatternRootKind},
    pattern::{SynPatternIdx, SynPatternMap},
    region::SynExprRegionData,
    variable::{CurrentVariableIdx, InheritedVariableIdx, VariableMap},
};
use salsa::DebugWithDb;

pub(crate) struct HirLazyExprBuilder<'a> {
    db: &'a ::salsa::Db,
    syn_expr_region_data: &'a SynExprRegionData,
    sem_expr_region_data: &'a SemExprRegionData,
    sem_place_contract_region: &'a SemPlaceContractRegion,
    hir_lazy_expr_arena: HirLazyExprArena,
    hir_lazy_stmt_arena: HirLazyStmtArena,
    hir_lazy_pattern_arena: HirLazyPatternArena,
    syn_to_hir_lazy_pattern_idx_map: SynPatternMap<HirLazyPatternIdx>,
    sem_to_hir_lazy_expr_idx_map: SemExprMap<HirLazyExprIdx>,
    sem_to_hir_lazy_stmt_idx_map: SemStmtMap<HirLazyStmtIdx>,
    hir_lazy_variable_region: HirLazyVariableRegion,
    variable_to_hir_lazy_variable_map: VariableMap<HirLazyVariableIdx>,
}

impl<'a> HirLazyExprBuilder<'a> {
    fn new(db: &'a ::salsa::Db, sem_expr_region: SemExprRegion) -> Self {
        let syn_expr_region_data = sem_expr_region.syn_expr_region(db).data(db);
        let sem_expr_region_data = sem_expr_region.data(db);
        let syn_to_hir_lazy_pattern_idx_map =
            SynPatternMap::new(syn_expr_region_data.pattern_arena());
        let (hir_lazy_variable_region, variable_to_hir_lazy_variable_map) =
            HirLazyVariableRegion::from_syn(syn_expr_region_data.variable_region());
        Self {
            db,
            syn_expr_region_data,
            sem_expr_region_data,
            sem_place_contract_region: sem_place_contract_region(db, sem_expr_region),
            hir_lazy_expr_arena: Default::default(),
            hir_lazy_stmt_arena: Default::default(),
            hir_lazy_pattern_arena: Default::default(),
            syn_to_hir_lazy_pattern_idx_map,
            sem_to_hir_lazy_expr_idx_map: SemExprMap::new(sem_expr_region_data.sem_expr_arena()),
            sem_to_hir_lazy_stmt_idx_map: SemStmtMap::new(sem_expr_region_data.sem_stmt_arena()),
            hir_lazy_variable_region,
            variable_to_hir_lazy_variable_map,
        }
    }

    pub(crate) fn syn_expr_region_data(&self) -> &'a SynExprRegionData {
        self.syn_expr_region_data
    }

    pub(crate) fn sem_expr_arena_ref(&self) -> SemExprArenaRef<'a> {
        self.sem_expr_region_data.sem_expr_arena()
    }

    pub(crate) fn sem_stmt_arena_ref(&self) -> SemStmtArenaRef<'a> {
        self.sem_expr_region_data.sem_stmt_arena()
    }

    pub(crate) fn sem_place_contract_region(&self) -> &'a SemPlaceContractRegion {
        self.sem_place_contract_region
    }

    pub(crate) fn alloc_stmts(
        &mut self,
        sem_stmt_indices: Vec<SemStmtIdx>,
        hir_eager_stmts: Vec<HirLazyStmtData>,
    ) -> HirLazyStmtIdxRange {
        debug_assert_eq!(sem_stmt_indices.len(), hir_eager_stmts.len());
        let hir_stmt_idx_range = self.hir_lazy_stmt_arena.alloc_many(hir_eager_stmts);
        for (sem_stmt_idx, hir_lazy_stmt_idx) in
            std::iter::zip(sem_stmt_indices, hir_stmt_idx_range)
        {
            self.sem_to_hir_lazy_stmt_idx_map
                .insert_new(sem_stmt_idx, hir_lazy_stmt_idx);
        }
        hir_stmt_idx_range
    }

    pub(crate) fn alloc_expr(
        &mut self,
        sem_expr_idx: SemExprIdx,
        hir_lazy_expr: HirLazyExprData,
    ) -> HirLazyExprIdx {
        let hir_lazy_expr_idx = self.hir_lazy_expr_arena.alloc_one(hir_lazy_expr);
        self.sem_to_hir_lazy_expr_idx_map
            .insert_new(sem_expr_idx, hir_lazy_expr_idx);
        hir_lazy_expr_idx
    }

    pub(crate) fn alloc_pattern(
        &mut self,
        syn_pattern_idx: SynPatternIdx,
        pattern_data: HirLazyPatternData,
    ) -> HirLazyPatternIdx {
        let hir_lazy_pattern_idx = self.hir_lazy_pattern_arena.alloc_one(pattern_data);
        self.syn_to_hir_lazy_pattern_idx_map
            .insert_new(syn_pattern_idx, hir_lazy_pattern_idx);
        hir_lazy_pattern_idx
    }

    pub fn db(&self) -> &'a ::salsa::Db {
        self.db
    }

    pub(crate) fn path(&self) -> String {
        format!("{:?}", self.syn_expr_region_data.path().debug(self.db))
    }

    pub(crate) fn expr_ty(&self, sem_expr_idx: SemExprIdx) -> FlyTerm {
        sem_expr_idx.ty(self.sem_expr_region_data.sem_expr_arena2())
    }

    pub(crate) fn expr_term_to_hir_ty(&self, sem_expr_idx: SemExprIdx) -> Option<HirType> {
        HirType::from_eth(self.expr_term(sem_expr_idx), self.db)
    }

    pub(crate) fn expr_term(&self, sem_expr_idx: SemExprIdx) -> EthTerm {
        // ad hoc
        match self
            .sem_expr_region_data
            .sem_expr_term(sem_expr_idx)
            .expect("hir stage some")
            .expect("hir stage ok")
            .base_resolved_inner(self.sem_expr_region_data.fly_term_region().terms())
        {
            FlyTermBase::Eth(term) => term,
            FlyTermBase::Sol(_) => todo!(),
            FlyTermBase::Hol(_) => todo!(),
            FlyTermBase::Place => todo!(),
        }
    }

    pub fn build_all_then_finish(mut self) -> (HirLazyExprRegion, HirLazyExprSourceMap) {
        for (sem_expr_idx, expr_root_kind) in self.sem_expr_region_data.sem_expr_roots() {
            match expr_root_kind {
                SynExprRootKind::RootBody | SynExprRootKind::ReturnExpr => {
                    sem_expr_idx.to_hir_lazy(&mut self);
                }
                // ad hoc
                SynExprRootKind::FieldBindInitialValue { .. } => (),
                // ad hoc
                SynExprRootKind::ParenateParameterDefaultValue { .. } => (),
                // ad hoc
                SynExprRootKind::Snippet => (),
                // ad hoc
                SynExprRootKind::ValExpr => (),
                _ => continue,
            }
        }
        for &syn_pattern_root in self.syn_expr_region_data.syn_pattern_roots() {
            match syn_pattern_root.kind() {
                SynPatternRootKind::Parenate => {
                    self.new_pattern(syn_pattern_root);
                }
                // already covered when building expr roots
                SynPatternRootKind::Let
                | SynPatternRootKind::Case
                | SynPatternRootKind::Be
                | SynPatternRootKind::Closure => continue,
            }
        }
        self.finish()
    }

    pub(crate) fn inherited_variable_to_hir_lazy_variable(
        &self,
        inherited_variable_idx: InheritedVariableIdx,
    ) -> Option<HirLazyVariableIdx> {
        self.variable_to_hir_lazy_variable_map
            .get_inherited(inherited_variable_idx)
            .copied()
    }

    pub(crate) fn current_variable_to_hir_lazy_variable(
        &self,
        current_variable_idx: CurrentVariableIdx,
    ) -> Option<HirLazyVariableIdx> {
        self.variable_to_hir_lazy_variable_map
            .get_current(current_variable_idx)
            .copied()
    }

    pub fn finish(self) -> (HirLazyExprRegion, HirLazyExprSourceMap) {
        (
            HirLazyExprRegion::new(
                self.db,
                self.hir_lazy_expr_arena,
                self.hir_lazy_stmt_arena,
                self.hir_lazy_pattern_arena,
                self.hir_lazy_variable_region,
            ),
            HirLazyExprSourceMap::new(
                self.db,
                self.syn_to_hir_lazy_pattern_idx_map,
                self.sem_to_hir_lazy_expr_idx_map,
                self.sem_to_hir_lazy_stmt_idx_map,
                self.variable_to_hir_lazy_variable_map,
            ),
        )
    }

    pub(crate) fn hir_lazy_expr_arena(&self) -> &HirLazyExprArena {
        &self.hir_lazy_expr_arena
    }

    pub(crate) fn fly_terms(&self) -> &FlyTerms {
        self.sem_expr_region_data.fly_term_region().terms()
    }

    pub(crate) fn sem_expr_region_data(&self) -> &'a SemExprRegionData {
        self.sem_expr_region_data
    }
}

/// todo: it's rather hard to find this function, put it somewhere else
#[salsa::tracked(jar = HirLazyExprJar)]
pub fn hir_lazy_expr_region_with_source_map(
    db: &::salsa::Db,
    sem_expr_region: SemExprRegion,
) -> (HirLazyExprRegion, HirLazyExprSourceMap) {
    let builder = HirLazyExprBuilder::new(db, sem_expr_region);
    builder.build_all_then_finish()
}

use crate::{
    variable::{
        comptime::HirEagerComptimeVariableRegionData,
        runtime::{HirEagerRuntimeVariableIdx, HirEagerRuntimeVariableRegionData},
    },
    *,
};
use husky_eth_term::term::EthTerm;
use husky_fly_term::{FlyTerm, FlyTermBase, FlyTerms};
use husky_hir_ty::{ritchie::HirContract, HirType};
use husky_place::place::EthPlace;
use husky_sem_expr::{
    SemExprArena, SemExprArenaRef, SemExprIdx, SemExprMap, SemExprRegion, SemExprRegionData,
    SemStmtArenaRef, SemStmtIdx, SemStmtMap,
};
use husky_sem_place_contract::region::{sem_place_contract_region, SemPlaceContractRegion};
use husky_syn_expr::region::SynExprRegion;
use husky_syn_expr::{
    context::{SynExprRootKind, SynPatternRootKind},
    pattern::{SynPatternIdx, SynPatternMap},
    region::SynExprRegionData,
    variable::{CurrentVariableIdx, InheritedVariableIdx, VariableMap},
};

pub(crate) struct HirEagerExprBuilder<'a> {
    db: &'a ::salsa::Db,
    syn_expr_region: SynExprRegion,
    syn_expr_region_data: &'a SynExprRegionData,
    pub(crate) sem_expr_region_data: &'a SemExprRegionData,
    sem_place_contract_region: &'a SemPlaceContractRegion,
    hir_eager_expr_arena: HirEagerExprArena,
    hir_eager_stmt_arena: HirEagerStmtArena,
    hir_eager_pattern_arena: HirEagerPatternArena,
    syn_to_hir_eager_pattern_idx_map: SynPatternMap<HirEagerPatternIdx>,
    sem_to_hir_eager_expr_idx_map: SemExprMap<HirEagerExprIdx>,
    sem_to_hir_eager_stmt_idx_map: SemStmtMap<HirEagerStmtIdx>,
    hir_eager_comptime_symbol_region_data: HirEagerComptimeVariableRegionData,
    hir_eager_runtime_variable_region_data: HirEagerRuntimeVariableRegionData,
    variable_to_hir_eager_runtime_variable_map: VariableMap<HirEagerRuntimeVariableIdx>,
}

impl<'db> HirEagerExprBuilder<'db> {
    fn new(db: &'db ::salsa::Db, sem_expr_region: SemExprRegion) -> Self {
        let syn_expr_region = sem_expr_region.syn_expr_region(db);
        let syn_expr_region_data = syn_expr_region.data(db);
        let sem_expr_region_data = sem_expr_region.data(db);
        let syn_to_hir_eager_pattern_idx_map =
            SynPatternMap::new(syn_expr_region_data.pattern_arena());
        let sem_to_hir_eager_expr_idx_map = SemExprMap::new(sem_expr_region_data.sem_expr_arena());
        let sem_to_hir_eager_stmt_idx_map = SemStmtMap::new(sem_expr_region_data.sem_stmt_arena());
        let hir_eager_comptime_symbol_region_data = HirEagerComptimeVariableRegionData::from_sema(
            sem_expr_region_data,
            syn_expr_region_data.variable_region(),
            db,
        );
        let (hir_eager_runtime_variable_region, variable_to_hir_eager_runtime_variable_map) =
            HirEagerRuntimeVariableRegionData::from_syn(syn_expr_region_data.variable_region());
        Self {
            db,
            syn_expr_region,
            syn_expr_region_data,
            sem_expr_region_data,
            sem_place_contract_region: sem_place_contract_region(db, sem_expr_region),
            hir_eager_expr_arena: Default::default(),
            hir_eager_pattern_arena: Default::default(),
            hir_eager_stmt_arena: Default::default(),
            syn_to_hir_eager_pattern_idx_map: syn_to_hir_eager_pattern_idx_map,
            sem_to_hir_eager_expr_idx_map,
            sem_to_hir_eager_stmt_idx_map,
            hir_eager_comptime_symbol_region_data,
            hir_eager_runtime_variable_region_data: hir_eager_runtime_variable_region,
            variable_to_hir_eager_runtime_variable_map,
        }
    }
}

impl<'db> HirEagerExprBuilder<'db> {
    pub(crate) fn syn_expr_region(&self) -> SynExprRegion {
        self.syn_expr_region
    }

    pub(crate) fn syn_expr_region_data(&self) -> &'db SynExprRegionData {
        self.syn_expr_region_data
    }

    pub(crate) fn sem_expr_arena_ref(&self) -> SemExprArenaRef<'db> {
        self.sem_expr_region_data.sem_expr_arena()
    }

    #[deprecated(note = "ad hoc")]
    pub(crate) fn sem_expr_arena_ref2(&self) -> &'db SemExprArena {
        self.sem_expr_region_data.sem_expr_arena2()
    }

    pub(crate) fn sem_stmt_arena_ref(&self) -> SemStmtArenaRef<'db> {
        self.sem_expr_region_data.sem_stmt_arena()
    }

    pub fn build_all_then_finish(mut self) -> (HirEagerExprRegion, HirEagerExprSourceMap) {
        for (sem_expr_idx, expr_root_kind) in self.sem_expr_region_data.sem_expr_roots() {
            match expr_root_kind {
                SynExprRootKind::RootBody
                | SynExprRootKind::ReturnExpr
                | SynExprRootKind::FieldBindInitialValue { .. }
                | SynExprRootKind::ParenateParameterDefaultValue { .. } => {
                    sem_expr_idx.to_hir_eager(&mut self);
                }
                // ad hoc
                SynExprRootKind::Snippet => (),
                // ad hoc
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

    pub(crate) fn alloc_stmts(
        &mut self,
        sem_stmt_indices: Vec<SemStmtIdx>,
        hir_eager_stmts: Vec<HirEagerStmtData>,
    ) -> HirEagerStmtIdxRange {
        debug_assert_eq!(sem_stmt_indices.len(), hir_eager_stmts.len());
        let hir_stmt_idx_range = self.hir_eager_stmt_arena.alloc_many(hir_eager_stmts);
        for (sem_stmt_idx, hir_eager_stmt_idx) in
            std::iter::zip(sem_stmt_indices, hir_stmt_idx_range)
        {
            self.sem_to_hir_eager_stmt_idx_map
                .insert_new(sem_stmt_idx, hir_eager_stmt_idx);
        }
        hir_stmt_idx_range
    }

    pub(crate) fn alloc_expr(
        &mut self,
        sem_expr_idx: SemExprIdx,
        hir_eager_expr_entry: HirEagerExprEntry,
    ) -> HirEagerExprIdx {
        let hir_eager_expr_idx = self.hir_eager_expr_arena.alloc_one(hir_eager_expr_entry);
        self.sem_to_hir_eager_expr_idx_map
            .insert_new(sem_expr_idx, hir_eager_expr_idx);
        hir_eager_expr_idx
    }

    pub(crate) fn alloc_pattern(
        &mut self,
        pattern: HirEagerPatternData,
        syn_pattern: SynPatternIdx,
    ) -> HirEagerPatternIdx {
        let contract =
            HirContract::from_contract(self.syn_expr_region_data.pattern_contract(syn_pattern));
        let entry = HirEagerPatternEntry::new(pattern, contract);
        let pattern = self.hir_eager_pattern_arena.alloc_one(entry);
        self.syn_to_hir_eager_pattern_idx_map
            .insert_new(syn_pattern, pattern);
        pattern
    }

    pub(crate) fn alloc_patterns(
        &mut self,
        patterns: Vec<HirEagerPatternData>,
        syn_patterns: impl Iterator<Item = SynPatternIdx> + Clone,
    ) -> HirEagerPatternIdxRange {
        let entries =
            std::iter::zip(patterns, syn_patterns.clone()).map(|(pattern, syn_pattern)| {
                let contract = HirContract::from_contract(
                    self.syn_expr_region_data.pattern_contract(syn_pattern),
                );
                HirEagerPatternEntry::new(pattern, contract)
            });
        let patterns = self.hir_eager_pattern_arena.alloc_many(entries);
        for (pattern, syn_pattern) in std::iter::zip(patterns, syn_patterns) {
            self.syn_to_hir_eager_pattern_idx_map
                .insert_new(syn_pattern, pattern);
        }
        patterns
    }

    pub(crate) fn path(&self) -> String {
        use salsa::DebugWithDb;

        format!("{:?}", self.syn_expr_region_data.path().debug(self.db))
    }

    pub fn db(&self) -> &'db ::salsa::Db {
        self.db
    }

    pub(crate) fn expr_term_hir_ty(&self, sem_expr_idx: SemExprIdx) -> Option<HirType> {
        HirType::from_eth(self.expr_term(sem_expr_idx), self.db)
    }

    pub(crate) fn expr_ty(&self, sem_expr_idx: SemExprIdx) -> FlyTerm {
        sem_expr_idx.ty(self.sem_expr_region_data.sem_expr_arena2())
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

    pub(crate) fn inherited_variable_to_hir_eager_runtime_variable(
        &self,
        inherited_variable_idx: InheritedVariableIdx,
    ) -> Option<HirEagerRuntimeVariableIdx> {
        self.variable_to_hir_eager_runtime_variable_map
            .get_inherited(inherited_variable_idx)
            .copied()
    }

    pub(crate) fn current_variable_to_hir_eager_runtime_variable(
        &self,
        current_variable_idx: CurrentVariableIdx,
    ) -> Option<HirEagerRuntimeVariableIdx> {
        self.variable_to_hir_eager_runtime_variable_map
            .get_current(current_variable_idx)
            .copied()
    }

    fn finish(self) -> (HirEagerExprRegion, HirEagerExprSourceMap) {
        let self_value_ty = self.sem_expr_region_data.self_value_ty().map(|term| {
            HirType::from_fly_base(
                term,
                self.db,
                self.sem_expr_region_data.fly_term_region().terms(),
            )
            .expect("no error at this stage")
        });
        (
            HirEagerExprRegion::new(
                self.db,
                self.sem_expr_region_data.region_path(),
                self_value_ty,
                self.hir_eager_expr_arena,
                self.hir_eager_stmt_arena,
                self.hir_eager_pattern_arena,
                self.hir_eager_comptime_symbol_region_data,
                self.hir_eager_runtime_variable_region_data,
            ),
            HirEagerExprSourceMap::new(
                self.db,
                self.syn_to_hir_eager_pattern_idx_map,
                self.sem_to_hir_eager_expr_idx_map,
                self.sem_to_hir_eager_stmt_idx_map,
                self.variable_to_hir_eager_runtime_variable_map,
            ),
        )
    }

    pub(crate) fn self_value_variable(&self) -> Option<HirEagerRuntimeVariableIdx> {
        self.hir_eager_runtime_variable_region_data
            .self_value_variable()
    }

    pub(crate) fn hir_eager_expr_arena(&self) -> &HirEagerExprArena {
        &self.hir_eager_expr_arena
    }

    pub(crate) fn syn_pattern_ty(&self, syn_pattern: SynPatternIdx) -> EthTerm {
        self.sem_expr_region_data
            .syn_pattern_ty(syn_pattern, self.db)
    }

    pub(crate) fn terms(&self) -> &'db FlyTerms {
        self.sem_expr_region_data.fly_term_region().terms()
    }

    pub(crate) fn sem_place_contract_region(&self) -> &'db SemPlaceContractRegion {
        self.sem_place_contract_region
    }
}

#[salsa::tracked(jar = HirEagerExprJar)]
pub fn hir_eager_expr_region_with_source_map(
    db: &::salsa::Db,
    sem_expr_region: SemExprRegion,
) -> (HirEagerExprRegion, HirEagerExprSourceMap) {
    let builder = HirEagerExprBuilder::new(db, sem_expr_region);
    builder.build_all_then_finish()
}

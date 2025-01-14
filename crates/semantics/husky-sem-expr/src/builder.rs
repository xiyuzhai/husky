mod dec_term_region;
#[macro_use]
mod helpers;
mod branch_ty_merger;

pub(crate) use self::branch_ty_merger::*;
pub(crate) use self::helpers::*;

use self::dec_term_region::*;
use crate::*;
use husky_dec_signature::{jar::DecSignatureDb, region::SynExprDecTermRegion};
use husky_entity_path::menu::{item_path_menu, ItemPathMenu};
use husky_entity_tree::{
    helpers::{tokra_region::crate_decl::HasCrateDeclTokraRegion, AvailableTraitItemsTable},
    region_path::SynNodeRegionPath,
};
use husky_eth_signature::{
    context::EthTermContextRef,
    error::EthSignatureResult,
    signature::{
        package::{PackageEthSignature, PackageEthSignatureData},
        HasEthSignature, HasEthTemplate,
    },
};
use husky_eth_term::{
    instantiation::IsEthTermContextRef,
    term::{symbolic_variable::EthSymbolicVariable, EthTerm},
};
use husky_fly_term::quary::FlyQuary;
use husky_place::{PlaceInfo, PlaceRegistry};
use husky_regional_token::{RegionalTokenIdx, RegionalTokensData};
use husky_syn_decl::decl::{
    assoc_item::{
        trai_for_ty_item::TraitForTypeItemSynNodeDecl, trai_item::TraitItemSynNodeDecl,
        ty_item::TypeItemSynNodeDecl, AssocItemSynNodeDecl,
    },
    HasSynNodeDecl, ItemSynNodeDecl,
};
use husky_token_data::{IntegerLikeLiteralTokenData, LiteralTokenData, TokenData};
use husky_vfs::path::menu::VfsPathMenu;
use husky_vfs::toolchain::Toolchain;
use vec_like::{SmallVecPairMap, SmallVecSet, VecPairMap};

pub(crate) struct SemExprBuilder<'db> {
    db: &'db ::salsa::Db,
    toolchain: Toolchain,
    item_path_menu: &'db ItemPathMenu,
    term_menu: &'db EthTermMenu,
    syn_expr_region: SynExprRegion,
    syn_expr_region_data: &'db SynExprRegionData,
    regional_tokens_data: RegionalTokensData<'db>,
    dec_term_region: &'db SynExprDecTermRegion,
    context_ref: EthTermContextRef,
    place_registry: PlaceRegistry,
    sem_expr_arena: SemExprArena,
    sem_stmt_arena: SemStmtArena,
    pub(crate) sem_expr_roots: VecPairMap<SynExprIdx, (SemExprIdx, SynExprRootKind)>,
    fly_term_region: FlyTermRegion,
    sem_expr_term_results: VecPairMap<SemExprIdx, SemExprTermResult<FlyTerm>>,
    symbol_terms: SymbolMap<FlyTerm>,
    symbol_tys: SymbolMap<SymbolType>,
    /// warning: not all pattern are inferred
    ///
    /// only those not inferred by dec term region is inferred
    pattern_ty_infos: SynPatternMap<PatternTypeInfo>,
    pattern_variable_ty_infos: SynPatternSymbolMap<PatternSymbolTypeInfo>,
    pattern_contracts: SynPatternMap<Contract>,
    return_ty: Option<EthTerm>,
    pub(crate) unveiler: Unveiler,
    self_ty: Option<EthTerm>,
    self_value: Option<EthSymbolicVariable>,
    self_value_ty: Option<FlyTerm>,
    self_lifetime: Option<EthSymbolicVariable>,
    self_place: Option<EthSymbolicVariable>,
    available_trai_items_table: AvailableTraitItemsTable<'db>,
    obvious_trais_map:
        SmallVecPairMap<EthSymbolicVariable, EthTermResult<SmallVecSet<EthTerm, 2>>, 4>,
}

/// # constructors

impl<'a> SemExprBuilder<'a> {
    pub(crate) fn new(db: &'a ::salsa::Db, syn_expr_region: SynExprRegion) -> Self {
        let syn_expr_region_data = syn_expr_region.data(db);
        // todo: improve this
        let parent_expr_region = syn_expr_region_data.parent();
        let region_path = syn_expr_region_data.path();
        let module_path = region_path.module_path(db);
        let return_ty = parent_expr_region
            .map(|parent_expr_region| {
                db.syn_expr_dec_term_region(parent_expr_region)
                    .expr_term(parent_expr_region.data(db).return_ty()?)
                    .ok()
            })
            .flatten()
            .map(|term| EthTerm::ty_from_dec(db, term).ok())
            .flatten();
        let dec_term_region = db.syn_expr_dec_term_region(syn_expr_region);
        let self_ty = dec_term_region
            .symbolic_variable_region()
            .self_ty()
            .map(|self_ty| EthTerm::ty_from_dec(db, self_ty).ok())
            .flatten();
        let self_value = dec_term_region
            .symbolic_variable_region()
            .self_value()
            .map(|self_value| EthSymbolicVariable::from_dec(db, self_value).ok())
            .flatten();
        let mut stack_location_registry = Default::default();
        let self_lifetime = dec_term_region
            .symbolic_variable_region()
            .self_lifetime()
            .map(|self_lifetime| EthSymbolicVariable::from_dec(db, self_lifetime).ok())
            .flatten();
        let self_place = dec_term_region
            .symbolic_variable_region()
            .self_place()
            .map(|self_place| EthSymbolicVariable::from_dec(db, self_place).ok())
            .flatten();
        let self_value_ty = calc_self_value_ty(
            syn_expr_region_data,
            self_ty,
            self_place,
            db,
            &mut stack_location_registry,
        );
        let context_ref = EthTermContextRef::new(region_path, db).expect("todo: handle error");
        // module_path
        //     .package_path(db)
        //     .eth_signature(db)
        //     .map(|signature| signature.data(db));
        let symbol_region = syn_expr_region_data.variable_region();
        let pattern_region = syn_expr_region_data.pattern_region();
        let toolchain = syn_expr_region.toolchain(db);
        let parent_sem_expr_region =
            parent_expr_region.map(|parent_expr_region| db.sem_expr_region(parent_expr_region));
        let regional_tokens_data = match syn_expr_region_data.path() {
            SynNodeRegionPath::CrateDecl(path) => match path.decl_tokra_region(db) {
                Some(region) => region.regional_tokens_data(db),
                None => todo!(),
            },
            SynNodeRegionPath::ItemDecl(path) => {
                path.decl_tokra_region(db).regional_tokens_data(db)
            }
            SynNodeRegionPath::ItemDefn(path) => path
                .defn_tokra_region(db)
                .expect("guaranteed")
                .tokens_data(db),
        };
        let obvious_trais_map = dec_term_region
            .symbolic_variable_region()
            .obvious_trais_map()
            .iter()
            .filter_map(|&(svar, ref trais)| {
                let trais = match trais {
                    Ok(trais) => trais
                        .iter()
                        .map(|&trai| {
                            EthTerm::from_dec(db, trai, TypeFinalDestinationExpectation::Any)
                        })
                        .collect(),
                    &Err(e) => Err(e.into()),
                };
                Some((EthSymbolicVariable::from_dec(db, svar).ok()?, trais))
            })
            .collect();
        Self {
            db,
            toolchain,
            item_path_menu: item_path_menu(db, toolchain),
            term_menu: db.eth_term_menu(toolchain),
            syn_expr_region,
            syn_expr_region_data,
            dec_term_region,
            obvious_trais_map,
            place_registry: stack_location_registry,
            sem_expr_arena: SemExprArena::default(),
            sem_stmt_arena: SemStmtArena::default(),
            sem_expr_roots: Default::default(),
            fly_term_region: FlyTermRegion::new(
                parent_sem_expr_region.map(|r| r.data(db).fly_term_region()),
            ),
            sem_expr_term_results: Default::default(),
            symbol_terms: SymbolMap::new(
                parent_sem_expr_region
                    .map(|parent_sem_expr_region| parent_sem_expr_region.data(db).symbol_terms()),
                syn_expr_region_data.variable_region(),
            ),
            symbol_tys: SymbolMap::new(
                parent_sem_expr_region
                    .map(|parent_sem_expr_region| parent_sem_expr_region.data(db).symbol_tys()),
                syn_expr_region_data.variable_region(),
            ),
            pattern_ty_infos: SynPatternMap::new(pattern_region.pattern_arena()),
            pattern_variable_ty_infos: SynPatternSymbolMap::new(
                pattern_region.pattern_variable_arena(),
            ),
            return_ty,
            unveiler: Unveiler::Uninitialized,
            self_ty,
            self_value,
            self_value_ty,
            self_lifetime,
            self_place,
            pattern_contracts: SynPatternMap::new(pattern_region.pattern_arena()),
            available_trai_items_table: AvailableTraitItemsTable::new_ad_hoc(db, module_path),
            regional_tokens_data,
            context_ref,
        }
    }
}

fn calc_self_value_ty(
    syn_expr_region_data: &SynExprRegionData,
    self_ty: Option<EthTerm>,
    self_place: Option<EthSymbolicVariable>,
    db: &salsa::Db,
    registry: &mut PlaceRegistry,
) -> Option<FlyTerm> {
    fn method_ritchie_self_value_modifier_from_self_value_parameter(
        self_value_parameter: &Option<SelfValueParameterSyndicate>,
    ) -> VariableModifier {
        let Some(self_value_parameter) = self_value_parameter else {
            return VariableModifier::Pure;
        };
        VariableModifier::new(self_value_parameter.ephem_symbol_modifier_token_verse())
    }
    let self_ty = self_ty?;
    let (self_value_ty, modifier) = match syn_expr_region_data.path() {
        SynNodeRegionPath::CrateDecl(_) => todo!(),
        SynNodeRegionPath::ItemDecl(syn_node_path) | SynNodeRegionPath::ItemDefn(syn_node_path) => {
            match syn_node_path.syn_node_decl(db) {
                ItemSynNodeDecl::AssocItem(syn_node_decl) => match syn_node_decl {
                    AssocItemSynNodeDecl::TypeItem(syn_node_decl) => match syn_node_decl {
                        TypeItemSynNodeDecl::MethodFn(syn_node_decl) => (
                            self_ty,
                            method_ritchie_self_value_modifier_from_self_value_parameter(
                                syn_node_decl
                                    .parenate_parameters(db)
                                    .as_ref()
                                    .ok()?
                                    .self_value_parameter(),
                            ),
                        ),
                        TypeItemSynNodeDecl::MemoizedField(_) => {
                            (self_ty.leashed(db), VariableModifier::Pure)
                        }
                        _ => return None,
                    },
                    AssocItemSynNodeDecl::TraitItem(syn_node_decl) => match syn_node_decl {
                        TraitItemSynNodeDecl::MethodRitchie(syn_node_decl) => (
                            self_ty,
                            method_ritchie_self_value_modifier_from_self_value_parameter(
                                syn_node_decl
                                    .parenate_parameter_decl_list(db)
                                    .as_ref()
                                    .ok()?
                                    .self_value_parameter(),
                            ),
                        ),
                        TraitItemSynNodeDecl::MemoizedField(_) => {
                            (self_ty.leashed(db), VariableModifier::Pure)
                        }
                        _ => return None,
                    },
                    AssocItemSynNodeDecl::TraitForTypeItem(syn_node_decl) => match syn_node_decl {
                        TraitForTypeItemSynNodeDecl::MethodFn(syn_node_decl) => (
                            self_ty,
                            method_ritchie_self_value_modifier_from_self_value_parameter(
                                syn_node_decl
                                    .parenate_parameter_decl_list(db)
                                    .as_ref()
                                    .ok()?
                                    .self_value_parameter(),
                            ),
                        ),
                        // todo: memo
                        _ => return None,
                    },
                    AssocItemSynNodeDecl::IllFormedItem(_) => return None,
                },
                _ => return None,
            }
        }
    };
    let place_data = PlaceInfo::SelfValue;
    let place = match modifier {
        VariableModifier::Pure => FlyQuary::StackPure {
            place: registry.issue_new(place_data).into(),
        },
        VariableModifier::Owned => FlyQuary::ImmutableOnStack {
            place: registry.issue_new(place_data).into(),
        },
        VariableModifier::Mut => FlyQuary::MutableOnStack {
            place: registry.issue_new(place_data).into(),
        },
        VariableModifier::Ref => todo!(),
        VariableModifier::RefMut => todo!(),
        VariableModifier::Compterm => todo!(),
        VariableModifier::Ambersand(_) => FlyQuary::Ref {
            guard: Left(registry.issue_new(place_data).into()),
        },
        VariableModifier::AmbersandMut(_) => FlyQuary::RefMut {
            place: registry.issue_new(place_data).into(),
            lifetime: None,
        },
        VariableModifier::Le => FlyQuary::Leashed {
            place: Some(registry.issue_new(place_data)),
        },
        VariableModifier::Tilde => FlyQuary::Leashed {
            place: Some(registry.issue_new(place_data)),
        },
        VariableModifier::At => FlyQuary::EtherealSymbol(self_place?),
    };
    let self_value_ty: FlyTerm = self_value_ty.into();
    Some(self_value_ty.with_quary(place))
}

/// # getters

impl<'db> FlyTermEngine<'db> for SemExprBuilder<'db> {
    fn db(&self) -> &'db ::salsa::Db {
        self.db
    }

    fn fly_term_region(&self) -> &FlyTermRegion {
        &self.fly_term_region
    }

    fn syn_expr_region_data(&self) -> &'db SynExprRegionData {
        self.syn_expr_region_data
    }

    fn item_path_menu(&self) -> &'db ItemPathMenu {
        self.item_path_menu
    }

    fn term_menu(&self) -> &'db EthTermMenu {
        self.term_menu
    }

    fn available_trai_items_table(&self) -> AvailableTraitItemsTable<'db> {
        self.available_trai_items_table
    }

    fn obvious_trais_map(
        &self,
    ) -> &[(
        EthSymbolicVariable,
        Result<SmallVecSet<EthTerm, 2>, EthTermError>,
    )] {
        &self.obvious_trais_map
    }

    fn context_ref(&self) -> EthTermContextRef {
        self.context_ref
    }
}

impl<'db> std::ops::Index<SynExprIdx> for SemExprBuilder<'db> {
    type Output = SynExprData;

    fn index(&self, index: SynExprIdx) -> &Self::Output {
        &self.syn_expr_region_data[index]
    }
}

impl<'a> SemExprBuilder<'a> {
    pub(crate) fn db(&self) -> &'a ::salsa::Db {
        self.db
    }

    pub(crate) fn dec_term_region(&self) -> &'a SynExprDecTermRegion {
        self.dec_term_region
    }

    pub(crate) fn symbol_terms(&self) -> &SymbolMap<FlyTerm> {
        &self.symbol_terms
    }

    pub(crate) fn expr_region_data(&self) -> &SynExprRegionData {
        self.syn_expr_region_data
    }

    pub(crate) fn item_path_menu(&self) -> &ItemPathMenu {
        self.item_path_menu
    }

    pub(crate) fn toolchain(&self) -> Toolchain {
        self.toolchain
    }

    pub(crate) fn eth_term_menu(&self) -> &EthTermMenu {
        self.term_menu
    }

    pub(crate) fn token_data(&self, regional_token_idx: RegionalTokenIdx) -> TokenData {
        self.regional_tokens_data[regional_token_idx]
    }

    pub(crate) fn syn_expr_region_data(&self) -> &'a SynExprRegionData {
        self.syn_expr_region_data
    }

    pub(crate) fn sem_expr_arena(&self) -> &SemExprArena {
        &self.sem_expr_arena
    }

    pub(crate) fn sem_expr_term_result(&self, expr: SemExprIdx) -> &SemExprTermResult<FlyTerm> {
        &self.sem_expr_term_results[expr].1
    }

    pub(crate) fn return_ty(&self) -> Option<EthTerm> {
        self.return_ty
    }

    pub(crate) fn symbol_tys(&self) -> &SymbolMap<SymbolType> {
        &self.symbol_tys
    }

    pub(crate) fn self_ty(&self) -> Option<EthTerm> {
        self.self_ty
    }

    pub(crate) fn self_place(&self) -> Option<EthSymbolicVariable> {
        self.self_place
    }

    pub(crate) fn self_value_ty(&self) -> Option<FlyTerm> {
        self.self_value_ty
    }

    pub(crate) fn get_pattern_ty(&self, pattern_idx: SynPatternIdx) -> Option<FlyTerm> {
        self.pattern_ty_infos
            .get(pattern_idx)
            .map(|info| info.ty().ok().copied())
            .flatten()
    }
}

/// # mut getters

impl<'a> FlyTermEngineMut<'a> for SemExprBuilder<'a> {
    fn place_registry_mut(&mut self) -> &mut PlaceRegistry {
        &mut self.place_registry
    }

    fn fly_term_region_mut(&mut self) -> &mut FlyTermRegion {
        &mut self.fly_term_region
    }
}

/// # actions

impl<'a> SemExprBuilder<'a> {
    pub(crate) fn infer_all(&mut self) {
        self.reuse_variable_inferences_from_dec_term_region();
        self.build_all_exprs()
    }

    pub(crate) fn alloc_expr(
        &mut self,
        data_result: Result<SemExprData, SemExprDataError>,
        ty_result: Result<FlyTerm, SemExprTypeError>,
        expectation_idx_and_ty: Option<(FlyTermExpectationIdx, FlyTerm)>,
    ) -> SemExprIdx {
        let expr = self
            .sem_expr_arena
            .alloc_one(data_result, ty_result, expectation_idx_and_ty);
        self.fly_term_region.resolve_as_much_as_possible(self.db());
        expr
    }

    pub(crate) fn alloc_stmt_batch(&mut self, batch: SemStmtBatch) -> SemStmtIdxRange {
        self.sem_stmt_arena.alloc_many(batch)
    }

    pub(crate) fn add_symbol_ty(&mut self, symbol_idx: CurrentVariableIdx, symbol_ty: SymbolType) {
        self.symbol_tys.insert_new(symbol_idx, symbol_ty)
    }

    /// perform this during finish stage
    pub(crate) fn infer_expr_term(&mut self, expr: SemExprIdx) -> Option<FlyTerm> {
        if let Some(term_result) = self.sem_expr_term_results.get_value(expr) {
            return term_result.as_ref().ok().copied();
        }
        let term_result = self.calc_expr_term(expr);
        let term = term_result.as_ref().ok().copied();
        self.save_new_expr_term(expr, term_result);
        term
    }

    /// clear all holes before using this
    pub(super) fn infer_extra_expr_terms_in_preparation_for_hir(&mut self) {
        for sem_expr_idx in self.sem_expr_arena.index_iter() {
            self.infer_extra_expr_term_in_preparation_for_hir(sem_expr_idx)
        }
    }

    // helpful for hir stage
    fn infer_extra_expr_term_in_preparation_for_hir(&mut self, sem_expr_idx: SemExprIdx) {
        if let Some(_) = self.sem_expr_term_results.get_value(sem_expr_idx) {
            return;
        }
        // ad hoc
        match sem_expr_idx.data_result(&self.sem_expr_arena) {
            Ok(SemExprData::Literal(_, _)) => (),
            _ => return,
        }
        let term_result = self.calc_expr_term(sem_expr_idx);
        let term = term_result.as_ref().ok().copied();
        self.save_new_expr_term(sem_expr_idx, term_result)
    }

    fn save_new_expr_term(
        &mut self,
        expr_idx: SemExprIdx,
        term_result: SemExprTermResult<FlyTerm>,
    ) {
        self.sem_expr_term_results
            .insert_new((expr_idx, term_result))
            .expect("todo")
    }

    pub(crate) fn infer_new_current_variable_ty(
        &mut self,
        current_variable_idx: CurrentVariableIdx,
    ) {
        let Some(ty) = self.calc_new_current_variable_ty(current_variable_idx) else {
            return;
        };
        let modifier =
            match *self.syn_expr_region_data().variable_region()[current_variable_idx].data() {
                CurrentVariableData::SimpleClosureParameter {
                    pattern_variable_idx,
                    ..
                }
                | CurrentVariableData::LetVariable {
                    pattern_variable_idx,
                    ..
                }
                | CurrentVariableData::BeVariable {
                    pattern_variable_idx,
                    ..
                }
                | CurrentVariableData::CaseVariable {
                    pattern_variable_idx,
                    ..
                } => self
                    .expr_region_data()
                    .pattern_variable_modifier(pattern_variable_idx),
                _ => unreachable!(),
            };
        let ty = match SymbolType::new_variable_ty(self, current_variable_idx, modifier, ty) {
            Ok(ty) => ty,
            Err(_) => todo!(),
        };
        self.symbol_tys.insert_new(current_variable_idx, ty)
    }

    /// used for defn body variables
    pub(crate) fn infer_variable_pattern_root_and_symbols_ty(
        &mut self,
        syn_pattern_root: impl Into<SynPatternRoot>,
        ty: FlyTerm,
        symbols: CurrentVariableIdxRange,
    ) {
        self.infer_pattern_ty(syn_pattern_root.into().syn_pattern_idx(), ty);
        for symbol in symbols {
            self.infer_new_current_variable_ty(symbol)
        }
    }

    /// the way type inference works for patterns is dual to that of expression
    pub(crate) fn infer_pattern_ty(&mut self, syn_pattern_idx: SynPatternIdx, ty: FlyTerm) {
        self.pattern_ty_infos
            .insert_new(syn_pattern_idx, PatternTypeInfo::new(Ok(ty)));
        self.infer_subpattern_tys(syn_pattern_idx, ty)
    }

    pub(crate) fn infer_new_pattern_variable_ty(
        &mut self,
        pattern_variable_idx: PatternVariableIdx,
    ) -> Option<FlyTerm> {
        let ty_result = self.calc_new_pattern_variable_ty(pattern_variable_idx);
        let ty = ty_result.as_ref().ok().copied();
        self.pattern_variable_ty_infos
            .insert_new(pattern_variable_idx, PatternSymbolTypeInfo::new(ty_result));
        ty
    }

    pub(crate) fn finish(mut self) -> SemExprRegion {
        let db = self.db;
        self.fly_term_region
            .finalize_unresolved_term_table(db, self.term_menu);
        self.infer_extra_expr_terms_in_preparation_for_hir();
        SemExprRegion::new(
            self.syn_expr_region_data
                .path()
                .region_path(db)
                .expect("should be some"),
            self.place_registry,
            self.syn_expr_region,
            self.sem_expr_arena,
            self.sem_stmt_arena,
            self.sem_expr_roots,
            self.pattern_ty_infos,
            self.pattern_variable_ty_infos,
            self.sem_expr_term_results,
            self.symbol_tys,
            self.symbol_terms,
            self.fly_term_region,
            self.return_ty,
            self.self_ty,
            self.self_value_ty,
            self.context_ref.context_itd(),
            self.db,
        )
    }
}

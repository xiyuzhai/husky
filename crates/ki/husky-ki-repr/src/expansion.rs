use crate::{
    repr::source::{KiReprExpansionSource, KiReprSource},
    *,
};
use husky_entity_kind::{ritchie::RitchieItemKind, MajorFormKind};
#[cfg(test)]
use husky_entity_path::path::major_item::form::MajorFormPath;
use husky_entity_path::path::{major_item::MajorItemPath, ItemPath, PrincipalEntityPath};
use husky_hir_defn::defn::{major_item::form::MajorFormHirDefn, HasHirDefn};
use husky_hir_expr::{HirExprIdx, HirExprRegion};
use husky_hir_lazy_expr::{
    helpers::control_flow::{HasControlFlow, HirLazyExprRegionControlFlowRegion},
    variable::HirLazyVariableMap,
    HirLazyBeVariablesPattern, HirLazyCallListArgument, HirLazyCondition, HirLazyExprData,
    HirLazyExprIdx, HirLazyExprMap, HirLazyExprRegion, HirLazyExprRegionData, HirLazyPatternData,
    HirLazyStmtData, HirLazyStmtIdx, HirLazyStmtIdxRange, HirLazyStmtMap,
};
use husky_hir_ty::{
    instantiation::{HirInstantiation, HirTermSymbolicVariableResolution},
    HirCompterm, HirTemplateArgument, HirTemplateVariable, HirTemplateVariableClass,
};
use husky_ki::{KiOpn, KiPatternData, KiRuntimeCompterm, KiRuntimeComptermData};
use husky_linket::{instantiation::LinInstantiation, linket::Linket};
use smallvec::{smallvec, SmallVec};

#[salsa::tracked]
pub struct KiReprExpansion {
    /// todo: needs to generalize to deal with closure expansion
    pub path: ItemPath,
    #[return_ref]
    pub hir_lazy_variable_ki_repr_map: HirLazyVariableMap<KiRepr>,
    #[return_ref]
    pub hir_lazy_expr_ki_repr_map: HirLazyExprMap<KiRepr>,
    #[return_ref]
    pub hir_lazy_stmt_ki_repr_map: HirLazyStmtMap<KiRepr>,
    #[return_ref]
    pub root_hir_lazy_stmt_ki_reprs: SmallVec<[KiRepr; 4]>,
}

impl KiRepr {
    pub fn expansion(self, db: &::salsa::Db) -> Option<KiReprExpansion> {
        ki_repr_expansion(db, self)
    }
}

#[salsa::tracked]
fn ki_repr_expansion(db: &::salsa::Db, ki_repr: KiRepr) -> Option<KiReprExpansion> {
    match ki_repr.opn(db) {
        KiOpn::Val(path) => {
            let MajorFormHirDefn::Val(hir_defn) = path.hir_defn(db)? else {
                unreachable!()
            };
            debug_assert!(ki_repr.arguments(db).is_empty());
            let (HirExprIdx::Lazy(body), HirExprRegion::Lazy(hir_lazy_expr_region)) =
                hir_defn.hir_expr_body_and_region(db)?
            else {
                return None;
            };
            Some(build_ki_repr_expansion(
                path.into(),
                ki_repr,
                body,
                hir_lazy_expr_region,
                &[],
                LinInstantiation::new_empty(path, false),
                db,
            ))
        }
        KiOpn::FunctionRitchie(_) => todo!(),
        _ => None,
    }
}

fn build_ki_repr_expansion(
    path: ItemPath,
    parent_ki_repr: KiRepr,
    body: HirLazyExprIdx,
    hir_lazy_expr_region: HirLazyExprRegion,
    argument_ki_reprs: &[KiRepr],
    lin_instantiation: LinInstantiation,
    db: &::salsa::Db,
) -> KiReprExpansion {
    let mut builder = KiReprExpansionBuilder::new(
        path,
        parent_ki_repr,
        body,
        hir_lazy_expr_region,
        argument_ki_reprs,
        lin_instantiation,
        db,
    );
    builder.build_all();
    builder.finish()
}

// todo: lin_instantiation
struct KiReprExpansionBuilder<'a> {
    path: ItemPath,
    parent_ki_repr: KiRepr,
    ki_domain_repr: KiDomainRepr,
    body: HirLazyExprIdx,
    hir_lazy_expr_region_data: HirLazyExprRegionData<'a>,
    // todo: change this to ordered map
    hir_lazy_variable_ki_repr_map: HirLazyVariableMap<KiRepr>,
    hir_lazy_expr_ki_repr_map: HirLazyExprMap<KiRepr>,
    hir_lazy_stmt_ki_repr_map: HirLazyStmtMap<KiRepr>,
    root_hir_lazy_stmt_ki_reprs: SmallVec<[KiRepr; 4]>,
    hir_lazy_expr_control_flow_region: &'a HirLazyExprRegionControlFlowRegion,
    lin_instantiation: LinInstantiation,
    db: &'a ::salsa::Db,
}

impl<'a> KiReprExpansionBuilder<'a> {
    fn new(
        path: ItemPath,
        parent_ki_repr: KiRepr,
        body: HirLazyExprIdx,
        hir_lazy_expr_region: HirLazyExprRegion,
        argument_ki_reprs: &[KiRepr],
        lin_instantiation: LinInstantiation,
        db: &'a ::salsa::Db,
    ) -> Self {
        let hir_lazy_expr_region_data = hir_lazy_expr_region.data(db);
        let mut variable_ki_repr_map =
            HirLazyVariableMap::new(hir_lazy_expr_region_data.hir_lazy_variable_region().arena());
        for (hir_lazy_variable_idx, &argument_ki_repr) in std::iter::zip(
            hir_lazy_expr_region_data
                .hir_lazy_variable_region()
                .arena()
                .indices(),
            argument_ki_reprs,
        ) {
            variable_ki_repr_map.insert_new(hir_lazy_variable_idx, argument_ki_repr)
        }
        Self {
            path,
            parent_ki_repr,
            ki_domain_repr: parent_ki_repr.ki_domain_repr(db),
            body,
            hir_lazy_expr_region_data,
            hir_lazy_variable_ki_repr_map: variable_ki_repr_map,
            hir_lazy_expr_ki_repr_map: HirLazyExprMap::new2(
                hir_lazy_expr_region_data.hir_lazy_expr_arena(),
            ),
            hir_lazy_stmt_ki_repr_map: HirLazyStmtMap::new2(
                hir_lazy_expr_region_data.hir_lazy_stmt_arena(),
            ),
            root_hir_lazy_stmt_ki_reprs: smallvec![],
            hir_lazy_expr_control_flow_region: hir_lazy_expr_region.control_flow(db),
            lin_instantiation,
            db,
        }
    }
}

impl<'a> KiReprExpansionBuilder<'a> {
    fn build_all(&mut self) {
        let ki_domain_repr_guard =
            KiDomainReprGuard::new(self.db, self.parent_ki_repr, self.ki_domain_repr);
        match self.hir_lazy_expr_region_data.hir_lazy_expr_arena()[self.body] {
            HirLazyExprData::Block { stmts } => {
                self.root_hir_lazy_stmt_ki_reprs = self.build_stmts(ki_domain_repr_guard, stmts)
            }
            _ => todo!(),
        }
    }

    fn build_stmts(
        &mut self,
        mut ki_domain_repr_guard: KiDomainReprGuard<'a>,
        stmts: HirLazyStmtIdxRange,
    ) -> SmallVec<[KiRepr; 4]> {
        let mut ki_reprs = smallvec![];
        for stmt in stmts {
            if let Some(ki_repr) = self.build_stmt(&mut ki_domain_repr_guard, stmt) {
                ki_domain_repr_guard.after_stmt(ki_repr);
                ki_reprs.push(ki_repr)
            }
        }
        ki_reprs
    }

    /// returns None for those guaranteed to return the unit type without control flow
    ///
    /// includes:
    /// - let statements
    /// - discard without without control flow
    fn build_stmt(
        &mut self,
        ki_domain_repr_guard: &mut KiDomainReprGuard<'a>,
        stmt: HirLazyStmtIdx,
    ) -> Option<KiRepr> {
        let (opn, arguments) = match self.hir_lazy_expr_region_data.hir_lazy_stmt_arena()[stmt] {
            HirLazyStmtData::Let {
                ref pattern,
                initial_value,
            } => {
                let initial_value_ki_repr = self.build_expr(ki_domain_repr_guard, initial_value);
                match self.hir_lazy_expr_region_data.hir_lazy_pattern_arena()[pattern.pattern_idx()]
                {
                    HirLazyPatternData::Literal(_) => todo!(),
                    HirLazyPatternData::Ident { ident: _ } => {
                        debug_assert_eq!(pattern.variables().len(), 1);
                        let variable_idx = pattern.variables()[0];
                        self.hir_lazy_variable_ki_repr_map.insert_new(
                            variable_idx,
                            initial_value_ki_repr.with_source(
                                KiReprSource::Expansion {
                                    parent_ki_repr: self.parent_ki_repr,
                                    source: KiReprExpansionSource::LetVariable {
                                        stmt,
                                        variable_idx,
                                    },
                                },
                                self.db,
                            ),
                        );
                        match self.hir_lazy_expr_control_flow_region[initial_value] {
                            HasControlFlow::True => {
                                todo!();
                            }
                            HasControlFlow::False => {
                                return None;
                            }
                        }
                    }
                    HirLazyPatternData::Unit(_) => todo!(),
                    HirLazyPatternData::Tuple { path: _, fields: _ } => todo!(),
                    HirLazyPatternData::Props { path: _, fields: _ } => todo!(),
                    HirLazyPatternData::OneOf { options: _ } => todo!(),
                    HirLazyPatternData::Binding { ident: _, src: _ } => todo!(),
                    HirLazyPatternData::Range { start: _, end: _ } => todo!(),
                }
            }
            HirLazyStmtData::Return { result } => (
                KiOpn::Return,
                smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, result)
                )],
            ),
            HirLazyStmtData::Require {
                ref condition,
                return_ty,
            } => {
                let db = self.db;
                let default = ki_domain_repr_guard.new_ki_repr(
                    KiReprExpansionSource::RequireDefault { stmt },
                    KiOpn::Linket(Linket::new_ty_default(
                        return_ty,
                        &self.lin_instantiation,
                        db,
                    )),
                    smallvec![],
                    HasControlFlow::False,
                );
                (
                    KiOpn::Require,
                    smallvec![
                        KiArgumentRepr::Simple(self.build_condition(
                            ki_domain_repr_guard,
                            KiReprExpansionSource::RequireCondition { stmt },
                            condition
                        )),
                        KiArgumentRepr::Simple(default)
                    ],
                )
            }
            HirLazyStmtData::Assert { ref condition } => (
                KiOpn::Assert,
                smallvec![KiArgumentRepr::Simple(self.build_condition(
                    ki_domain_repr_guard,
                    KiReprExpansionSource::AssertCondition { stmt },
                    condition
                ))],
            ),
            HirLazyStmtData::Eval {
                expr_idx,
                discarded,
            } => {
                let expr_ki_repr = self.build_expr(ki_domain_repr_guard, expr_idx);
                match discarded {
                    true => match self.hir_lazy_expr_control_flow_region[stmt] {
                        HasControlFlow::True => (
                            KiOpn::EvalDiscarded,
                            smallvec![KiArgumentRepr::Simple(expr_ki_repr)],
                        ),
                        HasControlFlow::False => return None,
                    },
                    false => return Some(expr_ki_repr),
                }
            }
            HirLazyStmtData::IfElse {
                ref if_branch,
                ref elif_branches,
                ref else_branch,
            } => {
                let mut ki_domain_repr_guard = ki_domain_repr_guard.clone();
                let mut branches: SmallVec<[KiArgumentRepr; 4]> = smallvec![];
                let if_condition = self.build_condition(
                    &mut ki_domain_repr_guard,
                    KiReprExpansionSource::IfCondition { stmt },
                    &if_branch.condition,
                );
                branches.push(KiArgumentRepr::Branch {
                    condition: Some(if_condition),
                    stmts: self.build_stmts(
                        ki_domain_repr_guard.under_condition(if_condition),
                        if_branch.stmts,
                    ),
                });
                for (branch_idx, elif_branch) in elif_branches.iter().enumerate() {
                    let elif_condition = self.build_condition(
                        &mut ki_domain_repr_guard,
                        KiReprExpansionSource::ElifCondition {
                            stmt,
                            branch_idx: branch_idx.try_into().unwrap(),
                        },
                        &elif_branch.condition,
                    );
                    branches.push(KiArgumentRepr::Branch {
                        condition: Some(elif_condition),
                        stmts: self.build_stmts(
                            ki_domain_repr_guard.under_condition(elif_condition),
                            elif_branch.stmts,
                        ),
                    });
                }
                if let Some(else_branch) = else_branch {
                    branches.push(KiArgumentRepr::Branch {
                        condition: None,
                        stmts: self.build_stmts(ki_domain_repr_guard, else_branch.stmts()),
                    });
                }
                (KiOpn::Branches, branches)
            }
            HirLazyStmtData::Match {} => todo!(),
            HirLazyStmtData::Narrate {} => todo!(),
        };
        let ki_repr = ki_domain_repr_guard.new_stmt_ki_repr(stmt, opn, arguments);
        self.hir_lazy_stmt_ki_repr_map.insert_new(stmt, ki_repr);
        Some(ki_repr)
    }

    fn build_condition(
        &mut self,
        ki_domain_repr_guard: &mut KiDomainReprGuard<'a>,
        source: KiReprExpansionSource,
        condition: &HirLazyCondition,
    ) -> KiRepr {
        match *condition {
            HirLazyCondition::Be { src, ref pattern } => {
                let opn = KiOpn::Be {
                    pattern_data: self.build_pattern(pattern),
                };
                let arguments = smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, src)
                )];
                ki_domain_repr_guard.new_ki_repr(
                    source,
                    opn,
                    arguments,
                    self.hir_lazy_expr_control_flow_region[src],
                )
            }
            // todo: consider conversion
            HirLazyCondition::Other {
                hir_lazy_expr_idx,
                conversion,
            } => self.build_expr(ki_domain_repr_guard, hir_lazy_expr_idx),
        }
    }

    fn build_expr(
        &mut self,
        ki_domain_repr_guard: &mut KiDomainReprGuard<'a>,
        expr: HirLazyExprIdx,
    ) -> KiRepr {
        let ki_repr = self.build_expr_aux(ki_domain_repr_guard, expr);
        self.hir_lazy_expr_ki_repr_map.insert_new(expr, ki_repr);
        ki_repr
    }

    fn build_expr_aux(
        &mut self,
        ki_domain_repr_guard: &mut KiDomainReprGuard<'a>,
        expr: HirLazyExprIdx,
    ) -> KiRepr {
        let db = self.db;
        let hir_lazy_expr_arena = self.hir_lazy_expr_region_data.hir_lazy_expr_arena();
        let (opn, arguments) = match hir_lazy_expr_arena[expr] {
            HirLazyExprData::Literal(lit) => (KiOpn::Literal(lit), smallvec![]),
            HirLazyExprData::PrincipalEntityPath(path) => match path {
                PrincipalEntityPath::Module(_) => todo!(),
                PrincipalEntityPath::MajorItem(path) => match path {
                    MajorItemPath::Type(_) => todo!(),
                    MajorItemPath::Trait(_) => todo!(),
                    MajorItemPath::Form(path) => match path.kind(db) {
                        MajorFormKind::Ritchie(_) => todo!(),
                        MajorFormKind::Val => return KiRepr::new_val(path, db),
                        MajorFormKind::TypeAlias
                        | MajorFormKind::TypeVar
                        | MajorFormKind::Conceptual => unreachable!(),
                        MajorFormKind::StaticMut => todo!(),
                        MajorFormKind::StaticVar => todo!(),
                        MajorFormKind::Compterm => todo!(),
                    },
                },
                PrincipalEntityPath::TypeVariant(path) => (KiOpn::TypeVariant(path), smallvec![]),
            },
            HirLazyExprData::ConstSymbol(_) => todo!(),
            HirLazyExprData::Variable(var) => return self.hir_lazy_variable_ki_repr_map[var],
            HirLazyExprData::Binary { lopd, opr, ropd } => {
                let opn = KiOpn::Binary(opr);
                let arguments = smallvec![
                    KiArgumentRepr::Simple(self.build_expr(ki_domain_repr_guard, lopd)),
                    KiArgumentRepr::Simple(self.build_expr(ki_domain_repr_guard, ropd))
                ];
                (opn, arguments)
            }
            HirLazyExprData::Be { src, pattern: _ } => (
                KiOpn::Be {
                    pattern_data: todo!(),
                },
                smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, src)
                )],
            ),
            HirLazyExprData::Prefix {
                opr,
                opd_hir_expr_idx,
            } => {
                let opn = KiOpn::Prefix(opr);
                let arguments = smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, opd_hir_expr_idx)
                )];
                (opn, arguments)
            }
            HirLazyExprData::Suffix {
                opd_hir_expr_idx,
                opr,
            } => {
                let opn = KiOpn::Suffix(opr);
                let arguments = smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, opd_hir_expr_idx)
                )];
                (opn, arguments)
            }
            HirLazyExprData::Unveil {
                opd_hir_expr_idx,
                unveil_assoc_fn_path,
                ref instantiation,
            } => {
                let db = self.db;
                let opn = KiOpn::Linket(Linket::new_unveil_assoc_fn(
                    unveil_assoc_fn_path,
                    instantiation,
                    &self.lin_instantiation,
                    self.db,
                ));
                let arguments = smallvec![
                    KiArgumentRepr::Simple(self.build_expr(ki_domain_repr_guard, opd_hir_expr_idx)),
                    KiArgumentRepr::RuntimeConstants(ki_runtime_compterms_from_hir_instantiation(
                        instantiation,
                        db,
                    ))
                ];
                (opn, arguments)
            }
            HirLazyExprData::Unwrap { opd_hir_expr_idx } => {
                let opn = KiOpn::Unwrap {};
                let arguments = smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, opd_hir_expr_idx)
                )];
                (opn, arguments)
            }
            HirLazyExprData::TypeConstructorCall {
                path,
                ref instantiation,
                ref item_groups,
                ..
            } => {
                let opn = KiOpn::Linket(Linket::new_ty_constructor_fn(
                    path,
                    instantiation,
                    &self.lin_instantiation,
                    self.db,
                ));
                let mut arguments: SmallVec<[KiArgumentRepr; 4]> = smallvec![];
                self.build_item_groups(
                    instantiation,
                    item_groups,
                    ki_domain_repr_guard,
                    &mut arguments,
                );
                (opn, arguments)
            }
            HirLazyExprData::TypeVariantConstructorCall {
                path,
                ref instantiation,
                ref item_groups,
                ..
            } => {
                let opn = KiOpn::Linket(Linket::new_ty_variant_constructor_fn(
                    path,
                    instantiation,
                    &self.lin_instantiation,
                    self.db,
                ));
                let mut arguments: SmallVec<[KiArgumentRepr; 4]> = smallvec![];
                self.build_item_groups(
                    instantiation,
                    item_groups,
                    ki_domain_repr_guard,
                    &mut arguments,
                );
                (opn, arguments)
            }
            HirLazyExprData::FunctionRitchieItemCall {
                path,
                ref instantiation,
                ref item_groups,
                ..
            } => {
                let opn = match path.kind(db).ritchie() {
                    RitchieItemKind::Fn => KiOpn::Linket(Linket::new_major_ritchie_item(
                        path,
                        instantiation,
                        &self.lin_instantiation,
                        self.db,
                    )),
                    RitchieItemKind::Gn => {
                        let Some(MajorFormHirDefn::Ritchie(hir_defn)) = path.hir_defn(db) else {
                            unreachable!()
                        };
                        match hir_defn.body_with_hir_expr_region(db) {
                            Some((body, _)) => todo!(),
                            None => KiOpn::Linket(Linket::new_major_ritchie_item(
                                path,
                                instantiation,
                                &self.lin_instantiation,
                                self.db,
                            )),
                        }
                    }
                    RitchieItemKind::Vn => todo!(),
                    RitchieItemKind::Pn => todo!(),
                    RitchieItemKind::Qn => todo!(),
                    RitchieItemKind::Bn => todo!(),
                    RitchieItemKind::Sn => todo!(),
                    RitchieItemKind::Tn => todo!(),
                };
                let mut arguments: SmallVec<[KiArgumentRepr; 4]> = smallvec![];
                self.build_item_groups(
                    instantiation,
                    item_groups,
                    ki_domain_repr_guard,
                    &mut arguments,
                );
                (opn, arguments)
            }
            HirLazyExprData::AssocFunctionRitchieCall {
                path,
                ref instantiation,
                ref item_groups,
                ..
            } => {
                let opn = KiOpn::Linket(Linket::new_assoc_function_ritchie_item(
                    path,
                    instantiation,
                    &self.lin_instantiation,
                    self.db,
                ));
                let mut arguments: SmallVec<[KiArgumentRepr; 4]> = smallvec![];
                self.build_item_groups(
                    instantiation,
                    item_groups,
                    ki_domain_repr_guard,
                    &mut arguments,
                );
                (opn, arguments)
            }
            HirLazyExprData::PropsStructField {
                self_argument,
                self_ty,
                ident,
                ..
            } => (
                KiOpn::Linket(Linket::new_props_struct_field(
                    self_ty,
                    ident,
                    &self.lin_instantiation,
                    self.db,
                )),
                smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, self_argument)
                )],
            ),
            HirLazyExprData::MemoizedField {
                owner,
                path,

                ref instantiation,
                ..
            } => (
                KiOpn::Linket(Linket::new_memo_field(
                    path,
                    instantiation,
                    &self.lin_instantiation,
                    self.db,
                )),
                smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, owner)
                )],
            ),
            HirLazyExprData::MethodRitchieCall {
                self_argument,
                path,

                ref instantiation,
                ref item_groups,
                ..
            } => {
                let mut arguments = smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, self_argument)
                )];
                self.build_item_groups(
                    instantiation,
                    item_groups,
                    ki_domain_repr_guard,
                    &mut arguments,
                );
                (
                    KiOpn::Linket(Linket::new_method(
                        path,
                        instantiation,
                        &self.lin_instantiation,
                        self.db,
                    )),
                    arguments,
                )
            }
            HirLazyExprData::NewTuple { items: _ } => todo!(),
            HirLazyExprData::Index { owner, ref items } => {
                let mut arguments = smallvec![KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, owner)
                )];
                for &item in items {
                    arguments.push(KiArgumentRepr::Simple(
                        self.build_expr(ki_domain_repr_guard, item),
                    ))
                }
                // (ValOpn::Linket(Linket::new_index(self.db)), arguments)
                (KiOpn::Index, arguments)
            }
            HirLazyExprData::ConstructList {
                ref items,
                element_ty,
            } => (
                // todo: disambiguate between Vec, SmallVec, Array
                KiOpn::Linket(Linket::new_vec_constructor(
                    element_ty,
                    &self.lin_instantiation,
                    self.db,
                )),
                smallvec![KiArgumentRepr::Variadic(
                    items
                        .iter()
                        .map(|&item| { self.build_expr(ki_domain_repr_guard, item) })
                        .collect()
                )],
            ),
            HirLazyExprData::Block { stmts: _ } => todo!(),
            HirLazyExprData::EmptyHtmlTag {
                function_ident: _,
                arguments: _,
            } => todo!(),
            HirLazyExprData::Todo => todo!(),
            HirLazyExprData::Unreachable => todo!(),
            HirLazyExprData::AssocRitchie { .. } => todo!(),
            HirLazyExprData::As { opd, ty } => todo!(),
        };
        ki_domain_repr_guard.new_expr_ki_repr(
            expr,
            opn,
            arguments,
            self.hir_lazy_expr_control_flow_region[expr],
        )
    }

    // instantiation is needed for runtime constants
    fn build_item_groups(
        &mut self,
        instantiation: &HirInstantiation,
        item_groups: &[HirLazyCallListArgument],
        ki_domain_repr_guard: &mut KiDomainReprGuard<'a>,
        arguments: &mut SmallVec<[KiArgumentRepr; 4]>,
    ) {
        let db = self.db;
        for item_group in item_groups {
            match *item_group {
                HirLazyCallListArgument::Simple(item) => arguments.push(KiArgumentRepr::Simple(
                    self.build_expr(ki_domain_repr_guard, item),
                )),
                HirLazyCallListArgument::Variadic(ref items) => {
                    let items: SmallVec<_> = items
                        .iter()
                        .map(|&item| self.build_expr(ki_domain_repr_guard, item))
                        .collect();
                    arguments.push(KiArgumentRepr::Variadic(items))
                }
                HirLazyCallListArgument::Keyed(_, item) => arguments.push(KiArgumentRepr::Keyed(
                    item.map(|item| self.build_expr(ki_domain_repr_guard, item)),
                )),
            }
        }
        arguments.push(KiArgumentRepr::RuntimeConstants(
            ki_runtime_compterms_from_hir_instantiation(instantiation, db),
        ));
    }

    fn build_pattern(&mut self, pattern: &HirLazyBeVariablesPattern) -> KiPatternData {
        match pattern {
            HirLazyBeVariablesPattern::Literal => todo!(),
            HirLazyBeVariablesPattern::None => KiPatternData::None,
            HirLazyBeVariablesPattern::Some => KiPatternData::Some,
        }
    }

    fn finish(self) -> KiReprExpansion {
        KiReprExpansion::new(
            self.db,
            self.path,
            self.hir_lazy_variable_ki_repr_map,
            self.hir_lazy_expr_ki_repr_map,
            self.hir_lazy_stmt_ki_repr_map,
            self.root_hir_lazy_stmt_ki_reprs,
        )
    }
}

pub fn ki_runtime_compterms_from_hir_instantiation(
    instantiation: &HirInstantiation,
    db: &salsa::Db,
) -> SmallVec<[KiRuntimeCompterm; 4]> {
    instantiation
        .iter()
        .filter_map(|&(symbol, res)| match symbol {
            HirTemplateVariable::Compterm(symbol)
                if symbol.index(db).class() == HirTemplateVariableClass::Poly =>
            {
                Some(match res {
                    HirTermSymbolicVariableResolution::Explicit(arg) => match arg {
                        HirTemplateArgument::Vacant => todo!(),
                        HirTemplateArgument::Type(_) => todo!(),
                        HirTemplateArgument::Constant(constant) => match constant {
                            HirCompterm::Unit(_) => todo!(),
                            HirCompterm::Bool(_) => todo!(),
                            HirCompterm::Char(_) => todo!(),
                            HirCompterm::I8(_) => todo!(),
                            HirCompterm::I16(_) => todo!(),
                            HirCompterm::I32(_) => todo!(),
                            HirCompterm::I64(_) => todo!(),
                            HirCompterm::I128(_) => todo!(),
                            HirCompterm::ISize(_) => todo!(),
                            HirCompterm::U8(_) => todo!(),
                            HirCompterm::U16(_) => todo!(),
                            HirCompterm::U32(_) => todo!(),
                            HirCompterm::U64(_) => todo!(),
                            HirCompterm::U128(_) => todo!(),
                            HirCompterm::USize(_) => todo!(),
                            HirCompterm::R8(_) => todo!(),
                            HirCompterm::R16(_) => todo!(),
                            HirCompterm::R32(_) => todo!(),
                            HirCompterm::R64(_) => todo!(),
                            HirCompterm::R128(_) => todo!(),
                            HirCompterm::RSize(_) => todo!(),
                            HirCompterm::Symbol(_) => todo!(),
                            HirCompterm::TypeVariant(path) => KiRuntimeCompterm::new(
                                db,
                                KiRuntimeComptermData::TypeVariantPath(path),
                            ),
                            HirCompterm::StaticLifetime => todo!(),
                        },
                        HirTemplateArgument::Lifetime(_) => todo!(),
                        HirTemplateArgument::ContractedQuary(_) => todo!(),
                    },
                    HirTermSymbolicVariableResolution::SelfLifetime => {
                        todo!()
                    }
                    HirTermSymbolicVariableResolution::SelfContractedQuary(_) => {
                        todo!()
                    }
                })
            }
            _ => None,
        })
        .collect()
}

#[cfg(test)]
fn val_ki_repr_expansions(
    db: &::salsa::Db,
    module_path: ModulePath,
) -> Vec<(MajorFormPath, Option<KiReprExpansion>)> {
    val_ki_reprs(db, module_path)
        .into_iter()
        .map(|(path, ki_repr)| (path, ki_repr.expansion(db)))
        .collect()
}

#[test]
fn val_ki_repr_expansions_works() {
    // todo: why compiler needs this line to work?
    use husky_ast::test_helpers::AstTestUtils;
    DB::ast_rich_test_debug_with_db(
        val_ki_repr_expansions,
        &AstTestConfig::new(
            "val_ki_repr_expansions",
            FileExtensionConfig::Markdown,
            TestDomainsConfig::VAL,
        ),
    )
}

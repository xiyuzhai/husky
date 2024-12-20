use crate::*;
use husky_entity_path::path::{assoc_item::AssocItemPath, ItemPath, ItemPathId};
use husky_eth_term::term::EthTerm;
use husky_fly_term::FlyTermBase;
use husky_hir_ty::trai::HirTrait;

use husky_syn_expr::syndicates::{
    trais::TraitsSyndicate, TemplateParameterSyndicateVariant, TemplateSynParameterData,
};
use path::impl_block::{ImplBlockPath, TypeSketch};
use smallvec::SmallVec;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HirTemplateParameter {
    symbol: HirTemplateVariable,
    data: HirTemplateParameterData,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub enum HirTemplateParameterData {
    Type {
        ident: Ident,
        traits: SmallVec<[HirTrait; 4]>,
    },
    Constant {
        ident: Ident,
        ty: HirType,
    },
    Lifetime {
        label: Label,
    },
    Place {
        label: Label,
    },
}

impl HirTemplateParameter {
    pub(crate) fn from_syn(
        syndicate: &TemplateSynParameterData,
        builder: &HirDeclBuilder,
    ) -> Option<Self> {
        let EthTerm::SymbolicVariable(symbol) = builder.current_variable_term(syndicate.symbol())
        else {
            todo!()
        };
        let db = builder.db();
        let symbol = HirTemplateVariable::from_eth(symbol, db)?;
        let data = match *syndicate.variant() {
            TemplateParameterSyndicateVariant::Type {
                ident_token,
                ref traits,
            } => HirTemplateParameterData::Type {
                ident: ident_token.ident(),
                traits: match *traits {
                    Some(TraitsSyndicate {
                        ref trai_syn_expr_idxs,
                        ..
                    }) => trai_syn_expr_idxs
                        .iter()
                        .map(|&trai_syn_expr_idx| {
                            let sem_expr_region_data = &builder.sem_expr_region_data();
                            let terms = sem_expr_region_data.fly_term_region().terms();
                            let trai_term = match sem_expr_region_data
                                .syn_root_expr_term(trai_syn_expr_idx)
                                .expect("some")
                                .expect("ok")
                                .base_resolved_inner(terms)
                            {
                                FlyTermBase::Eth(trai_term) => trai_term,
                                FlyTermBase::Sol(_) => todo!(),
                                FlyTermBase::Hol(_) => todo!(),
                                FlyTermBase::Place => todo!(),
                            };
                            HirTrait::from_eth(trai_term, db)
                        })
                        .collect(),
                    None => smallvec![],
                },
            },
            TemplateParameterSyndicateVariant::Compterm {
                ident_token,
                ty_expr,
                ..
            } => {
                let ident = ident_token.ident();
                HirTemplateParameterData::Constant {
                    ident,
                    ty: builder.hir_ty(ty_expr).unwrap(),
                }
            }
            TemplateParameterSyndicateVariant::Lifetime { label_token } => {
                HirTemplateParameterData::Lifetime {
                    label: label_token.label(),
                }
            }
            TemplateParameterSyndicateVariant::Place { label_token } => {
                HirTemplateParameterData::Place {
                    label: label_token.label(),
                }
            }
        };
        Some(Self { data, symbol })
    }

    pub fn symbol(&self) -> HirTemplateVariable {
        self.symbol
    }

    pub fn data(&self) -> &HirTemplateParameterData {
        &self.data
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct HirTemplateParameters(SmallVec<[HirTemplateParameter; 2]>);

impl HirTemplateParameters {
    pub(crate) fn from_syn(
        syndicates: &[TemplateSynParameterData],
        builder: &HirDeclBuilder,
    ) -> Self {
        HirTemplateParameters(
            syndicates
                .iter()
                .filter_map(|syndicate| HirTemplateParameter::from_syn(syndicate, builder))
                .collect(),
        )
    }
}

impl<'a> std::iter::IntoIterator for &'a HirTemplateParameters {
    type Item = &'a HirTemplateParameter;

    type IntoIter = impl Iterator<Item = &'a HirTemplateParameter> + 'a;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl std::ops::Deref for HirTemplateParameters {
    type Target = [HirTemplateParameter];

    fn deref(&self) -> &Self::Target {
        self.0.deref()
    }
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq)]
pub struct HirTemplateParameterStats {
    pub self_ty: u8,
    pub tys: u8,
    pub constants: u8,
    pub lifetimes: u8,
    pub places: u8,
}

impl std::ops::AddAssign<Self> for HirTemplateParameterStats {
    fn add_assign(&mut self, rhs: Self) {
        self.self_ty += rhs.self_ty;
        self.tys += rhs.tys;
        self.constants += rhs.constants;
        self.lifetimes += rhs.lifetimes;
        self.places += rhs.places;
    }
}

/// for associated items, the parent's template parameters count
#[salsa::tracked]
pub fn item_hir_template_parameter_stats(
    db: &::salsa::Db,
    item_path_id: ItemPathId,
) -> Option<HirTemplateParameterStats> {
    let path = item_path_id.item_path(db);
    let mut stats = HirTemplateParameterStats {
        self_ty: 0,
        tys: 0,
        constants: 0,
        lifetimes: 0,
        places: 0,
    };
    let hir_decl = path.hir_decl(db)?;
    if let Some(template_parameters) = hir_decl.template_parameters(db) {
        for param in template_parameters {
            match param.data {
                HirTemplateParameterData::Type { .. } => stats.tys += 1,
                HirTemplateParameterData::Constant { .. } => stats.constants += 1,
                HirTemplateParameterData::Lifetime { .. } => stats.lifetimes += 1,
                HirTemplateParameterData::Place { .. } => stats.places += 1,
            }
        }
    }
    use ::husky_print_utils::p;
    use ::salsa::DebugWithDb;
    match path {
        ItemPath::AssocItem(assoc_item_path) => match assoc_item_path {
            AssocItemPath::TypeItem(ty_item_path) => {
                stats +=
                    item_hir_template_parameter_stats(db, *ty_item_path.impl_block(db)).unwrap()
            }
            AssocItemPath::TraitItem(trai_item_path) => {
                stats.self_ty += 1;
                stats +=
                    item_hir_template_parameter_stats(db, *trai_item_path.trai_path(db)).unwrap()
            }
            AssocItemPath::TraitForTypeItem(trai_for_ty_item_path) => {
                stats +=
                    item_hir_template_parameter_stats(db, *trai_for_ty_item_path.impl_block(db))
                        .unwrap()
            }
        },
        ItemPath::TypeVariant(_, ty_variant_path) => {
            stats +=
                item_hir_template_parameter_stats(db, *ty_variant_path.parent_ty_path(db)).unwrap()
        }
        ItemPath::ImplBlock(impl_block_path) => match impl_block_path {
            ImplBlockPath::TypeImplBlock(_) => (),
            ImplBlockPath::TraitForTypeImplBlock(trai_for_ty_impl_block_path) => {
                match trai_for_ty_impl_block_path.ty_sketch(db) {
                    TypeSketch::DeriveAny => stats.self_ty += 1,
                    TypeSketch::Path(_) => (),
                }
            }
        },
        _ => (),
    }
    debug_assert!(stats.self_ty <= 1);
    Some(stats)
}

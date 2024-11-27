use self::signature::trai_for_ty_item::assoc_ty::TraitForTypeAssocTypeEthSignatureBuilder;

use super::*;
use assoc_item::trai_for_ty_item::TraitForTypeItemEthSignatureBuilder;
use husky_dec_signature::signature::{
    impl_block::trai_for_ty_impl_block::{DeclarativeSelfType, TraitForTypeImplBlockDecTemplate},
    HasDecTemplate,
};
use husky_entity_path::path::impl_block::trai_for_ty_impl_block::TraitForTypeImplBlockPath;
use husky_entity_tree::node::HasAssocItemPaths;
use husky_eth_term::term::symbolic_variable::EthSymbolicVariable;
use husky_term_prelude::TypeFinalDestinationExpectation;
use salsa::DebugWithDb;
use vec_like::VecMapGetEntry;

#[salsa::interned(constructor = new)]
pub struct TraitForTypeImplBlockEthTemplate {
    pub path: TraitForTypeImplBlockPath,
    #[return_ref]
    pub template_parameters: EthTemplateParameters,
    pub trai: EthTerm,
    pub self_ty_refined: EtherealSelfTypeInTraitImpl,
}

impl TraitForTypeImplBlockEthTemplate {
    pub fn self_ty(self, db: &::salsa::Db) -> EthTerm {
        self.self_ty_refined(db).term()
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum EtherealSelfTypeInTraitImpl {
    PathLeading(EthTerm),
    DeriveAny(EthSymbolicVariable),
}

impl EtherealSelfTypeInTraitImpl {
    pub fn term(self) -> EthTerm {
        match self {
            EtherealSelfTypeInTraitImpl::PathLeading(ty_term) => ty_term,
            EtherealSelfTypeInTraitImpl::DeriveAny(ty_term_symbol) => ty_term_symbol.into(),
        }
    }
}

impl EthInstantiate for EtherealSelfTypeInTraitImpl {
    type Output = EthTerm;

    fn instantiate(
        self,
        instantiation: &EthInstantiation,
        ctx: impl IsEthTermContextRef,
        db: &::salsa::Db,
    ) -> Self::Output {
        match self {
            EtherealSelfTypeInTraitImpl::PathLeading(term) => {
                term.instantiate(instantiation, ctx, db)
            }
            EtherealSelfTypeInTraitImpl::DeriveAny(term_symbol) => {
                term_symbol.instantiate(instantiation, ctx, db)
            }
        }
    }
}

impl EtherealSelfTypeInTraitImpl {
    fn from_dec(db: &::salsa::Db, declarative_self_ty: DeclarativeSelfType) -> EthTermResult<Self> {
        Ok(match declarative_self_ty {
            DeclarativeSelfType::Path(declarative_term) => {
                EtherealSelfTypeInTraitImpl::PathLeading(EthTerm::ty_from_dec(
                    db,
                    declarative_term,
                )?)
            }
            DeclarativeSelfType::DerivedAny(dec_symbolic_variable) => {
                EtherealSelfTypeInTraitImpl::DeriveAny(EthSymbolicVariable::from_dec(
                    db,
                    dec_symbolic_variable,
                )?)
            }
        })
    }

    pub fn parameter_variable(self) -> Option<EthSymbolicVariable> {
        match self {
            EtherealSelfTypeInTraitImpl::PathLeading(_) => None,
            EtherealSelfTypeInTraitImpl::DeriveAny(symbol) => Some(symbol),
        }
    }
}

impl HasEthTemplate for TraitForTypeImplBlockPath {
    type EthTemplate = TraitForTypeImplBlockEthTemplate;

    fn eth_template(self, db: &::salsa::Db) -> EthSignatureResult<Self::EthTemplate> {
        trai_for_ty_impl_block_eth_template(db, self)
    }
}

#[salsa::tracked]
fn trai_for_ty_impl_block_eth_template(
    db: &::salsa::Db,
    path: TraitForTypeImplBlockPath,
) -> EthSignatureResult<TraitForTypeImplBlockEthTemplate> {
    TraitForTypeImplBlockEthTemplate::from_dec(db, path, path.dec_template(db)?)
}

impl TraitForTypeImplBlockEthTemplate {
    fn from_dec(
        db: &::salsa::Db,
        path: TraitForTypeImplBlockPath,
        dec_template: TraitForTypeImplBlockDecTemplate,
    ) -> EthSignatureResult<Self> {
        let template_parameters =
            EthTemplateParameters::from_dec(db, dec_template.template_parameters(db))?;
        let trai = EthTerm::from_dec(
            db,
            dec_template.trai(db),
            TypeFinalDestinationExpectation::Any,
        )?;
        let self_ty = EtherealSelfTypeInTraitImpl::from_dec(db, dec_template.self_ty(db))?;
        Ok(Self::new(db, path, template_parameters, trai, self_ty))
    }
}

pub type TraitForTypeImplBlockSignatureTemplates = SmallVec<[TraitForTypeImplBlockEthTemplate; 2]>;

#[salsa::interned(constructor = new)]
pub struct TraitForTypeImplBlockEthSignatureBuilderItd {
    pub template: TraitForTypeImplBlockEthTemplate,
    pub instantiation_builder: EthInstantiationBuilder,
    pub context_itd: EthTermContextItd,
}

impl TraitForTypeImplBlockEthTemplate {
    /// try to give a partial instantiation such that `self_ty` is equal to `target_ty`
    /// returns `Nothing` when template matching failed
    #[inline(always)]
    pub fn instantiate_ty<'db>(
        self,
        target_ty_arguments: &'db [EthTerm],
        target_ty_term: EthTerm,
        context_itd: EthTermContextItd,
        db: &'db ::salsa::Db,
    ) -> EthSignatureMaybeResult<TraitForTypeImplBlockEthSignatureBuilderItd> {
        let mut builder = self.template_parameters(db).empty_instantiation_builder(
            self.path(db).into(),
            true,
            context_itd.context_ref(db),
        );
        match self.self_ty_refined(db) {
            EtherealSelfTypeInTraitImpl::PathLeading(self_ty_term) => {
                builder.try_add_rules_from_application(self_ty_term, target_ty_arguments, db)?;
                JustOk(TraitForTypeImplBlockEthSignatureBuilderItd::new(
                    db,
                    self,
                    builder,
                    context_itd,
                ))
            }
            EtherealSelfTypeInTraitImpl::DeriveAny(symbol) => {
                let JustOk(()) = builder.try_add_symbol_rule(symbol, target_ty_term) else {
                    unreachable!("this can't go wrong because instantiation was empty")
                };
                JustOk(TraitForTypeImplBlockEthSignatureBuilderItd::new(
                    db,
                    self,
                    builder,
                    context_itd,
                ))
            }
        }
    }
}

impl TraitForTypeImplBlockEthSignatureBuilderItd {
    pub fn try_into_signature(self, db: &::salsa::Db) -> Option<TraitForTypeImplBlockEthSignature> {
        let instantiation = &self.instantiation_builder(db).try_into_instantiation()?;
        let ctx = self.context_itd(db).context_ref(db);
        let template = self.template(db);
        Some(TraitForTypeImplBlockEthSignature {
            path: template.path(db),
            trai: template.trai(db).instantiate(instantiation, ctx, db),
            self_ty: template.self_ty(db).instantiate(instantiation, ctx, db),
        })
    }

    /// normally further instantiation comes from methods or associated fns/gns/functions
    /// but this serves as a useful shortcut for traits like `Unveil`
    /// return `Nothing` when template matching failed
    pub fn instantiate_trai(
        self,
        target_trai_arguments: &[EthTerm],
        db: &::salsa::Db,
    ) -> EthSignatureMaybeResult<Self> {
        let mut builder = self.instantiation_builder(db);
        let template = self.template(db);
        builder.try_add_rules_from_application(template.trai(db), target_trai_arguments, db)?;
        JustOk(Self::new(db, template, builder, self.context_itd(db)))
    }

    /// for better caching, many common traits use "Output" as an associated
    /// only use this when you are sure the trait has an associated type
    /// named "Output"
    pub fn assoc_output_signature_builder(
        self,
        db: &::salsa::Db,
    ) -> EthSignatureResult<TraitForTypeAssocTypeEthSignatureBuilder> {
        trai_for_ty_impl_block_with_ty_instantiated_assoc_output_ethereal_signature_builder(
            db, self,
        )
    }

    pub fn assoc_item_signature_builder(
        self,
        db: &::salsa::Db,
        ident: Ident,
    ) -> EthSignatureResult<TraitForTypeItemEthSignatureBuilder> {
        trai_for_ty_impl_block_item_eth_signature_builder_with_ty_instantiated(db, self, ident)
    }
}

#[salsa::tracked]
fn trai_for_ty_impl_block_with_ty_instantiated_assoc_output_ethereal_signature_builder(
    db: &::salsa::Db,
    template: TraitForTypeImplBlockEthSignatureBuilderItd,
) -> EthSignatureResult<TraitForTypeAssocTypeEthSignatureBuilder> {
    match trai_for_ty_impl_block_item_eth_signature_builder_with_ty_instantiated(
        db,
        template,
        coword_menu(db).camel_case_output_ident(),
    )? {
        TraitForTypeItemEthSignatureBuilder::AssocType(item_template) => Ok(item_template),
        _ => unreachable!(),
    }
}

#[salsa::tracked]
fn trai_for_ty_impl_block_item_eth_signature_builder_with_ty_instantiated(
    db: &::salsa::Db,
    signature_builder: TraitForTypeImplBlockEthSignatureBuilderItd,
    ident: Ident,
) -> EthSignatureResult<TraitForTypeItemEthSignatureBuilder> {
    let item_path = signature_builder
        .template(db)
        .path(db)
        .assoc_item_paths(db)
        .get_entry(ident)
        .ok_or(
            EthSignatureError::NoSuchItemInTraitForTypeImplBlockEthSignatureBuilder {
                signature_builder,
                ident,
            },
        )?
        .1;
    let item_eth_template = item_path.eth_template(db)?;
    Ok(item_eth_template.inherit_instantiation_builder(db, signature_builder))
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct TraitForTypeImplBlockEthSignature {
    path: TraitForTypeImplBlockPath,
    trai: EthTerm,
    self_ty: EthTerm,
}

impl TraitForTypeImplBlockEthSignature {
    pub fn path(&self) -> TraitForTypeImplBlockPath {
        self.path
    }

    pub fn trai(&self) -> EthTerm {
        self.trai
    }

    pub fn ty(&self) -> EthTerm {
        self.self_ty
    }
}

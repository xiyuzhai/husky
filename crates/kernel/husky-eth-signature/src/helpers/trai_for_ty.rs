use super::*;
use crate::signature::{
    attr::derive::HasDeriveAttrShardEthTemplates,
    impl_block::trai_for_ty_impl_block::{
        TraitForTypeImplBlockEthSignatureBuilderItd, TraitForTypeImplBlockEthTemplate,
        TraitForTypeImplBlockSignatureTemplates,
    },
    HasEthTemplate,
};
use either::*;
use husky_entity_kind::ritchie::RitchieItemKind;
use husky_entity_path::path::major_item::{
    trai::{PreludeTraitPath, TraitPath},
    ty::TypePath,
};
use husky_entity_tree::{
    helpers::trai_side_derive_any_trai_for_ty_impl_block_paths_map,
    helpers::trai_side_path_leading_trai_for_ty_impl_block_paths_map,
    helpers::ty_side_trai_for_ty_impl_block_paths_map,
};
use husky_eth_term::{context::EthTermContextItd, term::application::TermFunctionReduced};
use husky_term_prelude::ritchie::{RitchieKind, RitchieTypeKind};
use signature::package::PackageEthSignatureData;

pub struct TraitForTypeImplBlockEthTemplates<'a> {
    trai_side_derive_any: &'a [TraitForTypeImplBlockEthTemplate],
    trai_side_path_leading: &'a [TraitForTypeImplBlockEthTemplate],
    ty_side: &'a [TraitForTypeImplBlockEthTemplate],
}

impl<'a> TraitForTypeImplBlockEthTemplates<'a> {
    pub fn iter(self) -> impl Iterator<Item = TraitForTypeImplBlockEthTemplate> + 'a {
        (self
            .trai_side_derive_any
            .iter()
            .chain(self.trai_side_path_leading.iter())
            .chain(self.ty_side.iter()))
        .copied()
    }
}

pub fn trai_path_for_ty_path_impl_block_eth_templates<'a>(
    db: &'a ::salsa::Db,
    trai_path: TraitPath,
    ty_path: TypePath,
) -> EthSignatureResult<TraitForTypeImplBlockEthTemplates<'a>> {
    let does_ty_path_derive_trai_path = ty_path.derive_attr_eth_templates(db, trai_path)?.is_some();
    Ok(TraitForTypeImplBlockEthTemplates {
        trai_side_derive_any: if does_ty_path_derive_trai_path {
            trai_side_derive_any_eth_templates(db, trai_path).as_ref()?
        } else {
            &[]
        },
        // todo: ty_kind
        trai_side_path_leading: trai_side_path_leading_eth_templates(db, trai_path, ty_path)?
            .unwrap_or(&[]),
        ty_side: ty_side_trai_for_ty_impl_block_signature_templates(db, trai_path, ty_path)
            .into_result_option()?
            .unwrap_or(&[]),
    })
}
/// given a trait path and a ty term, find all the implementation blocks and return their ethereal signature builders
pub fn trai_path_for_ty_term_impl_block_eth_signature_builders<'db>(
    db: &'db ::salsa::Db,
    trai_path: TraitPath,
    ty_term: EthTerm,
    context_itd: EthTermContextItd,
) -> EthSignatureResult<SmallVec<[TraitForTypeImplBlockEthSignatureBuilderItd; 2]>> {
    let application_expansion = ty_term.application_expansion(db);
    let arguments = application_expansion.arguments(db);
    let TermFunctionReduced::TypeOntology(ty_path) = application_expansion.function() else {
        unreachable!()
    };
    let mut builders: SmallVec<[TraitForTypeImplBlockEthSignatureBuilderItd; 2]> = smallvec![];
    for template in trai_path_for_ty_path_impl_block_eth_templates(db, trai_path, ty_path)?.iter() {
        match template.instantiate_ty(arguments, ty_term, context_itd, db) {
            JustOk(builder) => builders.push(builder),
            JustErr(_) => todo!(),
            Nothing => todo!(),
        }
    }
    Ok(builders)
}

// todo: check argument ty trai satisfaction
pub fn trai_path_for_ty_term_impl_block_ethereal_signature_builder_exists<'db>(
    db: &'db ::salsa::Db,
    trai_path: TraitPath,
    ty_term: EthTerm,
    context_itd: EthTermContextItd,
) -> EthSignatureResult<bool> {
    match ty_term {
        EthTerm::SymbolicVariable(_) => return Ok(false), // ad hoc
        EthTerm::AbstractVariable(_) => todo!(),
        EthTerm::Ritchie(ritchie) => match ritchie.ritchie_kind(db) {
            RitchieKind::Type(ritchie_ty_kind) => match ritchie_ty_kind {
                RitchieTypeKind::Item(ritchie_item_kind) => match ritchie_item_kind {
                    RitchieItemKind::Fn => match trai_path.refine(db) {
                        Left(prelude_trai_path) => {
                            return Ok(match prelude_trai_path {
                                PreludeTraitPath::Clone | PreludeTraitPath::Copy => true,
                                _ => false,
                            })
                        }
                        Right(_) => todo!(),
                    },
                    RitchieItemKind::Gn => todo!(),
                    RitchieItemKind::Vn => todo!(),
                    RitchieItemKind::Pn => todo!(),
                    RitchieItemKind::Qn => todo!(),
                    RitchieItemKind::Bn => todo!(),
                    RitchieItemKind::Sn => todo!(),
                    RitchieItemKind::Tn => todo!(),
                },
                // ad hoc, should check whether there are variables captured
                RitchieTypeKind::Closure(_) => return Ok(false),
            },
            RitchieKind::Trait(_) => todo!(),
        },
        EthTerm::TypeAsTraitItem(_) => todo!(),
        _ => (),
    }
    let application_expansion = ty_term.application_expansion(db);
    let function = application_expansion.function();
    let arguments = application_expansion.arguments(db);
    match function {
        TermFunctionReduced::TypeOntology(ty_path) => {
            for template in
                trai_path_for_ty_path_impl_block_eth_templates(db, trai_path, ty_path)?.iter()
            {
                match template.instantiate_ty(arguments, ty_term, context_itd, db) {
                    JustOk(_builder) => return Ok(true),
                    JustErr(e) => return Err(e),
                    Nothing => continue,
                }
            }
            Ok(false)
        }
        TermFunctionReduced::TypeVar(ty_var_path) => {
            // use husky_print_utils::p;
            // use salsa::DebugWithDb;

            // p!(ty_var_path.debug(db), trai_path.debug(db));
            // todo!()
            // ad hoc
            Ok(false)
        }
        TermFunctionReduced::Trait(_) => todo!(),
        TermFunctionReduced::Other(_) => todo!(),
    }
}

// todo: cache this, context could be simplified to increase caching rate
#[deprecated(note = "we should probably use a better notion")]
pub fn is_ty_term_always_copyable<'db>(
    ty_term: EthTerm,
    db: &'db ::salsa::Db,
) -> EthSignatureResult<Option<bool>> {
    let context_itd = EthTermContextItd::new_generic(db);
    let Some(item_path_menu) = ty_term.item_path_menu(db) else {
        return Ok(None);
    };
    let copy_trai = item_path_menu.copy_trai_path();
    trai_path_for_ty_term_impl_block_ethereal_signature_builder_exists(
        db,
        copy_trai,
        ty_term,
        context_itd,
    )
    .map(Some)
}

// trait side

#[salsa::tracked(return_ref)]
fn trai_side_derive_any_eth_templates(
    db: &::salsa::Db,
    trai_path: TraitPath,
) -> EthSignatureResult<SmallVec<[TraitForTypeImplBlockEthTemplate; 2]>> {
    trai_side_derive_any_trai_for_ty_impl_block_paths_map(db, trai_path)
        .iter()
        .map(|path| path.eth_template(db))
        .collect()
}

fn trai_side_path_leading_eth_templates(
    db: &::salsa::Db,
    trai_path: TraitPath,
    ty_path: TypePath,
) -> EthSignatureResult<Option<&[TraitForTypeImplBlockEthTemplate]>> {
    match trai_side_path_leading_trai_for_ty_impl_block_eth_templates_map(db, trai_path)
        .get_value(ty_path)
    {
        Some(Ok(v)) => Ok(Some(v)),
        Some(Err(e)) => Err(*e),
        None => Ok(None),
    }
}

#[salsa::tracked(return_ref)]
fn trai_side_path_leading_trai_for_ty_impl_block_eth_templates_map(
    db: &::salsa::Db,
    trai_path: TraitPath,
) -> SmallVecPairMap<TypePath, EthSignatureResult<SmallVec<[TraitForTypeImplBlockEthTemplate; 2]>>, 8>
{
    trai_side_path_leading_trai_for_ty_impl_block_paths_map(db, trai_path)
        .map_collect(|paths| paths.iter().map(|path| path.eth_template(db)).collect())
}

// type side

pub fn ty_side_trai_for_ty_impl_block_signature_templates(
    db: &::salsa::Db,
    trai_path: TraitPath,
    ty_path: TypePath,
) -> EthSignatureMaybeResult<&[TraitForTypeImplBlockEthTemplate]> {
    match ty_side_impl_block_signature_templates_map(db, ty_path).get_value(trai_path) {
        Some(result) => match result {
            Ok(templates) => JustOk(templates),
            Err(e) => JustErr(*e),
        },
        None => Nothing,
    }
}

#[salsa::tracked(return_ref)]
fn ty_side_impl_block_signature_templates_map(
    db: &::salsa::Db,
    ty_path: TypePath,
) -> SmallVecPairMap<TraitPath, EthSignatureResult<TraitForTypeImplBlockSignatureTemplates>, 2> {
    ty_side_trai_for_ty_impl_block_paths_map(db, ty_path)
        .map_collect(|paths| paths.iter().map(|path| path.eth_template(db)).collect())
}

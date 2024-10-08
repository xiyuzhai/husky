use super::*;
use husky_entity_path::path::major_item::ty::{PreludeIndirectionTypePath, PreludeTypePath};
use husky_eth_signature::{
    context::EthTermContextRef,
    error::EthSignatureResult,
    signature::{
        assoc_item::ty_item::memo::HasTypeMemoizedFieldEthSignature,
        major_item::ty::HasPropsFieldEthSignature, package::PackageEthSignatureData,
    },
};
use husky_eth_term::term::application::{EthApplication, TermFunctionReduced};

pub(super) fn eth_ty_field_dispatch<'db>(
    db: &'db ::salsa::Db,
    ty_term: EthTerm,
    ident: Ident,
    indirections: FlyIndirections,
    ctx: EthTermContextRef,
) -> FlyTermMaybeResult<FlyFieldInstanceDispatch> {
    // divide into cases for memoization
    match ty_term {
        EthTerm::ItemPath(ItemPathTerm::TypeOntology(ty_path)) => {
            eth_ty_ontology_path_ty_field_dispatch(db, ty_path, ident, indirections, ctx)
        }
        EthTerm::Application(ty_term) => {
            eth_term_application_ty_field_dispatch(db, ty_term, ident, indirections, ctx)
        }
        _ => Nothing,
    }
}

pub(crate) fn eth_ty_ontology_path_ty_field_dispatch<'db>(
    db: &'db ::salsa::Db,
    ty_path: TypePath,
    ident: Ident,
    indirections: FlyIndirections,
    ctx: EthTermContextRef,
) -> FlyTermMaybeResult<FlyFieldInstanceDispatch> {
    eth_ty_field_dispatch_aux(db, ty_path, &[], ident, indirections, ctx)
}

pub(crate) fn eth_term_application_ty_field_dispatch<'db>(
    db: &'db ::salsa::Db,
    ty_term: EthApplication,
    ident: Ident,
    indirections: FlyIndirections,
    ctx: EthTermContextRef,
) -> FlyTermMaybeResult<FlyFieldInstanceDispatch> {
    let application_expansion = ty_term.application_expansion(db);
    match application_expansion.function() {
        TermFunctionReduced::TypeOntology(ty_path) => eth_ty_field_dispatch_aux(
            db,
            ty_path,
            application_expansion.arguments(db),
            ident,
            indirections,
            ctx,
        ),
        TermFunctionReduced::TypeVar(_) => todo!(),
        TermFunctionReduced::Trait(_) | TermFunctionReduced::Other(_) => Nothing,
    }
}

fn eth_ty_field_dispatch_aux<'db>(
    db: &'db ::salsa::Db,
    ty_path: TypePath,
    arguments: &'db [EthTerm],
    ident: Ident,
    mut indirections: FlyIndirections,
    ctx: EthTermContextRef,
) -> FlyTermMaybeResult<FlyFieldInstanceDispatch> {
    match ty_path.refine(db) {
        Left(PreludeTypePath::Indirection(prelude_indirection_ty_path)) => {
            match prelude_indirection_ty_path {
                PreludeIndirectionTypePath::Ref => todo!(),
                PreludeIndirectionTypePath::RefMut => todo!(),
                PreludeIndirectionTypePath::Leash => {
                    indirections.add(FlyIndirection::Leash);
                    if arguments.len() != 1 {
                        todo!()
                    }
                    return eth_ty_field_dispatch(db, arguments[0], ident, indirections, ctx);
                }
                PreludeIndirectionTypePath::At => todo!(),
            }
        }
        _ => (),
    }
    if let Some(regular_field_ethereal_signature) = ty_path
        .props_field_ethereal_signature(db, arguments, ident)
        .into_result_option()?
    {
        return JustOk(FlyFieldInstanceDispatch {
            indirections,
            signature: regular_field_ethereal_signature.into(),
        });
    };

    if let Some(memo_field_ethereal_signature) = ty_path
        .ty_memo_field_ethereal_signature(arguments, ident, ctx, db)
        .into_result_option()?
    {
        return JustOk(FlyFieldInstanceDispatch {
            indirections,
            signature: memo_field_ethereal_signature.into(),
        });
    }
    // todo!("trai for ty memoized field");
    // ad hoc
    // needs to consider `Deref` `DerefMut` `Carrier`
    Nothing
}

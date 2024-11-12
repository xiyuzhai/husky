use super::*;
use husky_eth_signature::helpers::trai_for_ty::ty_side_trai_for_ty_impl_block_signature_templates;

pub(super) fn ethereal_owner_ty_int_index_signature(
    engine: &mut impl FlyTermEngineMut,
    syn_expr_idx: SynExprIdx,
    owner_ty: EthTerm,
    custom_ty_path: OtherTypePath,
    owner_ty_arguments: &[EthTerm],
    index_ty: FlyTerm,
    final_place: FlyQuary,
) -> FlyTermMaybeResult<FlyIndexSignature> {
    if !coersible_to_int(engine, index_ty) {
        return Nothing;
    };
    let db = engine.db();
    let element_ty = ty_side_trai_for_ty_impl_block_signature_templates(
        db,
        engine.item_path_menu().int_index_trai_path(),
        custom_ty_path.into(),
    )?
    .iter()
    .filter_map(|template| {
        template
            .instantiate_ty(owner_ty_arguments, owner_ty, engine.context_itd(), db)
            .into_option_result()
    })
    .next()??
    .assoc_output_signature_builder(db)?
    .try_into_signature(db)
    .expect("fully instantiated")
    .ty_term();
    JustOk(FlyIndexSignature::Int {
        element_ty: FlyTerm::new_eth(final_place, element_ty),
    })
}

fn coersible_to_int(engine: &mut impl FlyTermEngineMut, index_ty: FlyTerm) -> bool {
    match index_ty.base_term_data(engine) {
        FlyTermData::Literal(_) => unreachable!(),
        FlyTermData::TypeOntology {
            refined_ty_path, ..
        } => match refined_ty_path {
            Left(PreludeTypePath::Num(PreludeNumTypePath::Int(_))) => true,
            _ => false,
        },
        FlyTermData::Trait { .. } => todo!(),
        FlyTermData::Curry { .. } => false,
        FlyTermData::Hole(hole_kind, _) => match hole_kind {
            HoleKind::UnspecifiedIntegerType => true,
            HoleKind::UnspecifiedFloatType => false,
            HoleKind::ImplicitType | HoleKind::AnyOriginal | HoleKind::AnyDerived => false,
        },
        FlyTermData::Sort(_) => false,
        FlyTermData::Ritchie {
            ritchie_kind,
            parameter_contracted_tys,
            return_ty,
        } => false,
        FlyTermData::SymbolicVariable {
            symbolic_variable: term,
            ty,
        } => false,
        FlyTermData::AbstractVariable { .. } => unreachable!(),
        FlyTermData::TypeVariant { path } => unreachable!(),
        FlyTermData::MajorTypeVar(_) => todo!(),
    }
}

mod ethereal;
mod hollow;
mod solid;

use super::*;
use assoc_item::{
    trai_for_ty_item::TraitForTypeItemFlySignature,
    trai_item::TraitItemFlySignature,
    ty_item::{assoc_ritchie::TypeAssocRitchieFlySignature, TypeItemFlySignature},
};
use husky_coword::Ident;
use husky_entity_path::path::major_item::trai::TraitPath;
use husky_entity_tree::node::HasAssocItemPaths;
use husky_eth_signature::signature::assoc_item::ty_item::{
    HasTypeItemTemplates, TypeItemEthTemplates,
};
use husky_eth_term::term::application::TermFunctionReduced;
use path::assoc_item::AssocItemPath;
use vec_like::VecMapGetEntry;

#[derive(Debug, PartialEq, Eq)]
pub enum OntologyDispatch {
    TypeItem {
        signature: TypeItemFlySignature,
    },
    TraitItem {
        signature: TraitItemFlySignature,
    },
    TraitForTypeItem {
        signature: TraitForTypeItemFlySignature,
    },
}
impl OntologyDispatch {
    pub fn requires_lazy_to_use(&self) -> bool {
        match self {
            OntologyDispatch::TypeItem { signature } => todo!(),
            OntologyDispatch::TraitItem { signature, .. } => todo!(),
            OntologyDispatch::TraitForTypeItem { signature } => todo!(),
        }
    }
}

// AssocRitchie(TypeAssocRitchieFlySignature),
// AssocStaticVar(AssocStaticVarFlySignature),
impl OntologyDispatch {
    pub fn item_ty_result(&self, engine: &mut impl FlyTermEngineMut) -> FlyTermResult<FlyTerm> {
        let db = engine.db();
        match self {
            OntologyDispatch::TypeItem { signature } => Ok(signature.item_ty()),
            OntologyDispatch::TraitItem { signature, .. } => Ok(signature.item_ty()),
            OntologyDispatch::TraitForTypeItem { signature } => todo!(),
        }
    }

    pub fn item_term_result(&self, engine: &mut impl FlyTermEngineMut) -> FlyTermResult<FlyTerm> {
        let db = engine.db();
        match *self {
            OntologyDispatch::TypeItem { ref signature } => todo!(),
            OntologyDispatch::TraitItem { ref signature, .. } => {
                let self_ty = signature.self_ty();
                let trai = signature.trai();
                let trai_item_path = signature.path();
                let ident = trai_item_path.ident(db);
                Ok(FlyTerm::new_ty_as_trai_item(
                    engine,
                    self_ty,
                    trai,
                    ident,
                    trai_item_path,
                ))
            }
            OntologyDispatch::TraitForTypeItem { ref signature } => todo!(),
            // StaticDispatch::AssocRitchie(_) => todo!(),
            // StaticDispatch::AssocGn => todo!(),
            // StaticDispatch::TypeAsTrait {
            //     trai,
            //     trai_item_path,
            //     ..
            // } => {
            //     let ty = self.calc_expr_term(parent_expr_idx).expect(
            //         "should be guaranteed to be okay by the fact that static dispatch is calculated",
            //     );
            //     Ok(FlyTerm::new_ty_as_trai_item(
            //         self,
            //         ty,
            //         trai,
            //         ident,
            //         trai_item_path,
            //     ))
            // }
        }
    }

    pub fn path(&self) -> AssocItemPath {
        match self {
            OntologyDispatch::TypeItem { signature } => signature.path().into(),
            OntologyDispatch::TraitItem { signature } => signature.path().into(),
            OntologyDispatch::TraitForTypeItem { signature } => signature.path().into(),
        }
    }
    pub fn instantiation(&self) -> &FlyInstantiation {
        match self {
            OntologyDispatch::TypeItem { signature } => signature.instantiation(),
            OntologyDispatch::TraitItem { signature } => signature.instantiation(),
            OntologyDispatch::TraitForTypeItem { signature } => signature.instantiation(),
        }
    }
}

impl FlyTerm {
    pub fn ontology_dispatch(
        self,
        engine: &mut impl FlyTermEngineMut,
        syn_expr_idx: SynExprIdx,
        ident: Ident,
        all_available_traits: &[()],
    ) -> FlyTermMaybeResult<OntologyDispatch> {
        // todo: optimize for ethereal etc.
        let db = engine.db();
        match self.base_term_data(engine) {
            FlyTermData::Literal(_) => todo!(),
            FlyTermData::TypeOntology {
                ty_path,
                ty_arguments,
                ..
            } => match ty_path.ty_item_eth_templates(db, ident) {
                // we prioritize type item than trait item
                JustOk(templates) => match templates {
                    TypeItemEthTemplates::AssocRitchie(templates) => {
                        let dst_ty_arguments: SmallVec<[_; 2]> = ty_arguments.to_smallvec();
                        let signatures: Vec<_> = templates
                            .iter()
                            .copied()
                            .filter_map(|template| {
                                TypeAssocRitchieFlySignature::from_ty_assoc_ritchie(
                                    engine,
                                    syn_expr_idx,
                                    template,
                                    &dst_ty_arguments,
                                    /* ad hoc */ &[],
                                )
                                .ok()
                            })
                            .collect();
                        match signatures.len() {
                            0 => Nothing,
                            1 => {
                                let mut signatures = signatures;
                                let signature = signatures.pop().unwrap();
                                let FlyBaseTypeData::TypeOntology {
                                    ty_arguments: src_ty_arguments,
                                    ..
                                } = signature.self_ty().base_ty_data(engine)
                                else {
                                    unreachable!()
                                };
                                let src_ty_arguments: SmallVec<[_; 2]> =
                                    src_ty_arguments.to_smallvec();
                                debug_assert_eq!(src_ty_arguments.len(), dst_ty_arguments.len());
                                for (&src_ty_argument, &dst_ty_argument) in
                                    std::iter::zip(&src_ty_arguments, &dst_ty_arguments)
                                {
                                    engine.add_expectation(
                                        ExpectationSource::new_expr(syn_expr_idx),
                                        src_ty_argument,
                                        ExpectSubtypeOrEqual::new(dst_ty_argument),
                                    );
                                }
                                return JustOk(OntologyDispatch::TypeItem {
                                    signature: signature.into(),
                                });
                            }
                            _ => todo!(),
                        }
                    }
                    TypeItemEthTemplates::MethodFn(_) => todo!(),
                    TypeItemEthTemplates::MethodFunction(_) => todo!(),
                    TypeItemEthTemplates::MemoizedField(_) => todo!(),
                },
                JustErr(_) => todo!(),
                Nothing => todo!(),
            },
            FlyTermData::Trait { .. } => todo!(),
            FlyTermData::Curry {
                toolchain,
                curry_kind,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => todo!(),
            FlyTermData::Hole(_, _) => todo!(),
            FlyTermData::Sort(_) => todo!(),
            FlyTermData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => todo!(),
            FlyTermData::SymbolicVariable {
                symbolic_variable, ..
            } => {
                let Ok(symbolic_variable_obvious_trais) =
                    engine.symbolic_variable_obvious_trais(symbolic_variable)
                else {
                    todo!()
                };
                match symbolic_variable_obvious_trais.len() {
                    0 => todo!(),
                    1 => {
                        let trai = symbolic_variable_obvious_trais[0];
                        JustOk(OntologyDispatch::TraitItem {
                            signature: TraitItemFlySignature::from_as_trai(
                                self,
                                trai,
                                ident,
                                syn_expr_idx,
                                engine,
                            )?,
                        })
                    }
                    _ => todo!(),
                }
            }
            FlyTermData::AbstractVariable { ty, index } => todo!(),
            FlyTermData::TypeVariant { path } => todo!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
        }
    }
    pub fn ontology_dispatch_as_trai(
        self,
        trai: Self,
        engine: &mut impl FlyTermEngineMut,
        syn_expr_idx: SynExprIdx,
        ident: Ident,
    ) -> FlyTermMaybeResult<OntologyDispatch> {
        let db = engine.db();
        match self.base_term_data(engine) {
            FlyTermData::Literal(_) => todo!(),
            FlyTermData::TypeOntology {
                ty_path,
                refined_ty_path,
                ty_arguments,
                ty_ethereal_term,
            } => todo!(),
            FlyTermData::Trait { .. } => todo!(),
            FlyTermData::Curry {
                toolchain,
                curry_kind,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => todo!(),
            FlyTermData::Hole(_, _) => todo!(),
            FlyTermData::Sort(_) => todo!(),
            FlyTermData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => todo!(),
            FlyTermData::SymbolicVariable {
                symbolic_variable,
                ty,
            } => todo!(),
            FlyTermData::AbstractVariable { ty, index } => todo!(),
            FlyTermData::TypeVariant { path } => todo!(),
            FlyTermData::MajorTypeVar(_) => {
                let trai_path: TraitPath = match trai.base_term_data(engine) {
                    FlyTermData::Trait { trai_path, .. } => trai_path,
                    _ => todo!(),
                };
                let Some(&(_, trai_item_path)) = trai_path.assoc_item_paths(db).get_entry(ident)
                else {
                    todo!()
                };
                JustOk(OntologyDispatch::TraitItem {
                    signature: TraitItemFlySignature::from_as_trai(
                        self,
                        trai,
                        ident,
                        syn_expr_idx,
                        engine,
                    )?,
                })
            }
        }
    }
}

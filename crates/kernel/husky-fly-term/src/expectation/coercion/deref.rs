use super::*;
use crate::quary::FlyQuary;
use husky_entity_path::path::major_item::ty::{PreludeIndirectionTypePath, PreludeTypePath};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum DedirectionFlyCoercion {
    Deleash,
    Deref { lifetime: FlyLifetime },
}

impl DedirectionFlyCoercion {
    pub fn place_after_coercion(self) -> FlyQuary {
        match self {
            DedirectionFlyCoercion::Deleash => FlyQuary::Leashed { place: None },
            DedirectionFlyCoercion::Deref { lifetime } => FlyQuary::Ref {
                guard: Right(lifetime),
            },
        }
    }
}

impl ExpectCoercion {
    pub(super) fn resolve_deref(
        &self,
        db: &::salsa::Db,
        terms: &mut FlyTerms,
        state: &mut ExpectationState,
    ) -> AltOption<FlyTermEffect> {
        let expectee_base_ty_data = state.expectee().base_ty_data_inner(db, terms);
        // todo: check contract
        match expectee_base_ty_data {
            FlyBaseTypeData::TypeOntology {
                refined_ty_path: Left(PreludeTypePath::Indirection(prelude_indirection_ty_path)),
                ty_arguments: expectee_ty_arguments,
                ..
            } => {
                match prelude_indirection_ty_path {
                    PreludeIndirectionTypePath::Ref => {
                        debug_assert_eq!(expectee_ty_arguments.len(), 2);
                        self.try_finalize_coercion(
                            self.ty_expected,
                            expectee_ty_arguments[1],
                            DedirectionFlyCoercion::Deref {
                                lifetime: FlyLifetime::from_term(
                                    expectee_ty_arguments[0],
                                    db,
                                    terms,
                                ),
                            },
                            db,
                            terms,
                            state,
                        )
                    }
                    PreludeIndirectionTypePath::RefMut => todo!(),
                    PreludeIndirectionTypePath::Leash => {
                        debug_assert_eq!(expectee_ty_arguments.len(), 1);
                        // todo: check expected_ty_argument_place
                        self.try_finalize_coercion(
                            self.ty_expected,
                            expectee_ty_arguments[0],
                            DedirectionFlyCoercion::Deleash,
                            db,
                            terms,
                            state,
                        )
                    }
                    PreludeIndirectionTypePath::At => todo!(),
                }
            }
            _ => AltNone,
        }
    }
}

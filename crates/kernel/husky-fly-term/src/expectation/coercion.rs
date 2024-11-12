//! coercion rules are
//!
pub mod deref;
pub mod holed;
pub mod never;
pub mod redirection;
pub mod trival;
pub mod wrap_in_some;

use self::trival::TrivialFlyCoercion;
use self::{deref::DedirectionFlyCoercion, quary::FlyQuary};
use super::*;
use redirection::RedirectionFlyCoercion;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FlyCoercion {
    Trivial(TrivialFlyCoercion),
    Never,
    WrapInSome,
    Redirection(RedirectionFlyCoercion),
    Dedirection(DedirectionFlyCoercion),
}

impl FlyCoercion {
    pub fn quary_after_coercion(self) -> FlyQuary {
        match self {
            FlyCoercion::Trivial(slf) => slf.quary_after_coercion(),
            FlyCoercion::Dedirection(slf) => slf.place_after_coercion(),
            FlyCoercion::Never | FlyCoercion::WrapInSome | FlyCoercion::Redirection(_) => {
                FlyQuary::Transient
            }
        }
    }
}

/// expect a type that is implicitly convertible to type under contract
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[salsa::derive_debug_with_db]
pub struct ExpectCoercion {
    contract: Contract,
    ty_expected: FlyTerm,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ExpectCoercionOutcome {
    coercion: FlyCoercion,
}

impl ExpectCoercionOutcome {
    pub fn coercion(&self) -> FlyCoercion {
        self.coercion
    }
}

impl ExpectCoercion {
    #[inline(always)]
    pub fn new(contract: Contract, ty_expected: FlyTerm) -> Self {
        Self {
            contract,
            ty_expected,
        }
    }

    #[inline(always)]
    pub fn new_const(ty: FlyTerm) -> Self {
        Self {
            contract: Contract::Compterm,
            ty_expected: ty,
        }
    }

    /// this will reduce place type to type
    #[inline(always)]
    pub fn new_pure(engine: &impl FlyTermEngine, ty: FlyTerm) -> Self {
        let ty = match ty.base_term_data(engine) {
            // FlyTermData::TypeOntologyAtPlace {
            //     ty_path,
            //     ty_arguments,
            //     ..
            // } => match ty_arguments.len() {
            //     0 => TermEntityPath::TypeOntology(ty_path).into(),
            //     // ad hoc
            //     _ => ty,
            // },
            _ => ty,
        };
        Self {
            contract: Contract::Pure,
            ty_expected: ty,
        }
    }

    #[inline(always)]
    pub fn new_pure_unit(engine: &impl FlyTermEngine) -> Self {
        Self {
            contract: Contract::Pure,
            ty_expected: engine.term_menu().unit_ty_ontology().into(),
        }
    }

    #[inline(always)]
    pub fn new_pure_bool(engine: &impl FlyTermEngine) -> Self {
        Self {
            contract: Contract::Pure,
            ty_expected: engine.term_menu().bool_ty_ontology().into(),
        }
    }

    #[inline(always)]
    pub fn new_move(ty: FlyTerm) -> Self {
        Self {
            contract: Contract::Move,
            ty_expected: ty,
        }
    }

    fn ty_expected(self) -> FlyTerm {
        self.ty_expected
    }
}

impl ExpectFlyTerm for ExpectCoercion {
    type Outcome = ExpectCoercionOutcome;

    fn retrieve_outcome(outcome: &ExpectationOutcome) -> &Self::Outcome {
        match outcome {
            ExpectationOutcome::Coercion(outcome) => outcome,
            _ => unreachable!(),
        }
    }

    #[inline(always)]
    fn final_destination_inner(&self, db: &::salsa::Db, terms: &FlyTerms) -> FinalDestination {
        self.ty_expected().final_destination_inner(db, terms)
    }

    fn destination(&self) -> FlyTermDestination {
        FlyTermDestination::Specific(self.ty_expected())
    }

    fn resolve(
        &self,
        db: &::salsa::Db,
        terms: &mut FlyTerms,
        state: &mut ExpectationState,
    ) -> AltOption<FlyTermEffect> {
        self.resolve_trivial(db, terms, state)?;
        self.resolve_holed(db, terms, state)?;
        self.resolve_never(db, terms, state)?;
        self.resolve_wrap_in_some(db, terms, state)?;
        self.resolve_deref(db, terms, state)?;
        self.resolve_redirection(db, terms, state)?;
        match state.resolve_progress() {
            ExpectationProgress::Intact => state.set_err(
                OriginalFlyTermExpectationError::ExpectedCoercion {
                    expectee: state.expectee(),
                    contract: self.contract,
                    expected: self.ty_expected,
                },
                smallvec![],
            ),
            ExpectationProgress::Holed => AltNone,
            ExpectationProgress::Resolved(_) => unreachable!(),
        }
    }
}

impl ExpectCoercion {
    fn try_finalize_coercion(
        &self,
        src: FlyTerm,
        dst: FlyTerm,
        coercion: impl Into<FlyCoercion>,
        db: &::salsa::Db,
        terms: &FlyTerms,
        state: &mut ExpectationState,
    ) -> AltOption<FlyTermEffect> {
        let coercion = coercion.into();
        Self::try_finalize_coercion_aux(
            src,
            dst,
            coercion
                .quary_after_coercion()
                .bind(self.contract)
                .map(|()| coercion)
                .map_err(Into::into),
            db,
            terms,
            state,
        )
    }

    fn try_finalize_coercion_aux(
        src: FlyTerm,
        dst: FlyTerm,
        coercion_result: FlyTermExpectationResult<FlyCoercion>,
        db: &::salsa::Db,
        terms: &FlyTerms,
        state: &mut ExpectationState,
    ) -> AltOption<FlyTermEffect> {
        let src_base_ty_data = src.base_ty_data_inner(db, terms);
        let dst_base_ty_data = dst.base_ty_data_inner(db, terms);
        let outcome_result = coercion_result.map(|coercion| ExpectCoercionOutcome { coercion });
        if src_base_ty_data == dst_base_ty_data {
            return state.set_result(outcome_result, smallvec![]);
        }
        match src_base_ty_data {
            FlyBaseTypeData::TypeOntology {
                ty_path: src_ty_path,
                ty_arguments: src_ty_arguments,
                ..
            } => match dst_base_ty_data {
                FlyBaseTypeData::TypeOntology {
                    ty_path: dst_ty_path,
                    refined_ty_path,
                    ty_arguments: dst_ty_arguments,
                    ty_ethereal_term,
                } if dst_ty_path == src_ty_path => {
                    if dst_ty_arguments.len() != src_ty_arguments.len() {
                        // p!(state.expectee().debug(db), self.ty_expected().debug(db));
                        todo!()
                    }
                    let mut actions = smallvec![];
                    for (src_argument_ty, dst_argument_ty) in std::iter::zip(
                        src_ty_arguments.iter().copied(),
                        dst_ty_arguments.iter().copied(),
                    ) {
                        if src_argument_ty != dst_argument_ty {
                            // todo: check variance
                            actions.push(FlyTermResolveAction::AddExpectation {
                                src: state.child_src(),
                                expectee: src_argument_ty,
                                expectation: ExpectSubtypeOrEqual::new(dst_argument_ty).into(),
                            })
                        }
                    }
                    state.set_result(outcome_result, actions)
                }
                _ => AltNone,
            },
            FlyBaseTypeData::Curry { .. } => AltNone,
            FlyBaseTypeData::Hole(_, _) => AltNone,
            FlyBaseTypeData::Sort(_) => todo!(),
            FlyBaseTypeData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => {
                p!(src_base_ty_data.debug(db), dst_base_ty_data.debug(db));
                todo!()
            }
            FlyBaseTypeData::SymbolicVariable {
                symbolic_variable: term,
            } => AltNone,
            FlyBaseTypeData::AbstractVariable {
                abstract_variable: hvar,
            } => todo!(),
        }
    }
}

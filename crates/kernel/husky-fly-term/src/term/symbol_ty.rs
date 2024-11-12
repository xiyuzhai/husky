use super::*;
use husky_dec_signature::region::variable::DecSymbolicVariableSignature;
use husky_place::PlaceInfo;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct SymbolType(FlyTerm);

impl SymbolType {
    pub fn term(self) -> FlyTerm {
        self.0
    }
}

impl Into<FlyTerm> for SymbolType {
    fn into(self) -> FlyTerm {
        self.term()
    }
}

impl SymbolType {
    #[inline(always)]
    pub fn new_parameter_ty_from_signature(
        engine: &mut impl FlyTermEngineMut,
        current_variable_idx: CurrentVariableIdx,
        signature: DecSymbolicVariableSignature,
    ) -> FlyTermResult<Self> {
        let ty = EthTerm::ty_from_dec(engine.db(), signature.ty()?)?;
        Ok(Self::new_parameter_ty(
            engine,
            current_variable_idx,
            signature.modifier(),
            ty.into(),
        ))
    }

    pub fn new_parameter_ty(
        engine: &mut impl FlyTermEngineMut,
        current_variable_idx: CurrentVariableIdx,
        modifier: VariableModifier,
        ty: FlyTerm,
    ) -> Self {
        let place_data = || {
            let Some(ident) = engine.syn_expr_region_data()[current_variable_idx].ident() else {
                let db = engine.db();
                p!(engine.syn_expr_region_data()[current_variable_idx]
                    .name()
                    .debug(db));
                unreachable!();
            };
            PlaceInfo::Parameter {
                current_variable_idx,
                ident,
            }
        };
        let quary = match modifier {
            VariableModifier::Pure => FlyQuary::StackPure {
                place: engine.issue_new_place_idx(place_data()).into(),
            },
            VariableModifier::Owned => FlyQuary::ImmutableOnStack {
                place: engine.issue_new_place_idx(place_data()).into(),
            },
            VariableModifier::Mut => todo!(),
            VariableModifier::Ref => todo!(),
            VariableModifier::RefMut => FlyQuary::RefMut {
                place: engine.issue_new_place_idx(place_data()).into(),
                lifetime: None,
            },
            VariableModifier::Compterm => FlyQuary::Compterm,
            VariableModifier::Ambersand(_) => todo!(),
            VariableModifier::AmbersandMut(_) => todo!(),
            VariableModifier::Le => todo!(),
            VariableModifier::Tilde => todo!(),
            VariableModifier::At => todo!(),
        };
        Self(ty.with_quary(quary))
    }

    pub fn new_variable_ty(
        engine: &mut impl FlyTermEngineMut,
        current_variable_idx: CurrentVariableIdx,
        modifier: VariableModifier,
        ty: FlyTerm,
    ) -> FlyTermResult<Self> {
        let ident = engine.syn_expr_region_data()[current_variable_idx]
            .ident()
            .unwrap();
        let place_data = PlaceInfo::Variable {
            current_variable_idx,
            ident,
        };
        let quary = match modifier {
            VariableModifier::Pure => match ty.quary {
                Some(FlyQuary::Transient) | None => FlyQuary::ImmutableOnStack {
                    place: engine.issue_new_place_idx(place_data).into(),
                },
                Some(quary) => match ty.always_copyable(engine.db(), engine.fly_terms())? {
                    Some(true) => FlyQuary::ImmutableOnStack {
                        place: engine.issue_new_place_idx(place_data).into(),
                    },
                    Some(false) => match quary {
                        FlyQuary::Compterm => todo!(),
                        FlyQuary::StackPure { place }
                        | FlyQuary::ImmutableOnStack { place }
                        | FlyQuary::MutableOnStack { place } => {
                            FlyQuary::Ref { guard: Left(place) }
                        }
                        FlyQuary::Transient => unreachable!(),
                        FlyQuary::Ref { guard } => todo!(),
                        FlyQuary::RefMut { .. } => todo!(),
                        FlyQuary::Leashed { .. } => FlyQuary::Leashed {
                            place: Some(engine.issue_new_place_idx(place_data)),
                        },
                        FlyQuary::Todo => todo!(),
                        FlyQuary::EtherealSymbol(_) => todo!(),
                    },
                    None => todo!(),
                },
            },
            VariableModifier::Owned => todo!(),
            VariableModifier::Mut => match ty.quary {
                Some(FlyQuary::Transient) | None => FlyQuary::MutableOnStack {
                    place: engine.issue_new_place_idx(place_data).into(),
                },
                Some(place) => match ty.always_copyable(engine.db(), engine.fly_terms())? {
                    Some(true) => FlyQuary::MutableOnStack {
                        place: engine.issue_new_place_idx(place_data).into(),
                    },
                    Some(false) => {
                        p!(ty.show2(engine.db(), engine.fly_terms()));
                        todo!()
                    }
                    None => todo!(),
                },
            },
            VariableModifier::Ref => todo!(),
            VariableModifier::RefMut => todo!(),
            VariableModifier::Compterm => todo!(),
            VariableModifier::Ambersand(_) => todo!(),
            VariableModifier::AmbersandMut(_) => todo!(),
            VariableModifier::Le => todo!(),
            VariableModifier::Tilde => todo!(),
            VariableModifier::At => todo!(),
        };
        Ok(Self(ty.with_quary(quary)))
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum FlyLifetime {
    StaticLifetime,
}

impl FlyLifetime {
    pub(crate) fn from_term(term: FlyTerm, db: &::salsa::Db, terms: &mut FlyTerms) -> Self {
        match term.base_term_data2(db, terms) {
            FlyTermData::Literal(lit) => match lit {
                Literal::StaticLifetime => FlyLifetime::StaticLifetime,
                _ => todo!(),
            },
            FlyTermData::TypeOntology { .. } => todo!(),
            FlyTermData::Trait { .. } => todo!(),
            FlyTermData::Curry { .. } => todo!(),
            FlyTermData::Hole(_, _) => todo!(),
            FlyTermData::Sort(_) => todo!(),
            FlyTermData::Ritchie { .. } => todo!(),
            FlyTermData::SymbolicVariable { .. } => todo!(),
            FlyTermData::AbstractVariable { .. } => todo!(),
            FlyTermData::TypeVariant { .. } => todo!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct FlyLifetimeIdx {}

// #[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
// pub struct PlaceTypeIdx(FlyTermIdx);

// impl Into<FlyTerm> for PlaceTypeIdx {
//     fn into(self) -> FlyTerm {
//         self.0.into()
//     }
// }

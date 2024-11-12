use super::*;

impl FlyTerm {
    pub(crate) fn curry_destination(self, db: &::salsa::Db, terms: &FlyTerms) -> FlyTerm {
        match self.base_term_data2(db, terms) {
            FlyTermData::TypeOntology { .. }
            | FlyTermData::Hole(_, _)
            | FlyTermData::Sort(_)
            | FlyTermData::Ritchie { .. }
            | FlyTermData::SymbolicVariable { .. }
            | FlyTermData::AbstractVariable { .. } => self,
            FlyTermData::Curry { return_ty, .. } => return_ty.curry_destination(db, terms),
            FlyTermData::Literal(_) | FlyTermData::TypeVariant { .. } => unreachable!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
            FlyTermData::Trait { .. } => todo!(),
        }
    }

    pub fn final_destination(self, engine: &impl FlyTermEngine) -> FinalDestination {
        self.final_destination_inner(engine.db(), engine.fly_terms())
    }

    /// this term as ty, what's its final destination?
    ///
    pub(crate) fn final_destination_inner(
        self,
        db: &::salsa::Db,
        fly_terms: &FlyTerms,
    ) -> FinalDestination {
        match self.base_term_data2(db, fly_terms) {
            FlyTermData::TypeOntology { .. } => FinalDestination::TypeOntology,
            FlyTermData::Trait { .. } => todo!(),
            FlyTermData::Curry { return_ty, .. } => {
                return_ty.final_destination_inner(db, fly_terms)
            }
            FlyTermData::Hole(kind, idx) => match kind {
                HoleKind::UnspecifiedIntegerType
                | HoleKind::UnspecifiedFloatType
                | HoleKind::ImplicitType => FinalDestination::TypeOntology,
                HoleKind::AnyOriginal => FinalDestination::AnyOriginal,
                HoleKind::AnyDerived => FinalDestination::AnyDerived,
            },
            FlyTermData::Sort(_) => FinalDestination::Sort,
            FlyTermData::Ritchie { ritchie_kind, .. } => FinalDestination::Ritchie(ritchie_kind),
            FlyTermData::SymbolicVariable { .. } | FlyTermData::AbstractVariable { .. } => {
                FinalDestination::AnyOriginal
            }
            FlyTermData::Literal(_) | FlyTermData::TypeVariant { .. } => unreachable!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
        }
    }

    /// the count is always positive but returns i8 for convenience in computing difference
    /// -> i8 {v: v> 0}
    ///
    /// todo: include ritchie??
    pub fn curry_parameter_count(self, engine: &impl FlyTermEngine) -> i8 {
        self.curry_parameter_count_inner(engine.db(), engine.fly_terms())
    }

    pub fn curry_parameter_count_inner(self, db: &::salsa::Db, fly_terms: &FlyTerms) -> i8 {
        match self.base_term_data2(db, fly_terms) {
            FlyTermData::Literal(_) => todo!(),
            FlyTermData::TypeOntology {
                ty_path: path,
                refined_ty_path: refined_path,
                ty_arguments: arguments,
                ty_ethereal_term,
            } => 0,
            FlyTermData::Curry {
                toolchain,
                curry_kind,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => match ty_ethereal_term {
                Some(ty_ethereal_term) => ty_ethereal_term.curry_parameter_count(db),
                None => todo!(),
            },
            FlyTermData::Hole(hole_kind, _) => 0,
            FlyTermData::Sort(_) => 0,
            FlyTermData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => 0,
            FlyTermData::SymbolicVariable { .. } | FlyTermData::AbstractVariable { .. } => 0,
            FlyTermData::TypeVariant { path } => todo!(),
            FlyTermData::MajorTypeVar(_) => todo!(),
            FlyTermData::Trait { .. } => todo!(),
        }
    }
}

use super::*;

pub(super) fn ethereal_term_data<'a>(
    db: &'a dyn FluffyTermDb,
    term: EtherealTerm,
) -> FluffyTermData<'a> {
    match term {
        EtherealTerm::Literal(_) => todo!(),
        EtherealTerm::Symbol(_) => todo!(),
        EtherealTerm::Variable(_) => todo!(),
        EtherealTerm::EntityPath(path) => match path {
            TermEntityPath::Form(_) => todo!(),
            TermEntityPath::Trait(_) => todo!(),
            TermEntityPath::TypeOntology(ty_path) => FluffyTermData::TypeOntology {
                path: ty_path,
                refined_path: ty_path.refine(db),
                arguments: &[],
                ty_ethereal_term: Some(path.into()),
            },
            TermEntityPath::TypeConstructor(_) => todo!(),
        },
        EtherealTerm::Category(term) => FluffyTermData::Category(term),
        EtherealTerm::Universe(_) => todo!(),
        EtherealTerm::Curry(term) => FluffyTermData::Curry {
            curry_kind: term.curry_kind(db),
            variance: term.variance(db),
            parameter_variable: term.parameter_variable(db).map(Into::into),
            parameter_ty: term.parameter_ty(db).into(),
            return_ty: term.return_ty(db).into(),
        },
        EtherealTerm::Ritchie(term) => FluffyTermData::Ritchie {
            ritchie_kind: term.ritchie_kind(db),
            parameter_contracted_tys: term_ritchie_fluffy_data(db, term),
            return_ty: term.return_ty(db).into(),
        },
        EtherealTerm::Abstraction(_) => todo!(),
        EtherealTerm::Application(term) => {
            term_application_fluffy_data(db, term).to_fluffy(term.into())
        }
        EtherealTerm::Subentity(_) => todo!(),
        EtherealTerm::AsTraitSubentity(_) => todo!(),
        EtherealTerm::TraitConstraint(_) => todo!(),
    }
}
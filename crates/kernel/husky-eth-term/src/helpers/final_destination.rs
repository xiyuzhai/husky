use husky_entity_kind::MajorFormKind;

use super::*;

impl EthTerm {
    pub fn final_destination(self, db: &::salsa::Db) -> FinalDestination {
        match self {
            EthTerm::Literal(_) => FinalDestination::AnyDerived,
            EthTerm::SymbolicVariable(_) | EthTerm::AbstractVariable(_) => {
                FinalDestination::AnyOriginal
            }
            EthTerm::ItemPath(path) => match path {
                ItemPathTerm::MajorForm(path) => match path.kind(db) {
                    MajorFormKind::TypeAlias => todo!(),
                    MajorFormKind::TypeVar => todo!(),
                    MajorFormKind::Ritchie(_)
                    | MajorFormKind::Val
                    | MajorFormKind::Conceptual
                    | MajorFormKind::StaticMut
                    | MajorFormKind::StaticVar
                    | MajorFormKind::Compterm => FinalDestination::AnyDerived,
                },
                ItemPathTerm::TypeOntology(_) => FinalDestination::TypeOntology,
                ItemPathTerm::Trait(_)
                | ItemPathTerm::TypeInstance(_)
                | ItemPathTerm::TypeVariant(_) => FinalDestination::AnyDerived,
            },
            EthTerm::Sort(_) => FinalDestination::Sort,
            EthTerm::Universe(_) => unreachable!("expect ty term"),
            EthTerm::Curry(slf) => curry_ethereal_term_final_destination(db, slf),
            EthTerm::Ritchie(slf) => FinalDestination::Ritchie(slf.ritchie_kind(db)),
            EthTerm::Abstraction(_) => unreachable!("expect ty term"),
            EthTerm::Application(slf) => application_ethereal_term_final_destination(db, slf),
            EthTerm::TypeAsTraitItem(_) => FinalDestination::AnyOriginal,
            EthTerm::TraitConstraint(_) => FinalDestination::Sort,
        }
    }
}

#[salsa::tracked]
fn application_ethereal_term_final_destination(
    db: &::salsa::Db,
    application: EthApplication,
) -> FinalDestination {
    application.function(db).final_destination(db)
}

#[salsa::tracked]
fn curry_ethereal_term_final_destination(db: &::salsa::Db, curry: EthCurry) -> FinalDestination {
    curry.return_ty(db).final_destination(db)
}

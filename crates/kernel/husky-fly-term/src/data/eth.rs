use husky_eth_term::term::{
    application::{EthApplication, TermFunctionReduced},
    ritchie::EthRitchie,
};
use path::major_item::trai::{OtherTraitPath, PreludeTraitPath};

use super::*;

pub(super) fn ethereal_term_data<'a>(db: &'a ::salsa::Db, term: EthTerm) -> FlyTermData<'a> {
    match term {
        EthTerm::Literal(lit) => FlyTermData::Literal(lit),
        EthTerm::SymbolicVariable(term) => FlyTermData::SymbolicVariable {
            symbolic_variable: term,
            ty: term.ty(db).into(),
        },
        EthTerm::AbstractVariable(term) => FlyTermData::AbstractVariable {
            ty: term.ty(db).into(),
            index: term.index(db),
        },
        EthTerm::ItemPath(path) => match path {
            ItemPathTerm::MajorForm(path) => FlyTermData::MajorTypeVar(path),
            ItemPathTerm::Trait(trai_path) => FlyTermData::Trait {
                trai_path,
                trai_arguments: &[],
                trai_ethereal_term: Some(term),
                refined_trai_path: trai_path.refine(db),
            },
            ItemPathTerm::TypeOntology(ty_path) => FlyTermData::TypeOntology {
                ty_path,
                refined_ty_path: ty_path.refine(db),
                ty_arguments: &[],
                ty_ethereal_term: Some(path.into()),
            },
            ItemPathTerm::TypeInstance(_) => todo!(),
            ItemPathTerm::TypeVariant(path) => FlyTermData::TypeVariant { path },
        },
        EthTerm::Sort(term) => FlyTermData::Sort(term),
        EthTerm::Universe(_) => todo!(),
        EthTerm::Curry(term) => FlyTermData::Curry {
            toolchain: term.toolchain(db),
            curry_kind: term.curry_kind(db),
            variance: term.variance(db),
            parameter_hvar: term.parameter_hvar(db).map(Into::into),
            parameter_ty: term.parameter_ty(db).into(),
            return_ty: term.return_ty(db).into(),
            ty_ethereal_term: Some(term),
        },
        EthTerm::Ritchie(term) => term_ritchie_fly_data(db, term).as_ref(),
        EthTerm::Abstraction(_) => todo!(),
        EthTerm::Application(term) => term_application_fly_data(db, term).as_ref(),
        EthTerm::TypeAsTraitItem(_) => todo!(),
        EthTerm::TraitConstraint(_) => todo!(),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct TermRitchieFlyData {
    ritchie_kind: RitchieKind,
    parameter_contracted_tys: SmallVec<[FlyRitchieParameter; 2]>,
    variadics: (),
    keyed_parameter_contracted_tys: (),
    return_ty: EthTerm,
}

impl TermRitchieFlyData {
    fn as_ref<'a>(&'a self) -> FlyTermData<'a> {
        FlyTermData::Ritchie {
            ritchie_kind: self.ritchie_kind,
            parameter_contracted_tys: &self.parameter_contracted_tys,
            return_ty: FlyTerm::from_eth_transient(self.return_ty),
        }
    }

    fn as_ref2<'a>(&'a self) -> FlyBaseTypeData<'a> {
        FlyBaseTypeData::Ritchie {
            ritchie_kind: self.ritchie_kind,
            parameter_contracted_tys: &self.parameter_contracted_tys,
            return_ty: FlyTerm::from_eth_transient(self.return_ty),
        }
    }
}

#[salsa::tracked(return_ref)]
pub(crate) fn term_ritchie_fly_data(db: &::salsa::Db, term: EthRitchie) -> TermRitchieFlyData {
    TermRitchieFlyData {
        ritchie_kind: term.ritchie_kind(db),
        parameter_contracted_tys: term
            .parameter_contracted_tys(db)
            .iter()
            .copied()
            .map(Into::into)
            .collect(),
        variadics: (),
        keyed_parameter_contracted_tys: (),
        return_ty: term.return_ty(db),
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum TermApplicationFlyData {
    TypeOntology {
        path: TypePath,
        refined_path: Either<PreludeTypePath, OtherTypePath>,
        arguments: SmallVec<[FlyTerm; 2]>,
        ty_ethereal_term: EthTerm,
    },
    Trait {
        trai_path: TraitPath,
        refined_trai_path: Either<PreludeTraitPath, OtherTraitPath>,
        arguments: SmallVec<[FlyTerm; 2]>,
        trai_ethereal_term: EthTerm,
    },
}

/// can't directly return FlyTermData<'_> because of lifetime
#[salsa::tracked(return_ref)]
pub(crate) fn term_application_fly_data(
    db: &::salsa::Db,
    term: EthApplication,
) -> TermApplicationFlyData {
    let expansion = term.application_expansion(db);
    match expansion.function() {
        TermFunctionReduced::TypeOntology(path) => TermApplicationFlyData::TypeOntology {
            path,
            refined_path: path.refine(db),
            arguments: expansion
                .arguments(db)
                .iter()
                .copied()
                .map(Into::into)
                .collect(),
            ty_ethereal_term: term.into(),
        },
        TermFunctionReduced::Trait(trai_path) => TermApplicationFlyData::Trait {
            trai_path,
            refined_trai_path: trai_path.refine(db),
            arguments: expansion
                .arguments(db)
                .iter()
                .copied()
                .map(Into::into)
                .collect(),
            trai_ethereal_term: term.into(),
        },
        TermFunctionReduced::TypeVar(_) => todo!(),
        TermFunctionReduced::Other(_) => todo!(),
    }
}

impl TermApplicationFlyData {
    fn as_ref<'a>(&'a self) -> FlyTermData<'a> {
        match *self {
            TermApplicationFlyData::TypeOntology {
                path,
                refined_path,
                ref arguments,
                ty_ethereal_term,
            } => FlyTermData::TypeOntology {
                ty_path: path,
                refined_ty_path: refined_path,
                ty_arguments: arguments,
                ty_ethereal_term: Some(ty_ethereal_term),
            },
            TermApplicationFlyData::Trait {
                trai_path: path,
                refined_trai_path: refined_path,
                ref arguments,
                trai_ethereal_term,
            } => FlyTermData::Trait {
                trai_path: path,
                refined_trai_path: refined_path,
                trai_arguments: arguments,
                trai_ethereal_term: Some(trai_ethereal_term),
            },
        }
    }

    fn as_ref2<'a>(&'a self) -> FlyBaseTypeData<'a> {
        match *self {
            TermApplicationFlyData::TypeOntology {
                path,
                refined_path,
                ref arguments,
                ty_ethereal_term,
            } => FlyBaseTypeData::TypeOntology {
                ty_path: path,
                refined_ty_path: refined_path,
                ty_arguments: arguments,
                ty_ethereal_term: Some(ty_ethereal_term),
            },
            TermApplicationFlyData::Trait { .. } => todo!(),
        }
    }
}

pub(super) fn ethereal_term_fly_base_ty_data<'a>(
    db: &'a ::salsa::Db,
    term: EthTerm,
) -> FlyBaseTypeData<'a> {
    match term {
        EthTerm::Literal(_) => todo!(),
        EthTerm::SymbolicVariable(symbol) => FlyBaseTypeData::SymbolicVariable {
            symbolic_variable: symbol,
        },
        EthTerm::AbstractVariable(hvar) => FlyBaseTypeData::AbstractVariable {
            abstract_variable: hvar,
        },
        EthTerm::ItemPath(path) => match path {
            ItemPathTerm::MajorForm(_) => todo!(),
            ItemPathTerm::Trait(_) => todo!(),
            ItemPathTerm::TypeOntology(ty_path) => FlyBaseTypeData::TypeOntology {
                ty_path,
                refined_ty_path: ty_path.refine(db),
                ty_arguments: &[],
                ty_ethereal_term: Some(path.into()),
            },
            ItemPathTerm::TypeInstance(_) => todo!(),
            ItemPathTerm::TypeVariant(path) => unreachable!(),
        },
        EthTerm::Sort(term) => FlyBaseTypeData::Sort(term),
        EthTerm::Universe(_) => todo!(),
        EthTerm::Curry(term) => FlyBaseTypeData::Curry {
            curry_kind: term.curry_kind(db),
            variance: term.variance(db),
            parameter_hvar: term.parameter_hvar(db).map(Into::into),
            parameter_ty: term.parameter_ty(db).into(),
            return_ty: term.return_ty(db).into(),
            ty_ethereal_term: Some(term),
        },
        EthTerm::Ritchie(term) => term_ritchie_fly_data(db, term).as_ref2(),
        EthTerm::Abstraction(_) => todo!(),
        EthTerm::Application(term) => term_application_fly_data(db, term).as_ref2(),
        EthTerm::TypeAsTraitItem(_) => todo!(),
        EthTerm::TraitConstraint(_) => todo!(),
    }
}

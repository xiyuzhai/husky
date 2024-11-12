use crate::{
    path_leading::HirTypePathLeading, quary::HirContractedQuary, ritchie::HirRitchieType, *,
};
use husky_eth_signature::helpers::trai_for_ty::is_ty_term_always_copyable;
use husky_eth_term::term::EthTerm;
use husky_fly_term::{FlyTerm, FlyTermBase, FlyTerms};
use husky_term_prelude::ItemPathTerm;

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum HirTemplateArgument {
    /// `Vacant` is used to repr abstract types
    ///
    /// say a list of any element type
    ///
    /// It doesn't mean two elements in the list can be of different type
    ///
    /// It just means that the type is capable of representing any list,
    /// saving the need to recompile.
    ///
    /// It should be noted that phantom template parameter should only accept vacant parameter.
    Vacant,
    Type(HirType),
    Constant(HirCompterm),
    Lifetime(HirLifetimeTemplateVariable),
    ContractedQuary(HirContractedQuary),
}

impl From<HirTemplateVariable> for HirTemplateArgument {
    fn from(variable: HirTemplateVariable) -> Self {
        match variable {
            HirTemplateVariable::Type(variable) => HirTemplateArgument::Type(variable.into()),
            HirTemplateVariable::Compterm(variable) => {
                HirTemplateArgument::Constant(variable.into())
            }
            HirTemplateVariable::Lifetime(variable) => {
                HirTemplateArgument::Lifetime(variable.into())
            }
            HirTemplateVariable::Quary(variable) => {
                HirTemplateArgument::ContractedQuary(variable.into())
            }
        }
    }
}

pub type HirTemplateArguments = smallvec::SmallVec<[HirTemplateArgument; 2]>;

impl HirTemplateArgument {
    pub(crate) fn from_eth(argument: EthTerm, db: &::salsa::Db) -> Option<Self> {
        Some(match argument {
            EthTerm::Literal(lit) => HirCompterm::from_term(lit, db).into(),
            EthTerm::SymbolicVariable(symbol) => HirTemplateVariable::from_eth(symbol, db)?.into(),
            EthTerm::AbstractVariable(_) => todo!(),
            EthTerm::ItemPath(path) => match path {
                ItemPathTerm::MajorForm(_path) => todo!(),
                ItemPathTerm::Trait(_) => todo!(),
                ItemPathTerm::TypeOntology(ty_path) => {
                    let always_copyable = is_ty_term_always_copyable(argument, db).unwrap()?;
                    HirTemplateArgument::Type(
                        HirTypePathLeading::new(db, ty_path, Default::default(), always_copyable)
                            .into(),
                    )
                }
                ItemPathTerm::TypeInstance(_) => todo!(),
                ItemPathTerm::TypeVariant(path) => HirTemplateArgument::Constant(path.into()),
            },
            EthTerm::Sort(_) => todo!(),
            EthTerm::Universe(_) => todo!(),
            EthTerm::Curry(_) => todo!(),
            EthTerm::Ritchie(term) => HirType::Ritchie(HirRitchieType::from_eth(term, db)).into(),
            EthTerm::Abstraction(_) => todo!(),
            EthTerm::Application(application) => {
                hir_ty_from_eth_term_application(db, application).into()
            }
            EthTerm::TypeAsTraitItem(_) => todo!(),
            EthTerm::TraitConstraint(_) => todo!(),
        })
    }

    pub(crate) fn from_fly(term: FlyTerm, db: &::salsa::Db, terms: &FlyTerms) -> Option<Self> {
        match term.base_resolved_inner(terms) {
            FlyTermBase::Eth(ethereal_term) => Self::from_eth(ethereal_term, db),
            FlyTermBase::Sol(_) => todo!(),
            FlyTermBase::Hol(t) => {
                use husky_print_utils::p;
                p!(t, term.show2(db, terms));
                todo!()
            }
            FlyTermBase::Place => todo!(),
        }
    }
}

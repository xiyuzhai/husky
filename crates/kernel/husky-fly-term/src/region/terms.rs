mod hol_terms;
mod sol_terms;

pub use self::hol_terms::*;
pub use self::sol_terms::*;

use super::*;
use husky_eth_term::term::symbolic_variable::EthSymbolicVariable;

// `Default` is not implemented because we might need to initialize `sol_terms` from the parent
#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct FlyTerms {
    sol_terms: SolTerms,
    hol_terms: HolTerms,
}

impl std::borrow::Borrow<HolTerms> for FlyTerms {
    fn borrow(&self) -> &HolTerms {
        &self.hol_terms
    }
}

impl FlyTerms {
    pub(crate) fn new(terms: Option<&Self>) -> Self {
        Self {
            sol_terms: SolTerms::new(terms.map(|terms| &terms.sol_terms)),
            // `Default` is derived for `hollow_terms` because we never inherited hollow terms
            hol_terms: Default::default(),
        }
    }

    pub(crate) fn new_hole_from_template_parameter_symbol(
        &mut self,
        hole_source: HoleSource,
        template_parameter_symbol: EthSymbolicVariable,
        db: &::salsa::Db,
    ) -> HolTerm {
        let hole_kind = match template_parameter_symbol.ty(db) {
            EthTerm::Literal(_) => todo!(),
            EthTerm::SymbolicVariable(_) => HoleKind::AnyOriginal,
            EthTerm::AbstractVariable(_) => todo!(),
            EthTerm::ItemPath(_) => todo!(),
            EthTerm::Sort(cat) => {
                if cat.universe().raw() != 1 {
                    // maybe we need to consider universe
                    todo!()
                }
                HoleKind::ImplicitType
            }
            EthTerm::Universe(_) => todo!(),
            EthTerm::Curry(_) => todo!(),
            EthTerm::Ritchie(_) => todo!(),
            EthTerm::Abstraction(_) => todo!(),
            EthTerm::Application(_) => todo!(),
            EthTerm::TypeAsTraitItem(_) => todo!(),
            EthTerm::TraitConstraint(_) => todo!(),
        };
        self.hol_terms.alloc_new(HolTermData::Hole {
            hole_source,
            hole_kind,
            fill: None,
            constraints: smallvec![],
        })
    }

    #[deprecated(note = "create holes from template parameters directly instead")]
    pub(crate) fn new_hole_from_parameter_hvar(
        &mut self,
        db: &::salsa::Db,
        hole_source: HoleSource,
        parameter_hvar: FlyHvar,
    ) -> HolTerm {
        let hole_kind = match parameter_hvar.base_term_data2(db, self) {
            FlyTermData::AbstractVariable { ty, .. } => match ty.base_term_data2(db, self) {
                FlyTermData::TypeOntology {
                    ty_path: path,
                    refined_ty_path: refined_path,
                    ty_arguments: arguments,
                    ty_ethereal_term,
                } => todo!(),
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
                FlyTermData::Sort(cat) => {
                    if cat.universe().raw() != 1 {
                        // maybe we need to consider universe
                        todo!()
                    }
                    HoleKind::ImplicitType
                }
                FlyTermData::Ritchie {
                    ritchie_kind,
                    parameter_contracted_tys,
                    return_ty,
                } => todo!(),
                FlyTermData::SymbolicVariable { .. } => HoleKind::AnyOriginal,
                FlyTermData::AbstractVariable { .. } => todo!(),
                _ => unreachable!(),
            },
            FlyTermData::Hole(_, _) => todo!(),
            // match parameter_symbol.base() {
            //     FlyTermBase::Ethereal(_) => todo!(),
            //     FlyTermBase::Solid(_) => todo!(),
            //     FlyTermBase::Hollow(hole_term) => return hole_term,
            //     FlyTermBase::Place => todo!(),
            // },
            _ => {
                p!(parameter_hvar.base_term_data2(db, self).debug(db));
                unreachable!()
            }
        };
        self.hol_terms.alloc_new(HolTermData::Hole {
            hole_source,
            hole_kind,
            fill: None,
            constraints: smallvec![],
        })
    }

    pub fn hol_terms(&self) -> &HolTerms {
        &self.hol_terms
    }

    pub fn sol_terms(&self) -> &SolTerms {
        &self.sol_terms
    }

    pub fn hol_terms_mut(&mut self) -> &mut HolTerms {
        &mut self.hol_terms
    }

    pub fn sol_terms_mut(&mut self) -> &mut SolTerms {
        &mut self.sol_terms
    }
}

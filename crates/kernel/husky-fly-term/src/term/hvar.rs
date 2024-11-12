use husky_eth_term::term::abstract_variable::EthAbstractVariable;

use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct FlyHvar(FlyTerm);

impl std::ops::Deref for FlyHvar {
    type Target = FlyTerm;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl FlyHvar {
    pub(crate) fn rewrite_inner(
        self,
        db: &::salsa::Db,
        terms: &mut FlyTerms,
        src: HoleSource,
        substitution_rules: &[FlyTermSubstitution],
    ) -> Self {
        let slf = (*self).rewrite_inner(db, terms, src, substitution_rules);
        match slf.base_ty_data_inner(db, terms) {
            FlyBaseTypeData::TypeOntology {
                ty_path,
                refined_ty_path,
                ty_arguments,
                ty_ethereal_term,
            } => todo!(),
            FlyBaseTypeData::Curry {
                curry_kind,
                variance,
                parameter_hvar,
                parameter_ty,
                return_ty,
                ty_ethereal_term,
            } => todo!(),
            FlyBaseTypeData::Hole(_, _) => todo!(),
            FlyBaseTypeData::Sort(_) => todo!(),
            FlyBaseTypeData::Ritchie {
                ritchie_kind,
                parameter_contracted_tys,
                return_ty,
            } => todo!(),
            FlyBaseTypeData::SymbolicVariable {
                symbolic_variable: symbol,
            } => todo!(),
            FlyBaseTypeData::AbstractVariable {
                abstract_variable: hvar,
            } => (),
        }
        Self(slf)
    }
}

impl From<EthAbstractVariable> for FlyHvar {
    fn from(value: EthAbstractVariable) -> Self {
        FlyHvar(value.into())
    }
}

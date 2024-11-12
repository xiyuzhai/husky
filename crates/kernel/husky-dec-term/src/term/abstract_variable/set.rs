use super::*;
use vec_like::VecSet;

/// unlike DecTermSymbols
/// Some(DecTermHvars { unaccounted_hvars: Default::default() })
/// means different from None
///
/// the former implies that hvars exists, but all accounted
#[salsa::tracked]
pub struct DecTermHvars {
    /// unaccounted means the hvar is not declared within this term
    #[return_ref]
    pub unaccounted_hvars: VecSet<DecAbstractVariable>,
}

impl DecTermHvars {
    #[inline(always)]
    pub(crate) fn contains(self, db: &::salsa::Db, hvar: DecAbstractVariable) -> bool {
        self.unaccounted_hvars(db).has(hvar)
    }

    #[inline(always)]
    fn merge(fst: impl Into<Option<Self>>, snd: impl Into<Option<Self>>) -> Option<Self> {
        let fst: Option<_> = fst.into();
        let snd: Option<_> = snd.into();
        match (fst, snd) {
            (None, None) => None,
            (None, Some(snd)) => Some(snd),
            (Some(fst), None) => Some(fst),
            (Some(_fst), Some(_snd)) => todo!(),
        }
    }

    #[inline(always)]
    fn remove(
        hvars: impl Into<Option<Self>>,
        _hvar: impl Into<Option<DecAbstractVariable>>,
    ) -> Option<Self> {
        let _hvars = hvars.into()?;
        todo!()
    }
}
impl DecTerm {
    pub fn contains_hvar(self, db: &::salsa::Db, hvar: DecAbstractVariable) -> bool {
        self.hvars(db)
            .map(|declarative_term_hvars| declarative_term_hvars.contains(db, hvar))
            .unwrap_or_default()
    }

    pub(crate) fn hvars(self, db: &::salsa::Db) -> Option<DecTermHvars> {
        match self {
            DecTerm::Literal(_) => todo!(),
            DecTerm::AbstractVariable(hvar) => {
                Some(DecTermHvars::new(db, VecSet::new_one_elem_set(hvar)))
            }
            DecTerm::SymbolicVariable(_symbol) => None,
            DecTerm::ItemPath(path) => match path {
                DecItemPath::Form(_) => todo!(),
                DecItemPath::Trait(_) | DecItemPath::Type(_) => None,
                DecItemPath::TypeVariant(_) => todo!(),
            },
            DecTerm::Category(_) => None,
            DecTerm::Universe(_) => None,
            DecTerm::Curry(declarative_term) => {
                declarative_term_curry_placeholders(db, declarative_term)
            }
            DecTerm::Ritchie(declarative_term) => {
                declarative_term_ritchie_hvars(db, declarative_term)
            }
            DecTerm::Abstraction(_) => todo!(),
            DecTerm::Application(declarative_term) => {
                declarative_term_application_hvars(db, declarative_term)
            }
            DecTerm::ApplicationOrRitchieCall(_declarative_ty) => todo!(),
            DecTerm::TypeAsTrait(_) => todo!(),
            DecTerm::TypeAsTraitItem(_) => todo!(),
            DecTerm::TraitConstraint(_) => todo!(),
            DecTerm::LeashOrBitNot(_) => todo!(),
            DecTerm::List(_) => todo!(),
            DecTerm::Wrapper(_) => todo!(),
        }
    }
}

#[salsa::tracked]
pub(crate) fn declarative_term_curry_placeholders(
    db: &::salsa::Db,
    term: DecCurry,
) -> Option<DecTermHvars> {
    let parameter_ty_hvars = term.parameter_ty(db).hvars(db);
    let return_ty_hvars = term.return_ty(db).hvars(db);
    DecTermHvars::merge(
        parameter_ty_hvars,
        DecTermHvars::remove(return_ty_hvars, term.parameter_hvar(db)),
    )
}

#[salsa::tracked]
pub(crate) fn declarative_term_ritchie_hvars(
    db: &::salsa::Db,
    term: DecRitchie,
) -> Option<DecTermHvars> {
    let mut hvars: Option<DecTermHvars> = None;
    for param in term.params(db) {
        hvars = DecTermHvars::merge(hvars, param.ty().hvars(db))
    }
    DecTermHvars::merge(hvars, term.return_ty(db).hvars(db))
}

#[salsa::tracked]
pub(crate) fn declarative_term_application_hvars(
    db: &::salsa::Db,
    term: DecApplication,
) -> Option<DecTermHvars> {
    DecTermHvars::merge(term.function(db).hvars(db), term.argument(db).hvars(db))
}

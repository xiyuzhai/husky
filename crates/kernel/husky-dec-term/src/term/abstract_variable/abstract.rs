use crate::helpers::DecTermFamily;

use super::*;

impl DecTerm {
    // hvar should only be created in curry or abstraction
    /// the only way to create new hvar
    ///
    /// this is not cached because
    /// - it's not called frequently
    /// - it's not computationally
    ///
    /// `<v0: Type> -> A v0 s0` w.r.t `s0` gives `<v1: _> -> <v0: Type> -> A v0 v1`
    /// `<v0: Type> -> A s0` w.r.t `s0` gives `<v1: _> -> <v0: Type> -> A v1`
    ///
    /// In the above two cases, it's necessary to name `s0` as `v1` otherwise there would be ambiguity.
    ///
    /// `A s0 -> <v0: A s0> -> B v0` w.r.t `s0` gives `<v0: _> -> A v0 -> <v0: A v0> -> B v0`
    ///
    /// In the above case, it's okay to name `s0` as `v0` because the inner dependent type hvar declaration overrides the previous one.
    ///
    /// Consider
    /// A s0 -> B (<v12: Type> -> ... -> C s0) (<v1: Type> -> ... -> C s0)
    ///
    /// todo: need thorough testing
    pub(in crate::term) fn create_hvar(
        self,
        db: &::salsa::Db,
        symbol: DecSymbolicVariable,
    ) -> (Self, Option<DecAbstractVariable>) {
        let Some(idx) = self.new_hvar_idx(db, symbol) else {
            return (self, None);
        };
        let hvar = DecAbstractVariable::new(symbol.ty(db), idx, db);
        (
            self.substitute_symbol_with_hvar(db, symbol, hvar),
            Some(hvar),
        )
    }

    pub fn new_curry_hvar() -> Self {
        todo!()
    }

    /// returns the hvar idx if turning this symbol into hvar
    /// returns None if symbol is not present
    #[inline(always)]
    fn new_hvar_idx(self, db: &::salsa::Db, symbol: DecSymbolicVariable) -> Option<u8> {
        self.new_hvar_idx_with_ty_family(db, symbol, symbol.ty_family(db))
    }

    /// with symbol_ty_family already fetched from db
    #[inline(always)]
    fn new_hvar_idx_with_ty_family(
        self,
        db: &::salsa::Db,
        symbol: DecSymbolicVariable,
        symbol_ty_family: DecTermFamily,
    ) -> Option<u8> {
        self.contains_symbol(db, symbol)
            .then(|| self.new_hvar_disambiguator_if_symbol_is_present(db, symbol, symbol_ty_family))
    }

    // todo: needs thorough testing
    fn new_hvar_disambiguator_if_symbol_is_present(
        self,
        db: &::salsa::Db,
        symbol: DecSymbolicVariable,
        symbol_ty_family: DecTermFamily,
    ) -> u8 {
        let mut disambiguator = match self {
            DecTerm::Curry(curry)
                if let Some(hvar) = curry.parameter_hvar(db)
                    && curry.return_ty(db).contains_symbol(db, symbol) =>
            {
                hvar.index(db).disambiguator() + 1
            }
            _ => 0,
        };
        let mut t = |term: DecTerm| {
            if let Some(subidx) = term.new_hvar_idx_with_ty_family(db, symbol, symbol_ty_family) {
                if subidx > disambiguator {
                    disambiguator = subidx
                }
            }
        };
        // scan
        match self {
            DecTerm::Curry(term) => {
                if let Some(v) = term.parameter_hvar(db) {
                    if let Ok(ty) = v.ty(db) {
                        t(ty)
                    }
                }
                t(term.parameter_ty(db));
                t(term.return_ty(db));
            }
            DecTerm::Ritchie(term) => {
                for parameter_ty in term.params(db) {
                    t(parameter_ty.ty())
                }
                t(term.return_ty(db));
            }
            DecTerm::Abstraction(term) => {
                let x = term.x(db);
                let m = term.m(db);
                t(m);
                if x.ty_family(db) == symbol_ty_family && m.contains_symbol(db, symbol) {
                    let x_disambiguator = x.index(db).disambiguator;
                    if x_disambiguator > disambiguator {
                        disambiguator = x_disambiguator
                    }
                }
            }
            DecTerm::Application(term) => {
                t(term.function(db));
                t(term.argument(db))
            }
            DecTerm::ApplicationOrRitchieCall(_) => todo!(),
            DecTerm::TypeAsTrait(_) => todo!(),
            DecTerm::TypeAsTraitItem(_) => todo!(),
            DecTerm::TraitConstraint(_) => todo!(),
            DecTerm::LeashOrBitNot(_) => todo!(),
            DecTerm::List(_) => todo!(),
            DecTerm::Literal(_)
            | DecTerm::SymbolicVariable(_)
            | DecTerm::AbstractVariable(_)
            | DecTerm::ItemPath(_)
            | DecTerm::Category(_)
            | DecTerm::Universe(_) => (),
            DecTerm::Wrapper(_) => todo!(),
        }
        disambiguator
    }

    // todo: needs thorough testing
    /// not cached on purpose
    pub(in crate::term) fn substitute_symbol_with_hvar(
        self,
        db: &::salsa::Db,
        symbol: DecSymbolicVariable,
        hvar: DecAbstractVariable,
    ) -> Self {
        if !self.contains_symbol(db, symbol) {
            return self;
        }
        match self {
            DecTerm::SymbolicVariable(term) if term == symbol => hvar.into(),
            DecTerm::Universe(_) => self, // ad hoc
            DecTerm::Curry(term) => term.substitute_symbol_with_hvar(db, symbol, hvar).into(),
            DecTerm::Ritchie(term) => DecRitchie::new(
                db,
                term.ritchie_kind(db),
                term.params(db)
                    .iter()
                    .map(|parameter_ty| {
                        parameter_ty
                            .substitute_ty(|ty| ty.substitute_symbol_with_hvar(db, symbol, hvar))
                    })
                    .collect(),
                term.return_ty(db)
                    .substitute_symbol_with_hvar(db, symbol, hvar),
            )
            .into(),
            DecTerm::Abstraction(term) => {
                let x = term.x(db);
                // should be equal by the choice of hvar idx and the fact that m contains the symbol
                debug_assert_ne!(x, hvar);
                DecAbstraction::new(
                    db,
                    x,
                    term.m(db).substitute_symbol_with_hvar(db, symbol, hvar),
                )
                .into()
            }
            DecTerm::Application(term) => DecApplication::new(
                db,
                term.function(db)
                    .substitute_symbol_with_hvar(db, symbol, hvar),
                term.argument(db)
                    .substitute_symbol_with_hvar(db, symbol, hvar),
            )
            .into(),
            DecTerm::ApplicationOrRitchieCall(_) => todo!(),
            DecTerm::TypeAsTraitItem(_) => todo!(),
            DecTerm::TraitConstraint(_) => todo!(),
            DecTerm::LeashOrBitNot(_) => todo!(),
            DecTerm::List(_) => todo!(),
            _ => self,
        }
    }
}

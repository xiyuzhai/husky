use super::*;

#[salsa::interned]
pub struct DecTermSymbols {
    #[return_ref]
    symbols: VecSet<DecSymbolicVariable>,
}

impl DecTermSymbols {
    pub(crate) fn contains(self, db: &::salsa::Db, symbol: DecSymbolicVariable) -> bool {
        self.symbols(db).has(symbol)
    }

    fn merge(
        db: &::salsa::Db,
        fst: impl Into<Option<Self>>,
        snd: impl Into<Option<Self>>,
    ) -> Option<Self> {
        let fst: Option<_> = fst.into();
        let snd: Option<_> = snd.into();
        match (fst, snd) {
            (None, None) => None,
            (None, Some(snd)) => Some(snd),
            (Some(fst), None) => Some(fst),
            (Some(fst), Some(snd)) => {
                let mut symbols = fst.symbols(db).clone();
                symbols.extend(snd.symbols(db).iter().copied());
                Some(DecTermSymbols::new(db, symbols))
            }
        }
    }
}
impl DecTerm {
    pub fn contains_symbol(self, db: &::salsa::Db, symbol: DecSymbolicVariable) -> bool {
        calc_dec_symbolic_variables(db, self)
            .map(|dec_symbolic_variables| dec_symbolic_variables.contains(db, symbol))
            .unwrap_or_default()
    }
}

fn calc_dec_symbolic_variables(
    db: &::salsa::Db,
    declarative_term: DecTerm,
) -> Option<DecTermSymbols> {
    match declarative_term {
        DecTerm::Literal(_) => None,
        DecTerm::SymbolicVariable(symbol) => {
            Some(DecTermSymbols::new(db, VecSet::new_one_elem_set(symbol)))
        }
        DecTerm::AbstractVariable(_) => None,
        DecTerm::ItemPath(path) => match path {
            DecItemPath::Form(_) => todo!(),
            DecItemPath::Trait(_) | DecItemPath::Type(_) => None,
            DecItemPath::TypeVariant(_) => todo!(),
        },
        DecTerm::Category(_) => None,
        DecTerm::Universe(_) => None,
        DecTerm::Curry(declarative_term) => declarative_term_curry_symbols(db, declarative_term),
        DecTerm::Ritchie(declarative_term) => {
            declarative_term_ritchie_symbols(db, declarative_term)
        }
        DecTerm::Abstraction(_) => todo!(),
        DecTerm::Application(declarative_term) => {
            application_dec_symbolic_variables(db, declarative_term)
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

#[salsa::tracked]
pub(crate) fn declarative_term_curry_symbols(
    db: &::salsa::Db,
    declarative_term: DecCurry,
) -> Option<DecTermSymbols> {
    let parameter_ty_symbols = calc_dec_symbolic_variables(db, declarative_term.parameter_ty(db));
    let return_ty_symbols = calc_dec_symbolic_variables(db, declarative_term.return_ty(db));
    DecTermSymbols::merge(db, parameter_ty_symbols, return_ty_symbols)
}

#[salsa::tracked]
pub(crate) fn declarative_term_ritchie_symbols(
    db: &::salsa::Db,
    declarative_term: DecRitchie,
) -> Option<DecTermSymbols> {
    let mut symbols: Option<DecTermSymbols> = None;
    for param in declarative_term.params(db) {
        symbols = DecTermSymbols::merge(db, symbols, calc_dec_symbolic_variables(db, param.ty()))
    }
    DecTermSymbols::merge(
        db,
        symbols,
        calc_dec_symbolic_variables(db, declarative_term.return_ty(db)),
    )
}

#[salsa::tracked]
pub(crate) fn application_dec_symbolic_variables(
    db: &::salsa::Db,
    declarative_term: DecApplication,
) -> Option<DecTermSymbols> {
    DecTermSymbols::merge(
        db,
        calc_dec_symbolic_variables(db, declarative_term.function(db)),
        calc_dec_symbolic_variables(db, declarative_term.argument(db)),
    )
}

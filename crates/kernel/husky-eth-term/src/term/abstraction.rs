use super::*;
use husky_dec_term::term::abstraction::DecAbstraction;

#[salsa::interned]
pub struct EthAbstraction {
    x: EthAbstractVariable,
    m: EthTerm,
}

#[test]
fn term_abstraction_size_works() {
    assert_eq!(
        std::mem::size_of::<EthAbstraction>(),
        std::mem::size_of::<u32>()
    );
}

impl EthAbstraction {
    pub(crate) fn from_dec(
        _db: &::salsa::Db,
        _precise_term: DecAbstraction,
        _term_ty_expectation: TypeFinalDestinationExpectation,
    ) -> EthTermResult<Self> {
        todo!()
    }

    pub fn ty(&self) -> EthTerm {
        todo!()
    }
}

/// # rewrite

impl EthAbstraction {
    pub fn substitute(self, substitution: EthTermSubstitution, db: &::salsa::Db) -> Self {
        let old_x = self.x(db);
        let new_x = old_x.substitute_intact(substitution, db);
        let old_m = self.m(db);
        let new_m = old_m.substitute(substitution, db);
        if old_x == new_x && old_m == new_m {
            return self;
        }
        Self::new(db, new_x, new_m)
    }
}

impl EthInstantiate for EthAbstraction {
    type Output = EthAbstraction;

    fn instantiate(
        self,
        instantiation: &EthInstantiation,
        ctx: impl IsEthTermContextRef,
        db: &::salsa::Db,
    ) -> Self::Output {
        Self::new(
            db,
            self.x(db).instantiate(instantiation, ctx, db),
            self.m(db).instantiate(instantiation, ctx, db),
        )
    }
}

impl salsa::DisplayWithDb for EthAbstraction {
    fn display_fmt_with_db(
        &self,
        _f: &mut std::fmt::Formatter<'_>,
        _db: &::salsa::Db,
    ) -> std::fmt::Result {
        // use std::fmt::Write;
        // f.write_char(husky_unicode_symbols::greek::GREEK_LETTER_LOWERCASE_LAMBDA);
        // todo!()
        todo!()
    }
}

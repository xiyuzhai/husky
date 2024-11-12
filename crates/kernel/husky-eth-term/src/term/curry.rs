mod utils;

pub(crate) use self::utils::*;

use super::*;

/// representing term `X -> Y` or dependent form `(a: X) -> Y(a)`
#[salsa::interned(constructor = new_inner)]
pub struct EthCurry {
    pub toolchain: Toolchain,
    pub curry_kind: CurryKind,
    pub variance: Variance,
    /// a
    pub parameter_hvar: Option<EthAbstractVariable>,
    /// X
    pub parameter_ty: EthTerm,
    /// Y
    pub return_ty: EthTerm,
}

#[test]
fn term_curry_size_works() {
    assert_eq!(std::mem::size_of::<EthCurry>(), std::mem::size_of::<u32>());
}

/// # constructors

impl EthCurry {
    pub fn new(
        toolchain: Toolchain,
        curry_kind: CurryKind,
        variance: Variance,
        parameter_hvar: Option<EthAbstractVariable>,
        parameter_ty: EthTerm,
        return_ty: EthTerm,
        db: &::salsa::Db,
    ) -> Self {
        Self::new_inner(
            db,
            toolchain,
            curry_kind,
            variance,
            parameter_hvar,
            parameter_ty.reduce(db),
            return_ty.reduce(db),
        )
    }

    pub(crate) fn from_dec(
        db: &::salsa::Db,
        declarative_term_curry: DecCurry,
    ) -> EthTermResult<Self> {
        term_curry_from_dec(db, declarative_term_curry)
    }
}

/// # rewrite

impl EthCurry {
    pub fn substitute(self, substitution: EthTermSubstitution, db: &::salsa::Db) -> Self {
        let parameter_hvar = self.parameter_hvar(db);
        if parameter_hvar == Some(substitution.src()) {
            return self;
        }
        Self::new(
            self.toolchain(db),
            self.curry_kind(db),
            self.variance(db),
            parameter_hvar.map(|hvar| hvar.substitute_intact(substitution, db)),
            self.parameter_ty(db),
            self.return_ty(db),
            db,
        )
    }
}

impl EthInstantiate for EthCurry {
    type Output = Self;

    fn instantiate(
        self,
        instantiation: &EthInstantiation,
        ctx: impl IsEthTermContextRef,
        db: &::salsa::Db,
    ) -> Self::Output {
        Self::new(
            self.toolchain(db),
            self.curry_kind(db),
            self.variance(db),
            self.parameter_hvar(db).instantiate(instantiation, ctx, db),
            self.parameter_ty(db).instantiate(instantiation, ctx, db),
            self.return_ty(db).instantiate(instantiation, ctx, db),
            db,
        )
    }
}

#[salsa::tracked]
pub(crate) fn term_curry_from_dec(db: &::salsa::Db, curry: DecCurry) -> EthTermResult<EthCurry> {
    let t = |declarative_ty| EthTerm::ty_from_dec(db, declarative_ty);
    Ok(EthCurry::new(
        curry.toolchain(db),
        curry.curry_kind(db),
        curry.variance(db),
        match curry.parameter_hvar(db) {
            Some(parameter_hvar) => Some(EthAbstractVariable::from_dec(db, parameter_hvar)?),
            None => None,
        },
        t(curry.parameter_ty(db))?,
        t(curry.return_ty(db))?,
        db,
    ))
}

impl salsa::DisplayWithDb for EthCurry {
    fn display_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
    ) -> std::fmt::Result {
        let parameter_hvar = self.parameter_hvar(db);
        if parameter_hvar.is_some() {
            f.write_str("(")?
        }
        f.write_str(self.variance(db).as_str())?;
        if let Some(parameter_hvar) = parameter_hvar {
            parameter_hvar.display_fmt_with_db(f, db)?;
            f.write_str(": ")?;
            self.parameter_ty(db).display_fmt_with_db(f, db)?;
            f.write_str(") -> ")?;
            self.return_ty(db).display_fmt_with_db(f, db)
        } else {
            self.parameter_ty(db).display_fmt_with_db(f, db)?;
            f.write_str(" -> ")?;
            self.return_ty(db).display_fmt_with_db(f, db)
        }
    }
}

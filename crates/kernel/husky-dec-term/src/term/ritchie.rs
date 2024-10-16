mod keyed;
mod regular;
mod variadic;

pub use self::keyed::*;
pub use self::regular::*;
pub use self::variadic::*;

use super::*;
use husky_term_prelude::ritchie::RitchieKind;
use smallvec::SmallVec;

/// representing declarative_term `x -> y`
#[salsa::interned]
pub struct DecRitchie {
    pub ritchie_kind: RitchieKind,
    #[return_ref]
    pub params: SmallVec<[DeclarativeRitchieParameter; 2]>,
    pub return_ty: DecTerm,
    // ty: DecTerm,
}

impl DecRitchie {
    #[inline(never)]
    pub(crate) fn display_fmt_with_db_and_ctx(
        self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
        ctx: &DecSymbolicVariableNameMap,
    ) -> std::fmt::Result {
        f.write_str(self.ritchie_kind(db).code())?;
        f.write_str("(")?;
        for (i, parameter_ty) in self.params(db).iter().enumerate() {
            if i > 0 {
                f.write_str(", ")?
            }
            parameter_ty.display_fmt_with_db_and_ctx(f, db, ctx)?
        }
        f.write_str(") -> ")?;
        self.return_ty(db).display_fmt_with_db_and_ctx(f, db, ctx)
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
#[enum_class::from_variants]
pub enum DeclarativeRitchieParameter {
    Simple(DeclarativeRitchieSimpleParameter),
    Variadic(DeclarativeRitchieVariadicParameter),
    Keyed(DeclarativeRitchieKeyedParameter),
}

impl DeclarativeRitchieParameter {
    pub fn ty(&self) -> DecTerm {
        match self {
            DeclarativeRitchieParameter::Simple(param) => param.ty(),
            DeclarativeRitchieParameter::Variadic(param) => param.ty(),
            DeclarativeRitchieParameter::Keyed(param) => param.ty(),
        }
    }

    pub(crate) fn substitute_ty(self, f: impl Fn(DecTerm) -> DecTerm) -> Self {
        match self {
            DeclarativeRitchieParameter::Simple(param) => param.substitute_ty(f).into(),
            DeclarativeRitchieParameter::Variadic(param) => param.substitute_ty(f).into(),
            DeclarativeRitchieParameter::Keyed(param) => param.substitute_ty(f).into(),
        }
    }

    fn display_fmt_with_db_and_ctx(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
        ctx: &DecSymbolicVariableNameMap,
    ) -> std::fmt::Result {
        match self {
            DeclarativeRitchieParameter::Simple(param) => {
                param.display_fmt_with_db_and_ctx(f, db, ctx)
            }
            DeclarativeRitchieParameter::Variadic(param) => {
                param.display_fmt_with_db_and_ctx(f, db, ctx)
            }
            DeclarativeRitchieParameter::Keyed(param) => {
                param.display_fmt_with_db_and_ctx(f, db, ctx)
            }
        }
    }
}

impl DecTermRewriteCopy for DecRitchie {
    fn substitute_copy(self, _db: &::salsa::Db, _substitution: &DecTermSubstitution) -> Self {
        todo!()
    }
}

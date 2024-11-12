use super::*;

#[salsa::interned]
pub struct DecAbstraction {
    pub x: DecAbstractVariable,
    pub m: DecTerm,
}

impl DecAbstraction {
    pub fn ty(&self) -> DecTerm {
        todo!()
    }

    #[inline(never)]
    pub(crate) fn display_fmt_with_db_and_ctx(
        self,
        _f: &mut std::fmt::Formatter<'_>,
        _db: &::salsa::Db,
        _ctx: &DecSymbolicVariableNameMap,
    ) -> std::fmt::Result {
        todo!()
    }
}

impl DecTermRewriteCopy for DecAbstraction {
    fn substitute_copy(self, _db: &::salsa::Db, _substitution: &DecTermSubstitution) -> Self {
        todo!()
    }
}

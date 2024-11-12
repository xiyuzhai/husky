use self::name::DecSymbolicVariableNameMap;
use crate::*;
use salsa::DisplayWithDb;

impl DecTerm {
    #[deprecated(note = "todo: redo this, see eth term")]
    pub(crate) fn display_fmt_with_db_and_ctx(
        self,
        f: &mut std::fmt::Formatter<'_>,
        db: &::salsa::Db,
        ctx: &DecSymbolicVariableNameMap,
    ) -> std::fmt::Result {
        match self {
            DecTerm::Literal(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::SymbolicVariable(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::AbstractVariable(term) => term.display_fmt_with_db(f, db),
            DecTerm::ItemPath(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::Category(term) => f.write_str(&term.to_string()),
            DecTerm::Universe(term) => f.write_str(&term.to_string()),
            DecTerm::Curry(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::Ritchie(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::Abstraction(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::Application(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::ApplicationOrRitchieCall(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::TypeAsTrait(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::TypeAsTraitItem(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::TraitConstraint(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::LeashOrBitNot(_) => f.write_str("~"),
            DecTerm::List(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
            DecTerm::Wrapper(term) => term.display_fmt_with_db_and_ctx(f, db, ctx),
        }
    }
}

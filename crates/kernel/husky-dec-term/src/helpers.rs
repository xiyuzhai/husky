use crate::*;
use husky_entity_path::{menu::item_path_menu, path::major_item::ty::TypePath};

impl DecTerm {
    #[inline(always)]
    pub fn apply(self, db: &::salsa::Db, argument: impl Into<DecTerm>) -> Self {
        DecApplication::new(db, self, argument.into()).into()
    }

    pub fn family(self, db: &::salsa::Db) -> DecTermFamily {
        match self {
            DecTerm::ItemPath(DecItemPath::Type(path)) => DecTermFamily::TypePath(path),
            DecTerm::Category(cat) => DecTermFamily::Category(cat),
            DecTerm::Application(term) => term.function(db).family(db),
            DecTerm::ApplicationOrRitchieCall(term) => term.function(db).family(db),
            DecTerm::LeashOrBitNot(toolchain) => {
                DecTermFamily::TypePath(item_path_menu(db, toolchain).leash_ty_path())
            }
            _ => DecTermFamily::Other,
        }
    }

    /// see `self` as the type of another term, return the type expectation for that term
    pub fn ty_final_destination_expectation(
        self,
        db: &::salsa::Db,
    ) -> DecTermResult<TypeFinalDestinationExpectation> {
        match self {
            DecTerm::ItemPath(DecItemPath::Type(path)) => {
                Ok(TypeFinalDestinationExpectation::EqsNonSortTypePath(path))
            }
            DecTerm::Category(_) => Ok(TypeFinalDestinationExpectation::EqsSort),
            DecTerm::Curry(slf) => slf.return_ty(db).ty_final_destination_expectation(db),
            DecTerm::Application(slf) => slf.function(db).ty_final_destination_expectation(db),
            _ => Ok(TypeFinalDestinationExpectation::Any),
        }
    }

    pub const PROP: DecTerm = DecTerm::Category(Sort::new(Universe::new(0)));

    pub const TYPE: DecTerm = DecTerm::Category(Sort::new(Universe::new(1)));
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum DecTermFamily {
    Category(Sort),
    TypePath(TypePath),
    Other,
}

impl DecSymbolicVariable {
    pub(crate) fn ty_family(self, db: &::salsa::Db) -> DecTermFamily {
        self.ty(db)
            .ok()
            .map(|ty| ty.family(db))
            .unwrap_or(DecTermFamily::Other)
    }
}

impl DecAbstractVariable {
    pub(crate) fn ty_family(self, db: &::salsa::Db) -> DecTermFamily {
        self.ty(db)
            .ok()
            .map(|ty| ty.family(db))
            .unwrap_or(DecTermFamily::Other)
    }
}

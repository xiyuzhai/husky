use super::*;
use husky_entity_path::menu::{item_path_menu, ItemPathMenu};

impl EthTerm {
    /// returns a toolchain except for universe, literals and categories
    pub fn toolchain(self, db: &::salsa::Db) -> Option<Toolchain> {
        match self {
            EthTerm::Literal(_) => None,
            EthTerm::SymbolicVariable(term) => Some(term.toolchain(db)),
            EthTerm::AbstractVariable(term) => term.toolchain(db),
            EthTerm::ItemPath(path) => Some(path.toolchain(db)),
            EthTerm::Sort(_) => None,
            EthTerm::Universe(_) => None,
            EthTerm::Curry(term) => ethereal_term_curry_toolchain(db, term),
            EthTerm::Ritchie(term) => ethereal_term_ritchie_toolchain(db, term),
            EthTerm::Abstraction(_) => todo!(),
            EthTerm::Application(term) => ethereal_term_application_toolchain(db, term),
            EthTerm::TypeAsTraitItem(term) => Some(term.trai_item_path(db).toolchain(db)),
            EthTerm::TraitConstraint(_) => todo!(),
        }
    }

    pub fn item_path_menu(self, db: &::salsa::Db) -> Option<&ItemPathMenu> {
        Some(item_path_menu(db, self.toolchain(db)?))
    }

    pub fn ethereal_term_menu(self, db: &::salsa::Db) -> Option<&EthTermMenu> {
        Some(db.eth_term_menu(self.toolchain(db)?))
    }
}

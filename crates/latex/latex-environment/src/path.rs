pub mod menu;

use husky_coword::Coword;
use thiserror::Error;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LxEnvironmentPath {
    name: LxEnvironmentName,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LxEnvironmentName(Coword);

impl LxEnvironmentPath {
    pub fn new(name: &str, db: &::salsa::Db) -> Self {
        Self {
            name: LxEnvironmentName::from_ref(name, db),
        }
    }
}

impl LxEnvironmentPath {
    pub fn name(&self) -> LxEnvironmentName {
        self.name
    }
}

impl LxEnvironmentName {
    pub fn new(coword: Coword) -> Self {
        Self(coword)
    }

    pub fn from_ref(name: &str, db: &::salsa::Db) -> Self {
        Self(Coword::from_ref(db, name))
    }
}

impl LxEnvironmentName {
    pub fn coword(self) -> Coword {
        self.0
    }
}

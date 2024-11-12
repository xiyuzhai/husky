pub mod menu;

use husky_coword::Coword;
use thiserror::Error;

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LxCommandPath {
    package: LxPackagePath,
    name: LxCommandName,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxPackagePath {
    Prelude,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxCommandName {
    LettersOnly(LettersOnlyLxCommandName),
    Escape(OneDigitNonLetterLxCommandName),
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LettersOnlyLxCommandName(Coword);

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OneDigitNonLetterLxCommandName(char);

impl LxCommandPath {
    #[deprecated(note = "ad hoc")]
    pub fn new_prelude(ident: Coword, db: &salsa::Db) -> Self {
        Self {
            package: LxPackagePath::Prelude,
            name: LxCommandName::new(ident, db).unwrap(),
        }
    }
}

impl LxCommandPath {
    pub fn package(&self) -> LxPackagePath {
        self.package
    }

    pub fn name(&self) -> LxCommandName {
        self.name
    }
}

impl LxCommandName {
    pub fn new(ident: Coword, db: &salsa::Db) -> LxCommandNameResult<Self> {
        let data = ident.data(db);
        if data.len() == 0 {
            Err(LxCommandNameError::Empty)?
        } else if data.len() == 1 {
            let c = data.chars().next().unwrap();
            if !c.is_alphabetic() {
                return Ok(Self::Escape(OneDigitNonLetterLxCommandName(c)));
            }
        } else {
            for c in data.chars() {
                if !c.is_alphabetic() {
                    Err(LxCommandNameError::NonAlphabeticCharater(c))?;
                }
            }
        }
        Ok(Self::LettersOnly(LettersOnlyLxCommandName(ident)))
    }

    pub fn new2(data: &str, db: &salsa::Db) -> LxCommandNameResult<Self> {
        if data.len() == 0 {
            Err(LxCommandNameError::Empty)?
        } else if data.len() == 1 {
            let c = data.chars().next().unwrap();
            if !c.is_alphabetic() {
                return Ok(Self::Escape(OneDigitNonLetterLxCommandName(c)));
            }
        } else {
            for c in data.chars() {
                if !c.is_alphabetic() {
                    Err(LxCommandNameError::NonAlphabeticCharater(c))?;
                }
            }
        }
        Ok(Self::LettersOnly(LettersOnlyLxCommandName(
            Coword::from_ref(db, data),
        )))
    }
}

impl salsa::DisplayWithDb for LxCommandName {
    fn display_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        db: &salsa::Db,
    ) -> std::fmt::Result {
        match self {
            Self::LettersOnly(LettersOnlyLxCommandName(c)) => write!(f, "{}", c.data(db)),
            Self::Escape(OneDigitNonLetterLxCommandName(c)) => write!(f, "{}", c),
        }
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Error, PartialEq, Eq, Clone, Copy)]
pub enum LxCommandNameError {
    /// command identifier cannot be empty
    #[error("empty identifier")]
    Empty,
    /// for an identifier with len > 1, all characters must be alphabetic
    #[error("non alphabetic character `{0}` in command name is not allowed")]
    NonAlphabeticCharater(char),
}

pub type LxCommandNameResult<T> = Result<T, LxCommandNameError>;

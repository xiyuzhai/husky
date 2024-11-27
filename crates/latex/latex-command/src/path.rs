pub mod menu;

use coword::Coword;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LxCommandPath {
    package: LxPackagePath,
    name: LxCommandName,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxPackagePath {
    Prelude,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LxCommandName {
    LettersOnly(LettersOnlyLxCommandName),
    Escape(OneDigitNonLetterLxCommandName),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct LettersOnlyLxCommandName(Coword);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct OneDigitNonLetterLxCommandName(char);

impl LxCommandPath {
    #[deprecated(note = "ad hoc")]
    pub fn new_prelude(ident: Coword) -> Self {
        Self {
            package: LxPackagePath::Prelude,
            name: LxCommandName::new(ident).unwrap(),
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
    pub fn new(ident: Coword) -> LxCommandNameResult<Self> {
        let data = ident.data();
        if data.len() == 0 {
            Err(LxCommandNameError::Empty)?
        } else if data.len() == 1 {
            let c = data.chars().next().unwrap();
            if !c.is_ascii_alphabetic() {
                return Ok(Self::Escape(OneDigitNonLetterLxCommandName(c)));
            }
        } else {
            for c in data.chars() {
                if !c.is_ascii_alphabetic() {
                    Err(LxCommandNameError::NonAsciiAlphabeticCharater(c))?;
                }
            }
        }
        Ok(Self::LettersOnly(LettersOnlyLxCommandName(ident)))
    }

    pub fn new2(data: &str) -> LxCommandNameResult<Self> {
        if data.len() == 0 {
            Err(LxCommandNameError::Empty)?
        } else if data.len() == 1 {
            let c = data.chars().next().unwrap();
            if !c.is_ascii_alphabetic() {
                return Ok(Self::Escape(OneDigitNonLetterLxCommandName(c)));
            }
        } else {
            for c in data.chars() {
                if !c.is_ascii_alphabetic() {
                    Err(LxCommandNameError::NonAsciiAlphabeticCharater(c))?;
                }
            }
        }
        Ok(Self::LettersOnly(LettersOnlyLxCommandName(
            Coword::from_ref(data),
        )))
    }
}

impl std::fmt::Display for LxCommandName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LettersOnly(LettersOnlyLxCommandName(c)) => write!(f, "{}", c.data()),
            Self::Escape(OneDigitNonLetterLxCommandName(c)) => write!(f, "{}", c),
        }
    }
}

#[derive(Debug, Error, PartialEq, Eq, Clone, Copy)]
pub enum LxCommandNameError {
    /// command identifier cannot be empty
    #[error("empty identifier")]
    Empty,
    /// for an identifier with len > 1, all characters must be alphabetic
    #[error("non alphabetic character `{0}` in command name is not allowed")]
    NonAsciiAlphabeticCharater(char),
}

pub type LxCommandNameResult<T> = Result<T, LxCommandNameError>;

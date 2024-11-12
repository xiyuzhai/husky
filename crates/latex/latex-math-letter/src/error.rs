use thiserror::Error;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Error)]
pub enum LxMathLetterError {
    #[error("cannot apply letter style to lower case latin letter")]
    CannotApplyLetterStyleToLowerCaseLatinLetter,
}

pub type LxMathLetterResult<T> = Result<T, LxMathLetterError>;

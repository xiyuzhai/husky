use std::path::PathBuf;
use thiserror::Error;

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum IoError {
    #[error("io error: {0}")]
    Io(PathBuf, String),
}

pub type IoResult<T> = Result<T, IoError>;

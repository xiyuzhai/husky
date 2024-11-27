use maybe_result::MaybeResult;
use std::path::PathBuf;
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LpCsvError {
    InvalidValue(String),
}

pub type LpCsvResult<T> = Result<T, LpCsvError>;
pub type LpCsvMaybeResult<T> = MaybeResult<T, LpCsvError>;

#[derive(Debug, Error)]
pub enum LpCsvFileError {
    #[error("io error: {error} for file: {file_path}")]
    Io {
        file_path: PathBuf,
        error: std::io::Error,
    },
    #[error("parse error: {input}")]
    Parse { input: String, error: LpCsvError },
}

pub type LpCsvFileResult<T> = Result<T, LpCsvFileError>;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum TpVfsError {
    #[error("metadata io")]
    MetadataIO(std::io::Error),
    #[error("modified")]
    Modified(std::io::Error),
    #[error("during since")]
    DuringSince(std::time::SystemTimeError),
    #[error("write")]
    Write(std::io::Error),
    #[error("read")]
    Read(std::io::Error),
}

pub type TpVfsResult<T> = Result<T, TpVfsError>;

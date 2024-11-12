use super::*;

#[derive(Debug, Error)]
pub enum VdSemExprTypeError {
    #[error("original error({0})")]
    Original(OriginalVdSemExprTypeError),
    #[error("derived error({0})")]
    Derived(DerivedVdSemExprTypeError),
}

#[derive(Debug, Error)]
pub enum OriginalVdSemExprTypeError {
    #[error("todo")]
    Todo,
}

#[derive(Debug, Error)]
pub enum DerivedVdSemExprTypeError {
    #[error("todo")]
    Todo,
}

pub type VdSemExprTypeResult<T> = Result<T, VdSemExprTypeError>;
pub type VdSemExprTypeResultRef<'a, T> = Result<T, &'a VdSemExprTypeError>;

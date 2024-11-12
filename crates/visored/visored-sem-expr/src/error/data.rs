use super::*;

#[derive(Debug, Error)]
pub enum VdSemExprDataError {
    #[error("original error({0})")]
    Original(OriginalVdSemExprDataError),
    #[error("derived error({0})")]
    Derived(DerivedVdSemExprDataError),
}

#[derive(Debug, Error)]
pub enum OriginalVdSemExprDataError {
    #[error("todo")]
    Todo,
}

#[derive(Debug, Error)]
pub enum DerivedVdSemExprDataError {
    #[error("todo")]
    Todo,
}

pub type VdSemExprDataResult<T> = Result<T, VdSemExprDataError>;
pub type VdSemExprDataResultRef<'a, T> = Result<T, &'a VdSemExprDataError>;

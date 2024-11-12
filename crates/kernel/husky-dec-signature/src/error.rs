use crate::*;
use husky_manifest::error::ManifestError;
use husky_syn_decl::error::{SynDeclError, SynNodeDeclError};
use husky_syn_expr::error::SynExprError;
use thiserror::Error;

#[salsa::derive_debug_with_db]
#[derive(Debug, Error, PartialEq, Eq, Clone, Copy)]
pub enum DecSignatureError {
    #[error("todo")]
    DecTermError,
    #[error("todo")]
    ParameterTypeDecTermError(u8),
    #[error("todo")]
    FieldTypeDecTermError(u8),
    #[error("todo")]
    ReturnTypeDecTermError,
    // derived
    #[error("todo")]
    SynDeclError(SynDeclError),
    #[error("todo")]
    NodeDeclError,
    #[error("todo")]
    ExprError,
    #[error("todo")]
    SelfTypeNotInferred,
    #[error("cyclic proj")]
    CyclicProj,
}

impl From<&DecSignatureError> for DecSignatureError {
    fn from(e: &DecSignatureError) -> Self {
        *e
    }
}

impl From<SynExprDecTermError> for DecSignatureError {
    fn from(value: SynExprDecTermError) -> Self {
        todo!()
    }
}

impl From<SynDeclError> for DecSignatureError {
    fn from(e: SynDeclError) -> Self {
        DecSignatureError::SynDeclError(e)
    }
}

impl From<&SynNodeDeclError> for DecSignatureError {
    fn from(_: &SynNodeDeclError) -> Self {
        DecSignatureError::NodeDeclError
    }
}
impl From<&SynExprError> for DecSignatureError {
    fn from(_: &SynExprError) -> Self {
        DecSignatureError::ExprError
    }
}

impl From<&ManifestError> for DecSignatureError {
    fn from(e: &ManifestError) -> Self {
        husky_print_utils::p!(e);
        todo!()
    }
}

impl From<&DecTermError> for DecSignatureError {
    fn from(value: &DecTermError) -> Self {
        DecSignatureError::DecTermError
    }
}

impl From<&SynExprDecTermError> for DecSignatureError {
    fn from(value: &SynExprDecTermError) -> Self {
        DecSignatureError::DecTermError
    }
}

pub type DecSignatureResult<T> = Result<T, DecSignatureError>;

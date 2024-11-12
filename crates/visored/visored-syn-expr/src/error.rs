use crate::expr::{VdSynBinaryOpr, VdSynExprIdx, VdSynPrefixOpr};
use either::Either;
use latex_token::idx::{LxTokenIdx, LxTokenIdxRange};
use thiserror::Error;
use visored_opr::opr::{binary::VdBaseBinaryOpr, prefix::VdBasePrefixOpr};

#[derive(Debug, Error, PartialEq, Eq)]
pub enum VdSynExprError {
    #[error("original error({0})")]
    Original(#[from] OriginalVdSynExprError),
    #[error("derived error({0})")]
    Derived(#[from] DerivedVdSynExprError),
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum OriginalVdSynExprError {
    #[error("empty")]
    Empty(LxTokenIdxRange),
    #[error("todo")]
    Todo,
    #[error("no right operand for binary operator")]
    NoRightOperandForBinaryOperator { opr: VdSynBinaryOpr },
    #[error("no operand for prefix operator")]
    NoOperandForPrefixOperator { opr: VdSynPrefixOpr },
    #[error("unterminated list")]
    UnterminatedList { bra_token_idx: LxTokenIdx },
    #[error("no left operand for binary operator")]
    NoLeftOperandForBinaryOperator { opr: VdSynBinaryOpr },
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum DerivedVdSynExprError {
    #[error("todo")]
    Todo,
}

pub type VdSynExprResult<T> = Result<T, VdSynExprError>;
pub type VdSynExprResultRef<'a, T> = Result<T, &'a VdSynExprError>;

impl VdSynExprError {
    pub fn token_idx_range(&self) -> LxTokenIdxRange {
        match self {
            VdSynExprError::Original(error) => error.token_idx_range(),
            VdSynExprError::Derived(error) => error.token_idx_range(),
        }
    }
}

impl OriginalVdSynExprError {
    pub fn token_idx_range(&self) -> LxTokenIdxRange {
        match *self {
            OriginalVdSynExprError::Empty(range) => range,
            OriginalVdSynExprError::Todo => todo!(),
            OriginalVdSynExprError::NoRightOperandForBinaryOperator { .. } => todo!(),
            OriginalVdSynExprError::NoOperandForPrefixOperator { .. } => todo!(),
            OriginalVdSynExprError::UnterminatedList { bra_token_idx } => todo!(),
            OriginalVdSynExprError::NoLeftOperandForBinaryOperator { opr } => todo!(),
        }
    }
}

impl DerivedVdSynExprError {
    pub fn token_idx_range(&self) -> LxTokenIdxRange {
        match self {
            Self::Todo => todo!(),
        }
    }
}

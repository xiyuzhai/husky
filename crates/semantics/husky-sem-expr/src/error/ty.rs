use super::*;
use husky_entity_path::path::major_item::ty::TypePath;

#[salsa::derive_debug_with_db]
#[derive(Debug, Error, PartialEq, Eq)]
pub enum SemExprTypeError {
    #[error("original {0}")]
    Original(#[from] OriginalSemExprTypeError),
    #[error("derived {0}")]
    Derived(#[from] DerivedSemExprTypeError),
}

impl From<EthSignatureError> for SemExprTypeError {
    fn from(e: EthSignatureError) -> Self {
        SemExprTypeError::Derived(e.into())
    }
}

impl From<EthTermError> for SemExprTypeError {
    fn from(e: EthTermError) -> Self {
        SemExprTypeError::Derived(e.into())
    }
}

impl From<FlyTermError> for SemExprTypeError {
    fn from(e: FlyTermError) -> Self {
        SemExprTypeError::Derived(e.into())
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Error, PartialEq, Eq)]
pub enum OriginalSemExprTypeError {
    #[error("unresolved term")]
    UnresolvedTerm,
    #[error("type method type error")]
    TypeMethodTypeError,
    #[error("type call type error")]
    TypeCallTypeError,
    #[error("TodoScopeResolution")]
    TodoScopeResolution,
    #[error("TodoBoxColon")]
    TodoBoxColon,
    #[error("final destination")]
    FinalDestination,
    #[error("form path type error")]
    FormPathTypeError,
    #[error("ambiguous type path")]
    AmbiguousTypePath,
    #[error("ritchie call wrong number of arguments")]
    RitchieCallWrongNumberOfArguments {
        number_of_nonself_parameters: u8,
        number_of_nonself_arguments: u8,
    },
    #[error("ambiguous list expr")]
    AmbiguousListExpr,
    #[error("AmbiguousTildeExpr")]
    AmbiguousTildeExpr,
    #[error("ExpectedCurryButGotRitchieInstead")]
    ExpectedCurryButGotRitchieInstead,
    #[error("cannot unveil")]
    CannotUnveil,
    #[error("cannot unwrap")]
    CannotUnwrap,
    #[error("no constructor")]
    NoConstructor { path: TypePath },
    /// in husky, i8 ~ isize, u8 ~ usize cannot be used for bit operation
    #[error("no bit opr for integer")]
    BitOperationOnlyWorksForRawBitsOrCustom,
    #[error("ExpectedNumTypeForIncrOrDecr")]
    ExpectedNumTypeForIncrOrDecr,
    #[error("ClosureParameterTypeNotInferred")]
    ClosureParameterTypeNotInferred,
}

impl OriginalError for OriginalSemExprTypeError {
    type Error = SemExprTypeError;
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Error, PartialEq, Eq)]
pub enum DerivedSemExprTypeError {
    #[error("field type error {0}")]
    FieldTypeTermError(EthTermError),
    #[error("type method type error {0}")]
    TypeMethodTypeError(EthTermError),
    #[error("type call type error {0}")]
    TypeCallTypeError(EthTermError),
    #[error("type info error")]
    TypeInfoError,
    #[error("expr error")]
    SynExprError,
    #[error("item type error")]
    EntityTypeError,
    #[error("boxList application first argument error")]
    BoxListApplicationFirstArgumentError,
    #[error("application or Ritchie call function type not inferred")]
    ApplicationOrRitchieCallFunctionTypeNotInferred,
    #[error("application argument type not inferred")]
    ApplicationArgumentTypeNotInferred,
    #[error("prefix operand type not inferred")]
    PrefixOperandTypeNotInferred,
    #[error("binary opn left operand type not inferred")]
    BinaryOperationLeftOperandTypeNotInferred,
    #[error("binary operation right operand type not inferred")]
    BinaryOperationRightOperandTypeNotInferred,
    #[error("field owner type not inferred")]
    FieldOwnerTypeNotInferred,
    #[error("method owner type not inferred")]
    MethodOwnerTypeNotInferred,
    #[error("block type error")]
    BlockTypeError,
    #[error("term symbol type error")]
    TermSymbolTypeError,
    #[error("type error {0}")]
    TypeError(#[from] EthTermError),
    #[error("bracketed item type error")]
    DelimiteredItemTypeError,
    #[error("current symbol type error")]
    CurrentVariableTypeError,
    #[error("inherited symbol type error")]
    InheritedVariableTypeError,
    #[error("callable type error")]
    CallableTypeError,
    #[error("function type not inferred in application or function call")]
    FunctionTypeNotInferredInApplicationOrFunctionCall,
    #[error("as operation right operand term not inferred")]
    CastAsOperationRightOperandTermNotInferred,
    #[error("return type not given in ritchie call")]
    ReturnTypeNotGivenInRitchieCall,
    #[error("self type not inferred")]
    SelfTypeNotInferred,
    #[error("self type not inferred for self value")]
    SelfTypeNotInferredForSelfValue,
    #[error("unresolved local term")]
    UnresolvedLocalTerm,
    #[error("item path error")]
    EntityPathError,
    #[error("final destination")]
    FinalDestination,
    #[error("cannot disambiguate list expression")]
    AmbiguateListExpr,
    #[error("form path type error {0}")]
    FormPathTypeError(EthTermError),
    #[error("ambiguous type path")]
    AmbiguousTypePath,
    #[error("explicit application function type not inferred")]
    ExplicitApplicationFunctionTypeNotInferred,
    #[error("AmbiguousTildeExpr")]
    AmbiguousTildeExpr,
    #[error("IntegerLiteralExpectationTypePathRefine")]
    IntegerLiteralExpectationTypePathRefine(EntityPathError),
    #[error("BitNotOperandTypeNotInferred")]
    BitNotOperandTypeNotInferred,
    #[error("BinaryShiftRightOperandTypeNotInferred")]
    BinaryShiftRightOperandTypeNotInferred,
    #[error("Fly term error")]
    FlyTermError(#[from] FlyTermError),
    #[error("SuffixOperandTypeNotInferred")]
    SuffixOperandTypeNotInferred,
    #[error("UnableToInferSuffixOperandType")]
    UnableToInferSuffixOperandType,
    #[error("UnableToInferFunctionApplicationArgumentType")]
    UnableToInferFunctionApplicationArgumentType,
    #[error("UnableToInferAssocItemParentTerm")]
    UnableToInferAssocItemParentTerm,
    #[error("UnableToInferArgumentTermForDependentType")]
    UnableToInferArgumentTermForDependentType,
    #[error("UnableToInferReturnTypeForUnveiling")]
    UnableToInferReturnTypeForUnveiling,
    #[error("EthSignature")]
    EthSignature(#[from] EthSignatureError),
    #[error("UnveilerError")]
    UnveilerError,
    #[error("UnableToInferUnwrapOperand")]
    UnableToInferUnwrapOperand,
    #[error("EvalExprTypeNotInferred")]
    EvalExprTypeNotInferred,
    #[error("BranchTypeMerge")]
    BranchTypeMerge,
    #[error("SynPatternError")]
    SynPatternError,
    #[error("ClosureReturnTypeNotInferred")]
    ClosureReturnTypeNotInferred,
}

pub type SemExprTypeResult<T> = Result<T, SemExprTypeError>;
pub type SemExprTypeResultRef<'a, T> = Result<T, &'a SemExprTypeError>;

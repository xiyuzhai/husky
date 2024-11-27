use crate::*;
use husky_entity_kind::EntityKind;
use husky_entity_path::{
    path::{EntityPath, PrincipalEntityPath},
    region::RegionPath,
};
use husky_entity_tree::{
    expr::r#use::UseExprIdx,
    node::ItemSynNodePath,
    presheet::{OnceUseRuleIdx, UseOneRuleState},
    region_path::SynNodeRegionPath,
};
use husky_regional_token::RegionalTokenIdx;
use husky_sem_expr::SemExprIdx;
use husky_syn_expr::{
    entity_path::SynPrincipalEntityPathExprIdx,
    pattern::SynPatternIdx,
    region::SynExprRegion,
    variable::{
        CurrentVariableIdx, CurrentVariableKind, InheritedVariableIdx, InheritedVariableKind,
    },
};
#[cfg(feature = "protocol_support")]
use husky_token_protocol::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct TokenInfo {
    regional_token_idx: Option<RegionalTokenIdx>,
    source: TokenInfoSource,
    data: TokenInfoData,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[enum_class::from_variants]
pub enum TokenInfoSource {
    UseExpr(UseExprIdx),
    SemExpr(RegionPath, SemExprIdx),
    SynPrincipalEntityPathExpr(SynPrincipalEntityPathExprIdx, PrincipalEntityPath),
    Pattern(RegionPath, SynPatternIdx),
    // todo: add #[skip] attribute
    TemplateParameter(CurrentVariableIdx),
    AstIdentifiable,
}

impl TokenInfo {
    pub fn new(
        regional_token_idx: Option<RegionalTokenIdx>,
        source: impl Into<TokenInfoSource>,
        data: TokenInfoData,
    ) -> Self {
        Self {
            regional_token_idx,
            source: source.into(),
            data,
        }
    }

    pub fn regional_token_idx(&self) -> Option<RegionalTokenIdx> {
        self.regional_token_idx
    }

    pub fn source(&self) -> TokenInfoSource {
        self.source
    }

    pub fn data(&self) -> &TokenInfoData {
        &self.data
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum TokenInfoData {
    Entity(EntityPath),
    EntityNode(ItemSynNodePath, EntityKind),
    InheritedVariable {
        inherited_variable_idx: InheritedVariableIdx,
        inherited_variable_kind: InheritedVariableKind,
        syn_expr_region: ExprRegionLeash,
    },
    CurrentVariable {
        current_variable_idx: CurrentVariableIdx,
        current_variable_kind: CurrentVariableKind,
        syn_expr_region: ExprRegionLeash,
    },
    SelfType,
    SelfValue,
    Field,
    Method,
    BoxColon,
    VecFunctorBoxPrefix,
    ArrayFunctorBoxPrefix,
    UseExprStar,
    UseExpr {
        use_expr_idx: UseExprIdx,
        rule_idx: OnceUseRuleIdx,
        state: UseOneRuleState,
    },
    HtmlFunctionIdent,
    HtmlPropertyIdent,
    UnitLeftParenthesis,
    UnitRightParenthesis,
    Todo,
    Unreachable,
    PrefixArithOpr,
    PrefixTypeOpr,
    BinaryOpr,
    CallPar,
    NestedBlockCurl,
    ClosureVert,
    ClosureLightArrow,
    ClosureEq,
    Literal,
    IndexColon,
    UnwrapExclamation,
    BeKeyword,
    NewListLbox,
    NewListRbox,
    DelimiterLpar,
    DelimiterRpar,
    TupleLpar,
    TupleRpar,
    UnveilOpr,
    SuffixOpr,
}

#[cfg(feature = "protocol_support")]
impl TokenInfoData {
    pub fn token_class(&self, db: &::salsa::Db) -> TokenClass {
        match self {
            TokenInfoData::Entity(path) => path.item_kind(db).class().into(),
            TokenInfoData::EntityNode(_path, item_kind) => item_kind.class().into(),
            TokenInfoData::CurrentVariable {
                current_variable_kind,
                ..
            } => match current_variable_kind {
                CurrentVariableKind::LetVariable { .. }
                | CurrentVariableKind::BeVariable { .. }
                | CurrentVariableKind::CaseVariable { .. } => TokenClass::Variable,
                CurrentVariableKind::SimpleParenateParameter { .. }
                | CurrentVariableKind::VariadicParenateParameter { .. }
                | CurrentVariableKind::SimpleClosureParameter { .. } => TokenClass::Parameter,
                CurrentVariableKind::LoopVariable(_) => TokenClass::LoopVariable,
                CurrentVariableKind::TemplateParameter { .. } => TokenClass::ImplicitParameter,
                CurrentVariableKind::FieldVariable { .. } => TokenClass::Variable,
            },
            // TokenProtocol::Variable,
            TokenInfoData::InheritedVariable {
                inherited_variable_kind,
                ..
            } => match inherited_variable_kind {
                InheritedVariableKind::Parenate { .. } => TokenClass::Parameter,
                InheritedVariableKind::Template { .. } => TokenClass::ImplicitParameter,
                InheritedVariableKind::SelfField { .. } => TokenClass::Variable,
                InheritedVariableKind::ReplLocal => TokenClass::Variable,
            },
            TokenInfoData::SelfType => TokenClass::SelfType,
            TokenInfoData::SelfValue => TokenClass::SelfValue,
            // TokenProtocol::Variable,
            TokenInfoData::Field => TokenClass::Field,
            TokenInfoData::Method => TokenClass::Method,
            TokenInfoData::BoxColon
            | TokenInfoData::VecFunctorBoxPrefix
            | TokenInfoData::ArrayFunctorBoxPrefix => TokenClass::TypeEntity,
            TokenInfoData::UseExpr { state, .. } => match state {
                UseOneRuleState::Resolved {
                    original_symbol: Some(original_symbol),
                } => original_symbol
                    .principal_entity_path(db)
                    .item_kind(db)
                    .class()
                    .into(),
                UseOneRuleState::Resolved {
                    original_symbol: None,
                } => todo!(),
                UseOneRuleState::Unresolved => todo!(),
                UseOneRuleState::Erroneous => TokenClass::Error,
            },
            TokenInfoData::UseExprStar => TokenClass::Punctuation,
            TokenInfoData::HtmlFunctionIdent => TokenClass::HtmlFunctionIdent,
            TokenInfoData::HtmlPropertyIdent => TokenClass::HtmlPropertyIdent,
            TokenInfoData::UnitLeftParenthesis | TokenInfoData::UnitRightParenthesis => {
                TokenClass::TypeEntity
            }
            TokenInfoData::Todo => TokenClass::Todo,
            TokenInfoData::Unreachable => TokenClass::Unreachable,
            TokenInfoData::PrefixTypeOpr => TokenClass::TypeEntity,
            TokenInfoData::CallPar => TokenClass::Punctuation,
            TokenInfoData::NestedBlockCurl => TokenClass::Punctuation,
            TokenInfoData::ClosureVert => TokenClass::Punctuation,
            TokenInfoData::ClosureLightArrow => TokenClass::Punctuation,
            TokenInfoData::ClosureEq => TokenClass::Punctuation,
            TokenInfoData::Literal => TokenClass::Literal,
            TokenInfoData::IndexColon => TokenClass::Punctuation,
            TokenInfoData::UnwrapExclamation => TokenClass::Punctuation,
            TokenInfoData::PrefixArithOpr => TokenClass::Punctuation,
            TokenInfoData::BinaryOpr => TokenClass::Punctuation,
            TokenInfoData::BeKeyword => TokenClass::OtherKeyword,
            TokenInfoData::NewListLbox => TokenClass::Punctuation,
            TokenInfoData::NewListRbox => TokenClass::Punctuation,
            TokenInfoData::DelimiterLpar => TokenClass::Punctuation,
            TokenInfoData::DelimiterRpar => TokenClass::Punctuation,
            TokenInfoData::TupleLpar => TokenClass::Punctuation,
            TokenInfoData::TupleRpar => TokenClass::Punctuation,
            TokenInfoData::UnveilOpr => TokenClass::Punctuation, // Changed from Operator
            TokenInfoData::SuffixOpr => TokenClass::Punctuation, // Changed from Operator
        }
    }
}

/// the purpose is to avoid extra debug with db in expr region
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ExprRegionLeash(SynExprRegion);

impl From<SynExprRegion> for ExprRegionLeash {
    fn from(value: SynExprRegion) -> Self {
        ExprRegionLeash(value)
    }
}
impl From<ExprRegionLeash> for SynExprRegion {
    fn from(value: ExprRegionLeash) -> Self {
        value.0
    }
}

impl std::ops::Deref for ExprRegionLeash {
    type Target = SynExprRegion;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::fmt::Debug for ExprRegionLeash {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("ExprRegionLeash(_)")
    }
}

impl salsa::DebugWithDb for ExprRegionLeash {
    fn debug_fmt_with_db(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        _db: &::salsa::Db,
    ) -> std::fmt::Result {
        f.write_str("ExprRegionLeash(_)")
    }
}

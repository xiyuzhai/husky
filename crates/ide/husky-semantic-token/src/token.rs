use crate::*;

use husky_text_protocol::range::TextPositionRange;
use husky_token_protocol::TokenClass;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SemanticToken {
    pub token_class: TokenClass,
    pub range: TextPositionRange,
}

impl PartialOrd for SemanticToken {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.range.start.partial_cmp(&other.range.start)
    }
}

impl SemanticToken {
    pub fn new(token_protocol: TokenClass, range: TextPositionRange) -> Self {
        Self {
            token_class: token_protocol,
            range,
        }
    }
}

impl SemanticToken {
    #[inline(always)]
    pub fn token_type(self) -> u32 {
        get_type_index(match self.token_class {
            TokenClass::ControlFlowKeyword | TokenClass::OtherKeyword => {
                ext::SemanticTokenType::KEYWORD
            }
            TokenClass::Comment => ext::SemanticTokenType::COMMENT,
            TokenClass::Field => ext::SemanticTokenType::PROPERTY,
            TokenClass::Punctuation => ext::SemanticTokenType::OPERATOR,
            TokenClass::Variable => ext::SemanticTokenType::VARIABLE,
            TokenClass::LoopVariable => ext::SemanticTokenType::VARIABLE,
            TokenClass::ModuleEntity => ext::SemanticTokenType::NAMESPACE,
            TokenClass::TypeEntity => ext::SemanticTokenType::TYPE,
            TokenClass::TypeAlias => ext::SemanticTokenType::TYPE,
            TokenClass::TypeVar => ext::SemanticTokenType::TYPE,
            TokenClass::ValEntity => ext::SemanticTokenType::VARIABLE,
            TokenClass::FunctionEntity => ext::SemanticTokenType::FUNCTION,
            TokenClass::TraitEntity => ext::SemanticTokenType::CLASS,
            TokenClass::MethodEntity => ext::SemanticTokenType::METHOD,
            TokenClass::MemoizedFieldEntity => ext::SemanticTokenType::PROPERTY,
            TokenClass::TypeVariantEntity => ext::SemanticTokenType::ENUM_MEMBER,
            TokenClass::ImplicitParameter => ext::SemanticTokenType::TYPE_PARAMETER,
            TokenClass::Parameter => ext::SemanticTokenType::PARAMETER,
            TokenClass::Method => ext::SemanticTokenType::METHOD,
            TokenClass::Literal => ext::SemanticTokenType::NUMBER,
            TokenClass::HtmlTagKind => ext::SemanticTokenType::FUNCTION,
            TokenClass::Attribute => ext::SemanticTokenType::DECORATOR,
            TokenClass::WordOpr => ext::SemanticTokenType::KEYWORD,
            TokenClass::SelfType => ext::SemanticTokenType::TYPE,
            TokenClass::SelfValue => ext::SemanticTokenType::KEYWORD,
            TokenClass::HtmlFunctionIdent => ext::SemanticTokenType::FUNCTION,
            TokenClass::HtmlPropertyIdent => ext::SemanticTokenType::PROPERTY,
            TokenClass::Todo => ext::SemanticTokenType::MACRO,
            TokenClass::Unreachable => ext::SemanticTokenType::MACRO,
            TokenClass::Ident => ext::SemanticTokenType::VARIABLE,
            TokenClass::Label => ext::SemanticTokenType::VARIABLE,
            TokenClass::Error => ext::SemanticTokenType::MACRO,
            TokenClass::DefEntity => ext::SemanticTokenType::VARIABLE,
            TokenClass::StaticMutEntity => ext::SemanticTokenType::VARIABLE,
            TokenClass::StaticVarEntity => ext::SemanticTokenType::VARIABLE,
            TokenClass::TermicEntity => todo!(),
        })
    }

    #[inline(always)]
    pub fn token_modifiers_bitset(self) -> u32 {
        let mut result = ModifierSet(0);
        match self.token_class {
            TokenClass::ControlFlowKeyword => result |= CONTROL_FLOW,
            _ => (),
        }
        result.0
    }
}

#[derive(Default)]
pub(crate) struct ModifierSet(pub(crate) u32);

impl std::ops::BitOrAssign<ext::SemanticTokenModifier> for ModifierSet {
    fn bitor_assign(&mut self, rhs: ext::SemanticTokenModifier) {
        let idx = SUPPORTED_MODIFIERS
            .iter()
            .position(|it| it == &rhs)
            .unwrap();
        self.0 |= 1 << idx;
    }
}

pub(crate) fn get_type_index(ty: ext::SemanticTokenType) -> u32 {
    SUPPORTED_TYPES.iter().position(|it| *it == ty).unwrap() as u32
}

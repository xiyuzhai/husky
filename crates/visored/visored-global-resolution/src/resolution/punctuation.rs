use latex_math_punctuation::{LxMathPunctuation, LxMathPunctuationMap};
use visored_opr::{
    delimiter::{VdBaseLeftDelimiter, VdBaseRightDelimiter},
    opr::{binary::VdBaseBinaryOpr, prefix::VdBasePrefixOpr, VdBaseOpr},
    separator::VdBaseSeparator,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdPunctuationGlobalResolution {
    Opr(VdBaseOpr),
    Separator(VdBaseSeparator),
    LeftDelimiter(VdBaseLeftDelimiter),
    RightDelimiter(VdBaseRightDelimiter),
    PrefixOrBinaryOpr(VdBasePrefixOpr, VdBaseBinaryOpr),
    PrefixOprOrSeparator(VdBasePrefixOpr, VdBaseSeparator),
    Todo,
}

pub type VdPunctuationGlobalResolutionMap =
    LxMathPunctuationMap<Option<VdPunctuationGlobalResolution>>;

impl VdPunctuationGlobalResolution {
    pub const ADD: Self = Self::PrefixOprOrSeparator(VdBasePrefixOpr::POS, VdBaseSeparator::ADD);
    pub const SUB: Self = Self::PrefixOrBinaryOpr(VdBasePrefixOpr::NEG, VdBaseBinaryOpr::SUB);
    pub const SEPARATOR_MUL: Self = Self::Separator(VdBaseSeparator::MUL);
    pub const DIV: Self = Self::Opr(VdBaseOpr::DIV);
    pub const EQ: Self = Self::Separator(VdBaseSeparator::EQ);
    pub const NE: Self = Self::Separator(VdBaseSeparator::NE);
    pub const LT: Self = Self::Separator(VdBaseSeparator::LT);
    pub const GT: Self = Self::Separator(VdBaseSeparator::GT);
    pub const LE: Self = Self::Separator(VdBaseSeparator::LE);
    pub const GE: Self = Self::Separator(VdBaseSeparator::GE);
    pub const LPAR: Self = Self::LeftDelimiter(VdBaseLeftDelimiter::LPAR);
    pub const RPAR: Self = Self::RightDelimiter(VdBaseRightDelimiter::RPAR);
}

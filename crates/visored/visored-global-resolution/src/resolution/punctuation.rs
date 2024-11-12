use latex_math_punctuation::{LxMathPunctuation, LxMathPunctuationMap};
use visored_opr::{
    delimiter::{VdBaseLeftDelimiter, VdBaseRightDelimiter},
    opr::VdBaseOpr,
    separator::VdBaseSeparator,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdPunctuationGlobalResolution {
    Opr(VdBaseOpr),
    Separator(VdBaseSeparator),
    LeftDelimiter(VdBaseLeftDelimiter),
    RightDelimiter(VdBaseRightDelimiter),
    Todo,
}

pub type VdPunctuationGlobalResolutionMap =
    LxMathPunctuationMap<Option<VdPunctuationGlobalResolution>>;

impl VdPunctuationGlobalResolution {
    pub const SEPARATOR_ADD: Self = Self::Separator(VdBaseSeparator::ADD);
    pub const SUB: Self = Self::Opr(VdBaseOpr::SUB);
    pub const SEPARATOR_MUL: Self = Self::Separator(VdBaseSeparator::MUL);
    pub const DIV: Self = Self::Opr(VdBaseOpr::DIV);
    pub const EQ: Self = Self::Separator(VdBaseSeparator::EQ);
    pub const LPAR: Self = Self::LeftDelimiter(VdBaseLeftDelimiter::LPAR);
    pub const RPAR: Self = Self::RightDelimiter(VdBaseRightDelimiter::RPAR);
}

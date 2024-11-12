use super::*;
use latex_command::path::LxCommandPath;
use latex_math_letter::letter::LxMathLetter;
use rustc_hash::FxHashMap;
use visored_item_path::path::VdItemPath;
use visored_opr::{opr::VdBaseOpr, separator::VdBaseSeparator};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdCompleteCommandGlobalResolution {
    Letter(LxMathLetter),
    Item(VdItemPath),
    Opr(VdBaseOpr),
    Separator(VdBaseSeparator),
    Frac,
    Sqrt,
    Text,
    Todo,
}

pub type VdCompleteCommandGlobalResolutionMap =
    FxHashMap<LxCommandPath, VdCompleteCommandGlobalResolution>;

impl VdCompleteCommandGlobalResolution {
    // - operators
    // -- relations
    pub const EQ: Self = Self::Separator(VdBaseSeparator::Eq);
    pub const NE: Self = Self::Separator(VdBaseSeparator::Ne);
    pub const IN: Self = Self::Separator(VdBaseSeparator::In);
    pub const SUBSET: Self = Self::Separator(VdBaseSeparator::Subset);
    pub const SUPSET: Self = Self::Separator(VdBaseSeparator::Supset);
    pub const SUBSETEQ: Self = Self::Separator(VdBaseSeparator::Subseteq);
    pub const SUPSETEQ: Self = Self::Separator(VdBaseSeparator::Supseteq);
    pub const SUBSETEQQ: Self = Self::Separator(VdBaseSeparator::Subseteqq);
    pub const SUPSETEQQ: Self = Self::Separator(VdBaseSeparator::Supseteqq);
    pub const SUBSETNEQ: Self = Self::Separator(VdBaseSeparator::Subsetneq);
    pub const SUPSETNEQ: Self = Self::Separator(VdBaseSeparator::Supsetneq);
    // -- arithmetic
    pub const INT: Self = Self::Opr(VdBaseOpr::INTEGRAL);
    pub const SUM: Self = Self::Opr(VdBaseOpr::SUM);
    pub const PROD: Self = Self::Opr(VdBaseOpr::PROD);
    pub const TIMES: Self = Self::Opr(VdBaseOpr::TIMES);
    pub const OTIMES: Self = Self::Opr(VdBaseOpr::OTIMES);
    pub const LOWER_ALPHA: Self = Self::Letter(LxMathLetter::LOWER_ALPHA);
    pub const LOWER_BETA: Self = Self::Letter(LxMathLetter::LOWER_BETA);
    pub const LOWER_GAMMA: Self = Self::Letter(LxMathLetter::LOWER_GAMMA);
    pub const LOWER_PI: Self = Self::Letter(LxMathLetter::LOWER_PI);
}

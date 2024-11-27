use super::*;
use latex_command::path::LxCommandPath;
use latex_math_letter::letter::LxMathLetter;
use rustc_hash::FxHashMap;
use visored_entity_path::path::VdItemPath;
use visored_opr::{opr::VdBaseOpr, separator::VdBaseSeparator};
use visored_prelude::division::VdDivisionLevel;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdCompleteCommandGlobalResolution {
    Letter(LxMathLetter),
    Item(VdItemPath),
    Opr(VdBaseOpr),
    Separator(VdBaseSeparator),
    NewDivision(VdDivisionLevel),
    Frac,
    Sqrt,
    Text,
    UsePackage,
    DocumentClass,
    Todo,
}

pub type VdCompleteCommandGlobalResolutionMap =
    FxHashMap<LxCommandPath, VdCompleteCommandGlobalResolution>;

impl VdCompleteCommandGlobalResolution {
    // - root
    pub const USEPACKAGE: Self = VdCompleteCommandGlobalResolution::UsePackage;
    pub const DOCUMENTCLASS: Self = VdCompleteCommandGlobalResolution::DocumentClass;
    pub const PART: Self = VdCompleteCommandGlobalResolution::NewDivision(VdDivisionLevel::Part);
    pub const CHAPTER: Self =
        VdCompleteCommandGlobalResolution::NewDivision(VdDivisionLevel::Chapter);
    pub const SECTION: Self =
        VdCompleteCommandGlobalResolution::NewDivision(VdDivisionLevel::Section);
    pub const SUBSECTION: Self =
        VdCompleteCommandGlobalResolution::NewDivision(VdDivisionLevel::Subsection);
    pub const SUBSUBSECTION: Self =
        VdCompleteCommandGlobalResolution::NewDivision(VdDivisionLevel::Subsubsection);
    // - operators
    // -- relations
    pub const EQ: Self = VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Eq);
    pub const NE: Self = VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Ne);
    pub const LE: Self = VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Le);
    pub const GE: Self = VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Ge);
    pub const IN: Self = VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::In);
    pub const SUBSET: Self = VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Subset);
    pub const SUPSET: Self = VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Supset);
    pub const SUBSETEQ: Self =
        VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Subseteq);
    pub const SUPSETEQ: Self =
        VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Supseteq);
    pub const SUBSETEQQ: Self =
        VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Subseteqq);
    pub const SUPSETEQQ: Self =
        VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Supseteqq);
    pub const SUBSETNEQ: Self =
        VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Subsetneq);
    pub const SUPSETNEQ: Self =
        VdCompleteCommandGlobalResolution::Separator(VdBaseSeparator::Supsetneq);
    // -- arithmetic
    pub const INT: Self = VdCompleteCommandGlobalResolution::Opr(VdBaseOpr::INTEGRAL);
    pub const SUM: Self = VdCompleteCommandGlobalResolution::Opr(VdBaseOpr::SUM);
    pub const PROD: Self = VdCompleteCommandGlobalResolution::Opr(VdBaseOpr::PROD);
    pub const LOWER_ALPHA: Self =
        VdCompleteCommandGlobalResolution::Letter(LxMathLetter::LOWER_ALPHA);
    pub const LOWER_BETA: Self =
        VdCompleteCommandGlobalResolution::Letter(LxMathLetter::LOWER_BETA);
    pub const LOWER_GAMMA: Self =
        VdCompleteCommandGlobalResolution::Letter(LxMathLetter::LOWER_GAMMA);
    pub const LOWER_PI: Self = VdCompleteCommandGlobalResolution::Letter(LxMathLetter::LOWER_PI);
}

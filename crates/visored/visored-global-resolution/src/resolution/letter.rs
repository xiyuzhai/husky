use latex_math_letter::letter::LxMathLetter;
use rustc_hash::FxHashMap;
use visored_item_path::path::VdItemPath;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdLetterGlobalResolution {
    Item(VdItemPath),
}

pub type VdLetterGlobalResolutionMap = FxHashMap<LxMathLetter, VdLetterGlobalResolution>;

impl VdLetterGlobalResolution {
    pub const NATURAL_NUMBER: Self = Self::Item(VdItemPath::NAT);
    pub const RATIONAL_NUMBER: Self = Self::Item(VdItemPath::RAT);
    pub const INTEGER: Self = Self::Item(VdItemPath::INT);
    pub const REAL_NUMBER: Self = Self::Item(VdItemPath::REAL);
    pub const COMPLEX_NUMBER: Self = Self::Item(VdItemPath::COMPLEX);
}

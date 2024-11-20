pub mod binary;
pub mod prefix;
pub mod suffix;

use self::{
    binary::{VdBaseBinaryOpr, VdCompositeBinaryOpr},
    prefix::{VdBasePrefixOpr, VdCompositePrefixOpr},
    suffix::{VdBaseSuffixOpr, VdCompositeSuffixOpr},
};

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum VdBaseOpr {
    Prefix(VdBasePrefixOpr),
    Suffix(VdBaseSuffixOpr),
    Binary(VdBaseBinaryOpr),
}

impl VdBaseOpr {
    pub const INTEGRAL: Self = Self::Prefix(VdBasePrefixOpr::INTEGRAL);
    pub const DIFFERENTIAL: Self = Self::Prefix(VdBasePrefixOpr::DIFFERENTIAL);
    pub const SUM: Self = Self::Prefix(VdBasePrefixOpr::SUM);
    pub const PROD: Self = Self::Prefix(VdBasePrefixOpr::PROD);

    pub const TIMES: Self = Self::Binary(VdBaseBinaryOpr::TIMES);
    pub const OTIMES: Self = Self::Binary(VdBaseBinaryOpr::OTIMES);

    pub const SUB: Self = Self::Binary(VdBaseBinaryOpr::SUB);
    pub const DIV: Self = Self::Binary(VdBaseBinaryOpr::DIV);
}

impl VdBaseOpr {
    pub fn latex_code(self) -> &'static str {
        match self {
            VdBaseOpr::Prefix(opr) => opr.latex_code(),
            VdBaseOpr::Suffix(opr) => opr.latex_code(),
            VdBaseOpr::Binary(opr) => opr.latex_code(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum VdCompositeOpr {
    Prefix(VdCompositePrefixOpr),
    Suffix(VdCompositeSuffixOpr),
    Binary(VdCompositeBinaryOpr),
}

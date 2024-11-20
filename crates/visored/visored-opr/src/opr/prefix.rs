use crate::precedence::{VdPrecedence, VdPrecedenceRange};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum VdBasePrefixOpr {
    Pos,
    Neg,
    Integral,
    Differential,
    Sum,
    Prod,
}

impl VdBasePrefixOpr {
    pub const POS: Self = Self::Pos;
    pub const NEG: Self = Self::Neg;
    pub const INTEGRAL: Self = Self::Integral;
    pub const DIFFERENTIAL: Self = Self::Differential;
    pub const SUM: Self = Self::Sum;
    pub const PROD: Self = Self::Prod;

    pub fn precedence(self) -> VdPrecedence {
        match self {
            VdBasePrefixOpr::Pos | VdBasePrefixOpr::Neg => VdPrecedence::SIGN,
            VdBasePrefixOpr::Integral => VdPrecedence::REDUCE_PREFIX,
            VdBasePrefixOpr::Differential => VdPrecedence::DIFFERENTIAL,
            VdBasePrefixOpr::Sum => todo!(),
            VdBasePrefixOpr::Prod => todo!(),
        }
    }
}

impl VdBasePrefixOpr {
    pub fn latex_code(self) -> &'static str {
        todo!()
    }

    pub fn precedence_range(self) -> VdPrecedenceRange {
        todo!()
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum VdCompositePrefixOpr {
    /// `d/dx`
    Differential,
}

impl VdCompositePrefixOpr {
    pub fn latex_code(self) -> &'static str {
        todo!()
    }

    pub fn precedence(self) -> VdPrecedence {
        todo!()
    }
}

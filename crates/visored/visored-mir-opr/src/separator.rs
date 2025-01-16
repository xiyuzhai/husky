pub mod chaining;
pub mod folding;

use self::{chaining::*, folding::*};
use visored_opr::{
    precedence::{VdPrecedence, VdPrecedenceRange},
    separator::VdSeparatorClass,
};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseSeparator {
    Chaining(VdMirBaseChainingSeparator),
    Folding(VdMirBaseFoldingSeparator),
}

impl VdMirBaseSeparator {
    pub const COMM_RING_ADD: Self =
        VdMirBaseSeparator::Folding(VdMirBaseFoldingSeparator::COMM_RING_ADD);
    pub const COMM_RING_MUL: Self =
        VdMirBaseSeparator::Folding(VdMirBaseFoldingSeparator::COMM_RING_MUL);
    pub const IFF: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::IFF);
    pub const EQ: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::EQ);
    pub const NE: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::NE);
    pub const LT: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::LT);
    pub const GT: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::GT);
    pub const LE: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::LE);
    pub const GE: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::GE);
    pub const SUBSET: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::SUBSET);
    pub const SUPSET: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::SUPSET);
    pub const SUBSETEQ: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::SUBSETEQ);
    pub const SUPSETEQ: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::SUPSETEQ);
    pub const SUBSETEQQ: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::SUBSETEQQ);
    pub const SUPSETEQQ: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::SUPSETEQQ);
    pub const SUBSETNEQ: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::SUBSETNEQ);
    pub const SUPSETNEQ: Self = VdMirBaseSeparator::Chaining(VdMirBaseChainingSeparator::SUPSETNEQ);
}

impl VdMirBaseSeparator {
    pub fn precedence(self) -> VdPrecedence {
        self.class().precedence()
    }

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        self.class().left_precedence_range()
    }

    pub fn right_precedence_range(self) -> VdPrecedenceRange {
        self.class().right_precedence_range()
    }

    pub fn class(self) -> VdSeparatorClass {
        match self {
            VdMirBaseSeparator::Folding(slf) => slf.class(),
            VdMirBaseSeparator::Chaining(slf) => slf.class(),
        }
    }

    pub fn is_equivalence(self) -> bool {
        match self {
            VdMirBaseSeparator::Chaining(slf) => slf.is_equivalence(),
            _ => false,
        }
    }
}

impl VdMirBaseSeparator {
    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBaseSeparator::Folding(slf) => slf.unicode(),
            VdMirBaseSeparator::Chaining(slf) => slf.unicode(),
        }
    }

    pub fn show_fmt(self, f: &mut impl std::fmt::Write) -> std::fmt::Result {
        f.write_str(self.unicode())
    }
}

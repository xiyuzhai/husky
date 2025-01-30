use visored_opr::{precedence::VdPrecedence, separator::VdSeparatorClass};

#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBasePrefixOpr {
    RingPos,
    RingNeg,
}

impl VdMirBasePrefixOpr {
    pub const RING_POS: Self = VdMirBasePrefixOpr::RingPos;
    pub const RING_NEG: Self = VdMirBasePrefixOpr::RingNeg;
}

impl VdMirBasePrefixOpr {
    pub fn precedence(self) -> VdPrecedence {
        match self {
            VdMirBasePrefixOpr::RING_POS | VdMirBasePrefixOpr::RING_NEG => VdPrecedence::SIGN,
            _ => todo!(),
        }
    }

    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBasePrefixOpr::RING_POS => "+",
            VdMirBasePrefixOpr::RING_NEG => "-",
        }
    }

    pub fn code(self) -> &'static str {
        match self {
            VdMirBasePrefixOpr::RING_POS => "pos",
            VdMirBasePrefixOpr::RING_NEG => "neg",
        }
    }
}

impl std::fmt::Display for VdMirBasePrefixOpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.unicode())
    }
}

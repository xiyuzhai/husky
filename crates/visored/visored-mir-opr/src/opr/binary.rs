use visored_opr::{
    precedence::{VdPrecedence, VdPrecedenceRange},
    separator::VdSeparatorClass,
};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseBinaryOpr {
    CommRingSub,
    CommFieldDiv,
}

impl VdMirBaseBinaryOpr {
    pub const COMM_RING_SUB: Self = VdMirBaseBinaryOpr::CommRingSub;
    pub const COMM_FIELD_DIV: Self = VdMirBaseBinaryOpr::CommFieldDiv;
}

impl VdMirBaseBinaryOpr {
    pub fn precedence(self) -> VdPrecedence {
        match self {
            VdMirBaseBinaryOpr::CommRingSub => VdPrecedence::ADD_SUB,
            VdMirBaseBinaryOpr::CommFieldDiv => VdPrecedence::MUL_DIV,
        }
    }

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        match self {
            VdMirBaseBinaryOpr::CommRingSub => VdPrecedenceRange::ADD_SUB_LEFT,
            VdMirBaseBinaryOpr::CommFieldDiv => VdPrecedenceRange::MUL_DIV_LEFT,
        }
    }

    pub fn right_precedence_range(self) -> VdPrecedenceRange {
        match self {
            VdMirBaseBinaryOpr::CommRingSub => VdPrecedenceRange::ADD_SUB_RIGHT,
            VdMirBaseBinaryOpr::CommFieldDiv => VdPrecedenceRange::MUL_DIV_RIGHT,
        }
    }

    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBaseBinaryOpr::CommRingSub => "-",
            VdMirBaseBinaryOpr::CommFieldDiv => "/",
        }
    }
}

impl std::fmt::Display for VdMirBaseBinaryOpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.unicode())
    }
}

use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseFoldingSeparator {
    CommRingAdd,
    CommRingMul,
    SetTimes,
    TensorOtimes,
}

impl std::fmt::Display for VdMirBaseFoldingSeparator {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.unicode())
    }
}

impl VdMirBaseFoldingSeparator {
    pub const COMM_RING_ADD: Self = VdMirBaseFoldingSeparator::CommRingAdd;
    pub const COMM_RING_MUL: Self = VdMirBaseFoldingSeparator::CommRingMul;
    pub const SET_TIMES: Self = VdMirBaseFoldingSeparator::SetTimes;
    pub const TENSOR_OTIMES: Self = VdMirBaseFoldingSeparator::TensorOtimes;
}

impl VdMirBaseFoldingSeparator {
    pub fn class(self) -> VdSeparatorClass {
        match self {
            VdMirBaseFoldingSeparator::CommRingAdd => VdSeparatorClass::Add,
            VdMirBaseFoldingSeparator::CommRingMul => VdSeparatorClass::Mul,
            VdMirBaseFoldingSeparator::SetTimes => VdSeparatorClass::Mul,
            VdMirBaseFoldingSeparator::TensorOtimes => VdSeparatorClass::Mul,
        }
    }

    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBaseFoldingSeparator::CommRingAdd => "+",
            VdMirBaseFoldingSeparator::CommRingMul => "*",
            VdMirBaseFoldingSeparator::SetTimes => "×",
            VdMirBaseFoldingSeparator::TensorOtimes => "⊗",
        }
    }

    pub fn outer_precedence(&self) -> VdPrecedence {
        self.class().precedence()
    }

    pub fn left_precedence_range(&self) -> VdPrecedenceRange {
        self.class().left_precedence_range()
    }

    pub fn right_precedence_range(&self) -> VdPrecedenceRange {
        self.class().right_precedence_range()
    }

    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.unicode())
    }
}

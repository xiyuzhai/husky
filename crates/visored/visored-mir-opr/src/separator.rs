use visored_opr::{
    precedence::{VdPrecedence, VdPrecedenceRange},
    separator::VdSeparatorClass,
};

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub enum VdMirBaseSeparator {
    Iff,
    CommRingAdd,
    CommRingMul,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    Subset,
    Supset,
    Subseteq,
    Supseteq,
    Subseteqq,
    Supseteqq,
    Subsetneq,
    Supsetneq,
    In,
    Notin,
    SetTimes,
    TensorOtimes,
}

impl VdMirBaseSeparator {
    pub const IFF: Self = VdMirBaseSeparator::Iff;
    pub const COMM_RING_ADD: Self = VdMirBaseSeparator::CommRingAdd;
    pub const COMM_RING_MUL: Self = VdMirBaseSeparator::CommRingMul;
    pub const EQ: Self = VdMirBaseSeparator::Eq;
    pub const NE: Self = VdMirBaseSeparator::Ne;
    pub const LT: Self = VdMirBaseSeparator::Lt;
    pub const GT: Self = VdMirBaseSeparator::Gt;
    pub const LE: Self = VdMirBaseSeparator::Le;
    pub const GE: Self = VdMirBaseSeparator::Ge;
    pub const SUBSET: Self = VdMirBaseSeparator::Subset;
    pub const SUPSET: Self = VdMirBaseSeparator::Supset;
    pub const SUBSETEQ: Self = VdMirBaseSeparator::Subseteq;
    pub const SUPSETEQ: Self = VdMirBaseSeparator::Supseteq;
    pub const SUBSETEQQ: Self = VdMirBaseSeparator::Subseteqq;
    pub const SUPSETEQQ: Self = VdMirBaseSeparator::Supseteqq;
    pub const SUBSETNEQ: Self = VdMirBaseSeparator::Subsetneq;
    pub const SUPSETNEQ: Self = VdMirBaseSeparator::Supsetneq;
}

impl VdMirBaseSeparator {
    pub fn precedence(self) -> VdPrecedence {
        match self {
            VdMirBaseSeparator::Iff => VdPrecedence::DEDUCTION,
            VdMirBaseSeparator::CommRingAdd => VdPrecedence::ADD_SUB,
            VdMirBaseSeparator::CommRingMul => VdPrecedence::MUL_DIV,
            VdMirBaseSeparator::SetTimes => VdPrecedence::MUL_DIV,
            VdMirBaseSeparator::TensorOtimes => VdPrecedence::MUL_DIV,
            VdMirBaseSeparator::Eq
            | VdMirBaseSeparator::Ne
            | VdMirBaseSeparator::Lt
            | VdMirBaseSeparator::Gt
            | VdMirBaseSeparator::Le
            | VdMirBaseSeparator::Ge
            | VdMirBaseSeparator::Subset
            | VdMirBaseSeparator::Supset
            | VdMirBaseSeparator::Subseteq
            | VdMirBaseSeparator::Supseteq
            | VdMirBaseSeparator::Subseteqq
            | VdMirBaseSeparator::Supseteqq
            | VdMirBaseSeparator::Subsetneq
            | VdMirBaseSeparator::Supsetneq
            | VdMirBaseSeparator::In
            | VdMirBaseSeparator::Notin => VdPrecedence::RELATION,
        }
    }

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        self.class().left_precedence_range()
    }

    pub fn right_precedence_range(self) -> VdPrecedenceRange {
        self.class().right_precedence_range()
    }

    pub fn class(self) -> VdSeparatorClass {
        match self {
            VdMirBaseSeparator::Iff => VdSeparatorClass::Deduction,
            VdMirBaseSeparator::CommRingAdd => VdSeparatorClass::Add,
            VdMirBaseSeparator::CommRingMul => VdSeparatorClass::Mul,
            VdMirBaseSeparator::SetTimes => VdSeparatorClass::Mul,
            VdMirBaseSeparator::TensorOtimes => VdSeparatorClass::Mul,
            VdMirBaseSeparator::Eq
            | VdMirBaseSeparator::Ne
            | VdMirBaseSeparator::Lt
            | VdMirBaseSeparator::Gt
            | VdMirBaseSeparator::Le
            | VdMirBaseSeparator::Ge
            | VdMirBaseSeparator::Subset
            | VdMirBaseSeparator::Supset
            | VdMirBaseSeparator::Subseteq
            | VdMirBaseSeparator::Supseteq
            | VdMirBaseSeparator::Subseteqq
            | VdMirBaseSeparator::Supseteqq
            | VdMirBaseSeparator::Subsetneq
            | VdMirBaseSeparator::Supsetneq
            | VdMirBaseSeparator::In
            | VdMirBaseSeparator::Notin => VdSeparatorClass::Relation,
        }
    }
}

impl VdMirBaseSeparator {
    pub fn unicode(self) -> &'static str {
        match self {
            VdMirBaseSeparator::Iff => "⟺",
            VdMirBaseSeparator::CommRingAdd => "+",
            VdMirBaseSeparator::CommRingMul => "*",
            VdMirBaseSeparator::Eq => "=",
            VdMirBaseSeparator::Ne => "≠",
            VdMirBaseSeparator::Lt => "<",
            VdMirBaseSeparator::Gt => ">",
            VdMirBaseSeparator::Le => "≤",
            VdMirBaseSeparator::Ge => "≥",
            VdMirBaseSeparator::Subset => "⊂",
            VdMirBaseSeparator::Supset => "⊃",
            VdMirBaseSeparator::Subseteq => "⊆",
            VdMirBaseSeparator::Supseteq => "⊇",
            VdMirBaseSeparator::Subseteqq => "⫅",
            VdMirBaseSeparator::Supseteqq => "⫆",
            VdMirBaseSeparator::Subsetneq => "⊊",
            VdMirBaseSeparator::Supsetneq => "⊋",
            VdMirBaseSeparator::In => "∈",
            VdMirBaseSeparator::Notin => "∉",
            VdMirBaseSeparator::SetTimes => "×",
            VdMirBaseSeparator::TensorOtimes => "⊗",
        }
    }

    pub fn show_fmt(self, f: &mut impl std::fmt::Write) -> std::fmt::Result {
        f.write_str(self.unicode())
    }
}

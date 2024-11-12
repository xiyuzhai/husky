use crate::precedence::{VdPrecedence, VdPrecedenceRange};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum VdBaseBinaryOpr {
    /// `a \times b`
    Times,
    /// `a \otimes b`
    Otimes,
    /// a-b
    Sub,
    /// a/b
    Div,
}

impl VdBaseBinaryOpr {
    pub const TIMES: Self = VdBaseBinaryOpr::Times;
    pub const OTIMES: Self = VdBaseBinaryOpr::Otimes;
    pub const SUB: Self = VdBaseBinaryOpr::Sub;
    pub const DIV: Self = VdBaseBinaryOpr::Div;
}

impl VdBaseBinaryOpr {
    pub fn fmt_str(self) -> &'static str {
        match self {
            VdBaseBinaryOpr::Times => todo!(),
            VdBaseBinaryOpr::Otimes => todo!(),
            VdBaseBinaryOpr::Sub => todo!(),
            VdBaseBinaryOpr::Div => todo!(),
        }
    }

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        match self {
            VdBaseBinaryOpr::Times => VdPrecedenceRange::MUL_DIV_LEFT,
            VdBaseBinaryOpr::Otimes => VdPrecedenceRange::MUL_DIV_LEFT,
            VdBaseBinaryOpr::Sub => VdPrecedenceRange::ADD_SUB_LEFT,
            VdBaseBinaryOpr::Div => todo!(),
        }
    }

    pub fn right_precedence_range(self) -> VdPrecedenceRange {
        todo!()
    }

    pub fn latex_code(self) -> &'static str {
        match self {
            VdBaseBinaryOpr::Times => "\\times",
            VdBaseBinaryOpr::Otimes => "\\otimes",
            VdBaseBinaryOpr::Sub => "-",
            VdBaseBinaryOpr::Div => "/",
        }
    }

    pub fn precedence(self) -> VdPrecedence {
        match self {
            VdBaseBinaryOpr::Times => VdPrecedence::MUL_DIV,
            VdBaseBinaryOpr::Otimes => VdPrecedence::MUL_DIV,
            VdBaseBinaryOpr::Sub => VdPrecedence::ADD_SUB,
            VdBaseBinaryOpr::Div => VdPrecedence::MUL_DIV,
        }
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum VdCompositeBinaryOpr {
    Add,
    Eq,
}

impl VdCompositeBinaryOpr {
    pub fn fmt_str(self) -> &'static str {
        match self {
            VdCompositeBinaryOpr::Add => "+",
            VdCompositeBinaryOpr::Eq => "=",
        }
    }

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        todo!()
    }

    pub fn right_precedence_range(self) -> VdPrecedenceRange {
        todo!()
    }

    pub fn latex_code(&self) -> &str {
        match self {
            VdCompositeBinaryOpr::Add => "+",
            VdCompositeBinaryOpr::Eq => "=",
        }
    }

    pub fn precedence(self) -> VdPrecedence {
        match self {
            VdCompositeBinaryOpr::Add => VdPrecedence::ADD_SUB,
            VdCompositeBinaryOpr::Eq => VdPrecedence::RELATION,
        }
    }
}

use crate::precedence::{LnPrecedence, LnPrecedenceRange};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy, Hash)]
pub enum LnBinaryOpr {
    Add,
    Sub,
    Mul,
    Div,
    Pow,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
}

impl LnBinaryOpr {
    pub fn fmt_str(self) -> &'static str {
        match self {
            LnBinaryOpr::Add => "+",
            LnBinaryOpr::Sub => "-",
            LnBinaryOpr::Mul => "*",
            LnBinaryOpr::Div => "/",
            LnBinaryOpr::Pow => "^",
            LnBinaryOpr::Eq => "=",
            LnBinaryOpr::Ne => "≠",
            LnBinaryOpr::Lt => "<",
            LnBinaryOpr::Gt => ">",
            LnBinaryOpr::Le => "≤",
            LnBinaryOpr::Ge => "≥",
        }
    }

    pub fn left_precedence_range(self) -> LnPrecedenceRange {
        match self {
            LnBinaryOpr::Add => LnPrecedenceRange::NoLess(LnPrecedence::AddSub),
            LnBinaryOpr::Sub => LnPrecedenceRange::NoLess(LnPrecedence::AddSub),
            LnBinaryOpr::Mul => LnPrecedenceRange::NoLess(LnPrecedence::MulDiv),
            LnBinaryOpr::Div => LnPrecedenceRange::NoLess(LnPrecedence::MulDiv),
            LnBinaryOpr::Pow => LnPrecedenceRange::NoLess(LnPrecedence::MulDiv),
            LnBinaryOpr::Eq => LnPrecedenceRange::NoLess(LnPrecedence::Relation),
            LnBinaryOpr::Ne => LnPrecedenceRange::NoLess(LnPrecedence::Relation),
            LnBinaryOpr::Lt => LnPrecedenceRange::NoLess(LnPrecedence::Relation),
            LnBinaryOpr::Gt => LnPrecedenceRange::NoLess(LnPrecedence::Relation),
            LnBinaryOpr::Le => LnPrecedenceRange::NoLess(LnPrecedence::Relation),
            LnBinaryOpr::Ge => LnPrecedenceRange::NoLess(LnPrecedence::Relation),
        }
    }

    pub fn right_precedence_range(self) -> LnPrecedenceRange {
        match self {
            LnBinaryOpr::Add => LnPrecedenceRange::Greater(LnPrecedence::AddSub),
            LnBinaryOpr::Sub => LnPrecedenceRange::Greater(LnPrecedence::AddSub),
            LnBinaryOpr::Mul => LnPrecedenceRange::Greater(LnPrecedence::MulDiv),
            LnBinaryOpr::Div => LnPrecedenceRange::Greater(LnPrecedence::MulDiv),
            LnBinaryOpr::Pow => LnPrecedenceRange::Greater(LnPrecedence::MulDiv),
            LnBinaryOpr::Eq => LnPrecedenceRange::Greater(LnPrecedence::Relation),
            LnBinaryOpr::Ne => LnPrecedenceRange::Greater(LnPrecedence::Relation),
            LnBinaryOpr::Lt => LnPrecedenceRange::Greater(LnPrecedence::Relation),
            LnBinaryOpr::Gt => LnPrecedenceRange::Greater(LnPrecedence::Relation),
            LnBinaryOpr::Le => LnPrecedenceRange::Greater(LnPrecedence::Relation),
            LnBinaryOpr::Ge => LnPrecedenceRange::Greater(LnPrecedence::Relation),
        }
    }

    pub fn outer_precedence(self) -> LnPrecedence {
        match self {
            LnBinaryOpr::Add => LnPrecedence::AddSub,
            LnBinaryOpr::Sub => LnPrecedence::AddSub,
            LnBinaryOpr::Mul => LnPrecedence::MulDiv,
            LnBinaryOpr::Div => LnPrecedence::MulDiv,
            LnBinaryOpr::Pow => LnPrecedence::MulDiv,
            LnBinaryOpr::Eq => LnPrecedence::Relation,
            LnBinaryOpr::Ne => LnPrecedence::Relation,
            LnBinaryOpr::Lt => LnPrecedence::Relation,
            LnBinaryOpr::Gt => LnPrecedence::Relation,
            LnBinaryOpr::Le => LnPrecedence::Relation,
            LnBinaryOpr::Ge => LnPrecedence::Relation,
        }
    }
}

impl std::fmt::Display for LnBinaryOpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.fmt_str())
    }
}

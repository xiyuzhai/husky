use crate::precedence::{VdPrecedence, VdPrecedenceRange};
use enum_index::IsEnumIndex;

#[derive(Debug, PartialEq, Eq, Clone, Copy, IsEnumIndex)]
pub enum VdBaseSeparator {
    Space,
    Comma,
    Semicolon,
    Add,
    Mul,
    Dot,
    Eq,
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
    Times,
    Otimes,
    Ne,
}

impl VdBaseSeparator {
    pub const SPACE: Self = Self::Space;
    pub const COMMA: Self = Self::Comma;
    pub const SEMICOLON: Self = Self::Semicolon;
    pub const ADD: Self = Self::Add;
    pub const MUL: Self = Self::Mul;
    pub const DOT: Self = Self::Dot;
    pub const EQ: Self = Self::Eq;
}

impl VdBaseSeparator {
    pub fn class(self) -> VdSeparatorClass {
        match self {
            VdBaseSeparator::Space => VdSeparatorClass::Space,
            VdBaseSeparator::Comma => VdSeparatorClass::Comma,
            VdBaseSeparator::Semicolon => VdSeparatorClass::Space,
            VdBaseSeparator::Add => VdSeparatorClass::Add,
            VdBaseSeparator::Mul | VdBaseSeparator::Times | VdBaseSeparator::Otimes => {
                VdSeparatorClass::Mul
            }
            VdBaseSeparator::Dot => VdSeparatorClass::Mul,
            VdBaseSeparator::Eq
            | VdBaseSeparator::Ne
            | VdBaseSeparator::Subset
            | VdBaseSeparator::Supset
            | VdBaseSeparator::Subseteq
            | VdBaseSeparator::Supseteq
            | VdBaseSeparator::Subseteqq
            | VdBaseSeparator::Supseteqq
            | VdBaseSeparator::Subsetneq
            | VdBaseSeparator::Supsetneq
            | VdBaseSeparator::In
            | VdBaseSeparator::Notin => VdSeparatorClass::Relation,
        }
    }

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        self.class().left_precedence_range()
    }

    pub fn right_precedence_range(self) -> VdPrecedenceRange {
        self.class().right_precedence_range()
    }
}

impl VdBaseSeparator {
    pub fn precedence(self) -> VdPrecedence {
        match self {
            VdBaseSeparator::Space => VdPrecedence::SPACE,
            VdBaseSeparator::Comma => todo!(),
            VdBaseSeparator::Semicolon => VdPrecedence::SEMICOLON,
            VdBaseSeparator::Add => VdPrecedence::ADD_SUB,
            VdBaseSeparator::Mul | VdBaseSeparator::Times | VdBaseSeparator::Otimes => {
                VdPrecedence::MUL_DIV
            }
            VdBaseSeparator::Dot => VdPrecedence::MUL_DIV,
            VdBaseSeparator::Eq
            | VdBaseSeparator::Subset
            | VdBaseSeparator::Supset
            | VdBaseSeparator::Subseteq
            | VdBaseSeparator::Supseteq
            | VdBaseSeparator::Subseteqq
            | VdBaseSeparator::Supseteqq
            | VdBaseSeparator::Subsetneq
            | VdBaseSeparator::Supsetneq
            | VdBaseSeparator::In
            | VdBaseSeparator::Notin
            | VdBaseSeparator::Ne => VdPrecedence::RELATION,
        }
    }

    pub fn latex_code(self) -> &'static str {
        match self {
            VdBaseSeparator::Space => "␣",
            VdBaseSeparator::Comma => ",",
            VdBaseSeparator::Semicolon => ";",
            VdBaseSeparator::Add => "+",
            VdBaseSeparator::Mul => "\\times",
            VdBaseSeparator::Dot => "\\cdot",
            VdBaseSeparator::Eq => "=",
            VdBaseSeparator::Subset => "\\subseteq",
            VdBaseSeparator::Supset => "\\supseteq",
            VdBaseSeparator::Subseteq => "\\subseteqq",
            VdBaseSeparator::Supseteq => "\\supseteqq",
            VdBaseSeparator::Subseteqq => "\\subseteqqq",
            VdBaseSeparator::Supseteqq => "\\supseteqqq",
            VdBaseSeparator::Subsetneq => "\\subsetneq",
            VdBaseSeparator::Supsetneq => "\\supsetneq",
            VdBaseSeparator::In => "\\in",
            VdBaseSeparator::Notin => "\\notin",
            VdBaseSeparator::Times => "\\times",
            VdBaseSeparator::Otimes => "\\otimes",
            VdBaseSeparator::Ne => "\\neq",
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSeparatorClass {
    Relation,
    Space,
    Comma,
    Semicolon,
    Mul,
    Add,
}

impl VdSeparatorClass {
    pub const RELATION: Self = Self::Relation;
    pub const SPACE: Self = Self::Space;
    pub const COMMA: Self = Self::Comma;
    pub const SEMICOLON: Self = Self::Semicolon;
    pub const MUL: Self = Self::Mul;
    pub const ADD: Self = Self::Add;
}

impl VdSeparatorClass {
    pub fn precedence(self) -> VdPrecedence {
        match self {
            VdSeparatorClass::Space => VdPrecedence::SPACE,
            VdSeparatorClass::Comma => VdPrecedence::COMMA,
            VdSeparatorClass::Semicolon => VdPrecedence::SEMICOLON,
            VdSeparatorClass::Add => VdPrecedence::ADD_SUB,
            VdSeparatorClass::Mul => VdPrecedence::MUL_DIV,
            VdSeparatorClass::Relation => VdPrecedence::RELATION,
        }
    }

    pub fn latex_code(self) -> &'static str {
        todo!()
    }

    pub fn left_precedence_range(self) -> VdPrecedenceRange {
        match self {
            VdSeparatorClass::Space => VdPrecedenceRange::NoLess(VdPrecedence::SPACE),
            VdSeparatorClass::Comma => VdPrecedenceRange::NoLess(VdPrecedence::COMMA),
            VdSeparatorClass::Semicolon => VdPrecedenceRange::NoLess(VdPrecedence::SEMICOLON),
            VdSeparatorClass::Add => VdPrecedenceRange::NoLess(VdPrecedence::ADD_SUB),
            VdSeparatorClass::Mul => VdPrecedenceRange::NoLess(VdPrecedence::MUL_DIV),
            VdSeparatorClass::Relation => VdPrecedenceRange::NoLess(VdPrecedence::RELATION),
        }
    }

    pub fn right_precedence_range(self) -> VdPrecedenceRange {
        match self {
            VdSeparatorClass::Space => VdPrecedenceRange::Greater(VdPrecedence::SPACE),
            VdSeparatorClass::Comma => VdPrecedenceRange::Greater(VdPrecedence::COMMA),
            VdSeparatorClass::Semicolon => VdPrecedenceRange::Greater(VdPrecedence::SEMICOLON),
            VdSeparatorClass::Add => VdPrecedenceRange::Greater(VdPrecedence::ADD_SUB),
            VdSeparatorClass::Mul => VdPrecedenceRange::Greater(VdPrecedence::MUL_DIV),
            VdSeparatorClass::Relation => VdPrecedenceRange::Greater(VdPrecedence::RELATION),
        }
    }
}

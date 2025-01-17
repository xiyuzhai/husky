use crate::precedence::{VdPrecedence, VdPrecedenceRange};
use enum_index::IsEnumIndex;
use lisp_csv::expr::{LpCsvExpr, LpCsvExprData};

#[derive(Debug, PartialEq, Eq, Clone, Copy, IsEnumIndex, Hash, PartialOrd, Ord)]
pub enum VdBaseSeparator {
    Space,
    Comma,
    Semicolon,
    Add,
    Cdot,
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
    Times,
    Otimes,
    Leftrightarrow,
}

impl VdBaseSeparator {
    pub const SPACE: Self = Self::Space;
    pub const COMMA: Self = Self::Comma;
    pub const SEMICOLON: Self = Self::Semicolon;
    pub const ADD: Self = Self::Add;
    pub const CDOT: Self = Self::Cdot;
    pub const EQ: Self = Self::Eq;
    pub const NE: Self = Self::Ne;
    pub const LT: Self = Self::Lt;
    pub const GT: Self = Self::Gt;
    pub const LE: Self = Self::Le;
    pub const GE: Self = Self::Ge;
    pub const IN: Self = Self::In;
    pub const TIMES: Self = Self::Times;
}

impl VdBaseSeparator {
    pub fn class(self) -> VdSeparatorClass {
        match self {
            VdBaseSeparator::Space => VdSeparatorClass::Space,
            VdBaseSeparator::Comma => VdSeparatorClass::Comma,
            VdBaseSeparator::Semicolon => VdSeparatorClass::Space,
            VdBaseSeparator::Add => VdSeparatorClass::Add,
            VdBaseSeparator::Times | VdBaseSeparator::Otimes | VdBaseSeparator::Cdot => {
                VdSeparatorClass::Mul
            }
            VdBaseSeparator::Eq
            | VdBaseSeparator::Ne
            | VdBaseSeparator::Lt
            | VdBaseSeparator::Gt
            | VdBaseSeparator::Le
            | VdBaseSeparator::Ge
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
            VdBaseSeparator::Leftrightarrow => todo!(),
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
            VdBaseSeparator::Times | VdBaseSeparator::Otimes => VdPrecedence::MUL_DIV,
            VdBaseSeparator::Cdot => VdPrecedence::MUL_DIV,
            VdBaseSeparator::Eq
            | VdBaseSeparator::Ne
            | VdBaseSeparator::Lt
            | VdBaseSeparator::Gt
            | VdBaseSeparator::Le
            | VdBaseSeparator::Ge
            | VdBaseSeparator::Subset
            | VdBaseSeparator::Supset
            | VdBaseSeparator::Subseteq
            | VdBaseSeparator::Supseteq
            | VdBaseSeparator::Subseteqq
            | VdBaseSeparator::Supseteqq
            | VdBaseSeparator::Subsetneq
            | VdBaseSeparator::Supsetneq
            | VdBaseSeparator::In
            | VdBaseSeparator::Notin => VdPrecedence::RELATION,
            VdBaseSeparator::Leftrightarrow => VdPrecedence::DEDUCTION,
        }
    }

    pub fn latex_code(self) -> &'static str {
        match self {
            VdBaseSeparator::Space => "␣",
            VdBaseSeparator::Comma => ",",
            VdBaseSeparator::Semicolon => ";",
            VdBaseSeparator::Add => "+",
            VdBaseSeparator::Times => "\\times",
            VdBaseSeparator::Cdot => "\\cdot",
            VdBaseSeparator::Eq => "=",
            VdBaseSeparator::Ne => "\\neq",
            VdBaseSeparator::Lt => "<",
            VdBaseSeparator::Gt => ">",
            VdBaseSeparator::Le => "\\le",
            VdBaseSeparator::Ge => "\\ge",
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
            VdBaseSeparator::Leftrightarrow => "\\Leftrightarrow",
        }
    }

    pub fn unicode(self) -> &'static str {
        match self {
            VdBaseSeparator::Space => "␣",
            VdBaseSeparator::Comma => ",",
            VdBaseSeparator::Semicolon => ";",
            VdBaseSeparator::Add => "+",
            VdBaseSeparator::Times => "×",
            VdBaseSeparator::Cdot => "·",
            VdBaseSeparator::Eq => "=",
            VdBaseSeparator::Ne => "≠",
            VdBaseSeparator::Lt => "<",
            VdBaseSeparator::Gt => ">",
            VdBaseSeparator::Le => "≤",
            VdBaseSeparator::Ge => "≥",
            VdBaseSeparator::Subset => "⊂",
            VdBaseSeparator::Supset => "⊃",
            VdBaseSeparator::Subseteq => "⊆",
            VdBaseSeparator::Supseteq => "⊇",
            VdBaseSeparator::Subseteqq => "⫅",
            VdBaseSeparator::Supseteqq => "⫆",
            VdBaseSeparator::Subsetneq => "⊊",
            VdBaseSeparator::Supsetneq => "⊋",
            VdBaseSeparator::In => "∈",
            VdBaseSeparator::Notin => "∉",
            VdBaseSeparator::Times => "×",
            VdBaseSeparator::Otimes => "⊗",
            VdBaseSeparator::Leftrightarrow => todo!(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSeparatorClass {
    Deduction,
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
            VdSeparatorClass::Deduction => VdPrecedence::DEDUCTION,
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
            VdSeparatorClass::Deduction => VdPrecedenceRange::NoLess(VdPrecedence::DEDUCTION),
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
            VdSeparatorClass::Deduction => VdPrecedenceRange::NoLess(VdPrecedence::DEDUCTION),
            VdSeparatorClass::Space => VdPrecedenceRange::Greater(VdPrecedence::SPACE),
            VdSeparatorClass::Comma => VdPrecedenceRange::Greater(VdPrecedence::COMMA),
            VdSeparatorClass::Semicolon => VdPrecedenceRange::Greater(VdPrecedence::SEMICOLON),
            VdSeparatorClass::Add => VdPrecedenceRange::Greater(VdPrecedence::ADD_SUB),
            VdSeparatorClass::Mul => VdPrecedenceRange::Greater(VdPrecedence::MUL_DIV),
            VdSeparatorClass::Relation => VdPrecedenceRange::Greater(VdPrecedence::RELATION),
        }
    }
}

impl VdBaseSeparator {
    pub fn from_lp_csv_expr(expr: &LpCsvExpr) -> Self {
        let LpCsvExprData::Ident(ref ident) = expr.data else {
            todo!()
        };
        match ident.as_str() {
            "space" => VdBaseSeparator::Space,
            "comma" => VdBaseSeparator::Comma,
            "semicolon" => VdBaseSeparator::Semicolon,
            "add" => VdBaseSeparator::Add,
            "dot" => VdBaseSeparator::Cdot,
            "eq" => VdBaseSeparator::Eq,
            "ne" => VdBaseSeparator::Ne,
            "lt" => VdBaseSeparator::Lt,
            "gt" => VdBaseSeparator::Gt,
            "le" => VdBaseSeparator::Le,
            "ge" => VdBaseSeparator::Ge,
            "subset" => VdBaseSeparator::Subset,
            "supset" => VdBaseSeparator::Supset,
            "in" => VdBaseSeparator::In,
            "notin" => VdBaseSeparator::Notin,
            "times" => VdBaseSeparator::Times,
            "otimes" => VdBaseSeparator::Otimes,
            "cdot" => VdBaseSeparator::Cdot,
            "leftrightarrow" => VdBaseSeparator::Leftrightarrow,
            _ => todo!(),
        }
    }
}

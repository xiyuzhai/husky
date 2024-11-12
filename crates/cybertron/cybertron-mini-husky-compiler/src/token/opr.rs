use super::ident::Ident;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Opr {
    Prefix(PrefixOpr),
    Binary(BinaryOpr),
    Suffix(SuffixOpr),
}

impl std::fmt::Debug for Opr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    Assign,
    TypeIs,
    EqNe,
    AddOrSub,
    MulOrDiv,
    Prefix,
    Suffix,
    ScopeResolution,
}

impl Opr {
    /// # prefix
    pub const NOT: Self = Opr::Prefix(PrefixOpr::Not);
    pub const PLUS: Self = Opr::Prefix(PrefixOpr::Plus);
    pub const MINUS: Self = Opr::Prefix(PrefixOpr::Minus);
    /// # binary
    pub const ADD: Self = Opr::Binary(BinaryOpr::Add);
    pub const SUB: Self = Opr::Binary(BinaryOpr::Sub);
    pub const MUL: Self = Opr::Binary(BinaryOpr::Mul);
    pub const DIV: Self = Opr::Binary(BinaryOpr::Div);
    pub const ASSIGN: Self = Opr::Binary(BinaryOpr::Assign);
    pub const EQ: Self = Opr::Binary(BinaryOpr::Eq);
    pub const TYPE_IS: Self = Opr::Binary(BinaryOpr::TypeIs);
    pub const SCOPE_RESOLUTION: Self = Opr::Binary(BinaryOpr::ScopeResolution);
    pub const LIGHT_ARROW: Self = Opr::Binary(BinaryOpr::LightArrow);
    /// # suffix
    pub const INCR: Self = Opr::Suffix(SuffixOpr::Incr);
    pub const DECR: Self = Opr::Suffix(SuffixOpr::Decr);
}

impl Opr {
    pub fn repr(self) -> String {
        match self {
            Opr::Prefix(slf) => slf.repr().to_string(),
            Opr::Binary(slf) => slf.repr().to_string(),
            Opr::Suffix(slf) => slf.repr(),
        }
    }

    pub fn repr_short(self) -> String {
        match self {
            Opr::Prefix(slf) => slf.repr_short().to_owned(),
            Opr::Binary(slf) => slf.repr_short().to_owned(),
            Opr::Suffix(slf) => slf.repr().to_owned(),
        }
    }
}

/// # binary

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum BinaryOpr {
    Add,
    Sub,
    Mul,
    Div,
    Assign,
    Eq,
    Ne,
    ScopeResolution,
    TypeIs,
    LightArrow,
    Vertical,
}

impl std::fmt::Debug for BinaryOpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}

impl BinaryOpr {
    pub fn precedence(self) -> Precedence {
        match self {
            BinaryOpr::Eq | BinaryOpr::Ne => Precedence::EqNe,
            BinaryOpr::Add | BinaryOpr::Sub => Precedence::AddOrSub,
            BinaryOpr::Mul | BinaryOpr::Div => Precedence::MulOrDiv,
            BinaryOpr::Assign => Precedence::Assign,
            BinaryOpr::ScopeResolution => Precedence::ScopeResolution,
            BinaryOpr::TypeIs => Precedence::TypeIs,
            BinaryOpr::LightArrow => todo!(),
            BinaryOpr::Vertical => todo!(),
        }
    }
}

impl BinaryOpr {
    pub fn repr(self) -> &'static str {
        match self {
            BinaryOpr::Add => "+(add)",
            BinaryOpr::Sub => "-(sub)",
            BinaryOpr::Mul => "*",
            BinaryOpr::Div => "/",
            BinaryOpr::Assign => "=",
            BinaryOpr::Eq => "==",
            BinaryOpr::Ne => "!=",
            BinaryOpr::ScopeResolution => "::",
            BinaryOpr::TypeIs => ":",
            BinaryOpr::LightArrow => "->",
            BinaryOpr::Vertical => todo!(),
        }
    }

    pub fn repr_short(self) -> &'static str {
        match self {
            BinaryOpr::Add => "+",
            BinaryOpr::Sub => "-",
            BinaryOpr::Mul => "*",
            BinaryOpr::Div => "/",
            BinaryOpr::Assign => "=",
            BinaryOpr::Eq => "==",
            BinaryOpr::Ne => "!=",
            BinaryOpr::ScopeResolution => "::",
            BinaryOpr::TypeIs => ":",
            BinaryOpr::LightArrow => "->",
            BinaryOpr::Vertical => todo!(),
        }
    }
}

/// # prefix

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PrefixOpr {
    Not,
    Minus,
    Plus,
}

impl std::fmt::Debug for PrefixOpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}

impl PrefixOpr {
    pub fn repr(self) -> &'static str {
        match self {
            PrefixOpr::Not => "!",
            PrefixOpr::Plus => "+(plus)",
            PrefixOpr::Minus => "-(minus)",
        }
    }

    pub fn repr_short(self) -> &'static str {
        match self {
            PrefixOpr::Not => "!",
            PrefixOpr::Plus => "+",
            PrefixOpr::Minus => "-",
        }
    }

    pub fn precedence(self) -> Precedence {
        Precedence::Prefix
    }
}

/// # suffix

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum SuffixOpr {
    Incr,
    Decr,
    Field(Ident),
}

impl SuffixOpr {
    pub fn precedence(self) -> Precedence {
        Precedence::Suffix
    }
}

impl std::fmt::Debug for SuffixOpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}

impl SuffixOpr {
    pub fn repr(self) -> String {
        match self {
            SuffixOpr::Incr => "++".to_string(),
            SuffixOpr::Decr => "--".to_string(),
            SuffixOpr::Field(ident) => format!(".{}", ident.repr()),
        }
    }
}

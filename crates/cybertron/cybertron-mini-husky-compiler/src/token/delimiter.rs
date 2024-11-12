#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Delimiter {
    Parenthesis,
    Box,
    Curly,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct LeftDelimiter(Delimiter);

impl std::fmt::Debug for LeftDelimiter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}
pub const LPAR: LeftDelimiter = LeftDelimiter(Delimiter::Parenthesis);
pub const LBOX: LeftDelimiter = LeftDelimiter(Delimiter::Box);
pub const LCURL: LeftDelimiter = LeftDelimiter(Delimiter::Curly);

impl LeftDelimiter {
    pub fn delimiter(self) -> Delimiter {
        self.0
    }

    pub fn repr(self) -> &'static str {
        match self.0 {
            Delimiter::Parenthesis => "(",
            Delimiter::Box => "[",
            Delimiter::Curly => "{",
        }
    }

    pub fn repr2(self) -> &'static str {
        match self.0 {
            Delimiter::Parenthesis => "(",
            Delimiter::Box => "[",
            Delimiter::Curly => "{ ",
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct RightDelimiter(Delimiter);

pub const RPAR: RightDelimiter = RightDelimiter(Delimiter::Parenthesis);
pub const RBOX: RightDelimiter = RightDelimiter(Delimiter::Box);
pub const RCURL: RightDelimiter = RightDelimiter(Delimiter::Curly);

impl RightDelimiter {
    pub fn repr(self) -> &'static str {
        match self.0 {
            Delimiter::Parenthesis => ")",
            Delimiter::Box => "]",
            Delimiter::Curly => "}",
        }
    }

    pub fn repr2(self) -> &'static str {
        match self.0 {
            Delimiter::Parenthesis => ")",
            Delimiter::Box => "]",
            Delimiter::Curly => " }",
        }
    }
}

impl std::fmt::Debug for RightDelimiter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}

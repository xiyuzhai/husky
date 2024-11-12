#[enum_class::from_variants]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Keyword {
    Defn(DefnKeyword),
    Stmt(StmtKeyword),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum DefnKeyword {
    Struct,
    Enum,
    Fn,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum StmtKeyword {
    Let,
    Return,
    Assert,
    If,
    Else,
}

impl std::fmt::Debug for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}

impl std::fmt::Debug for DefnKeyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}

impl std::fmt::Debug for StmtKeyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("`{}`", self.repr()))
    }
}

impl Keyword {
    pub(super) fn new(s: &str) -> Option<Self> {
        match s {
            "struct" => Some(Keyword::Defn(DefnKeyword::Struct)),
            "enum" => Some(Keyword::Defn(DefnKeyword::Enum)),
            "fn" => Some(Keyword::Defn(DefnKeyword::Fn)),
            "let" => Some(Keyword::Stmt(StmtKeyword::Let)),
            "return" => Some(Keyword::Stmt(StmtKeyword::Return)),
            "assert" => Some(Keyword::Stmt(StmtKeyword::Assert)),
            "if" => Some(Keyword::Stmt(StmtKeyword::If)),
            "else" => Some(Keyword::Stmt(StmtKeyword::Else)),
            _ => None,
        }
    }
}

impl DefnKeyword {
    pub fn repr(self) -> &'static str {
        match self {
            DefnKeyword::Struct => "struct",
            DefnKeyword::Enum => "enum",
            DefnKeyword::Fn => "fn",
        }
    }
}

impl StmtKeyword {
    pub fn repr(self) -> &'static str {
        match self {
            StmtKeyword::Let => "let",
            StmtKeyword::If => "if",
            StmtKeyword::Else => "else",
            StmtKeyword::Return => "return",
            StmtKeyword::Assert => "assert",
        }
    }
}

impl Keyword {
    pub fn repr(self) -> &'static str {
        match self {
            Keyword::Defn(defn_keyword) => defn_keyword.repr(),
            Keyword::Stmt(stmt_keyword) => stmt_keyword.repr(),
        }
    }
}

impl Keyword {
    pub const LET: Keyword = Keyword::Stmt(StmtKeyword::Let);
    pub const IF: Keyword = Keyword::Stmt(StmtKeyword::If);
    pub const ELSE: Keyword = Keyword::Stmt(StmtKeyword::Else);
    pub const STRUCT: Keyword = Keyword::Defn(DefnKeyword::Struct);
    pub const ENUM: Keyword = Keyword::Defn(DefnKeyword::Enum);
    pub const FN: Keyword = Keyword::Defn(DefnKeyword::Fn);
}

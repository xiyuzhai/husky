use enum_index::{full_map::EnumFullVecMap, IsEnumIndex};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, IsEnumIndex)]
#[repr(u8)]
pub enum LxMathPunctuation {
    /// Addition `+`
    Add,
    /// Subtraction `-`
    Sub,
    /// Multiplication `\cdot`
    Mul,
    /// Division `/`
    Div,
    /// Element of `\in` or `∈`
    In,
    /// Not an element of `\notin` or `∉`
    NotIn,
    /// Subset of `\subset` or `⊂`
    Subset,
    /// Superset of `\supset` or `⊃`
    Superset,
    /// Subset of or equal to `\subseteq` or `⊆`
    SubsetEq,
    /// Superset of or equal to `\supseteq` or `⊇`
    SupersetEq,
    /// For all `\forall` or `∀`
    ForAll,
    /// Exists `\exists` or `∃`
    Exists,
    /// Does not exist `\nexists` or `∄`
    NotExists,
    /// Infinity `\infty` or `∞`
    Infinity,
    /// Equals `=`
    Equals,
    /// Not equals `\neq` or `≠`
    NotEquals,
    /// Less than `<`
    LessThan,
    /// Greater than `>`
    GreaterThan,
    /// Less than or equal to `\leq` or `≤` or `<=`
    LessEq,
    /// Greater than or equal to `\geq` or `≥` `>=`
    GreaterEq,
    /// Plus minus `\pm` or `±`
    PlusMinus,
    /// Times `\times` or `×`
    Times,
    /// Left parenthesis `(`
    Lpar,
    /// Right parenthesis `)`
    Rpar,
    /// Left box `[`
    Lbox,
    /// Right box `]`
    Rbox,
    /// Escaped left curly `{`
    EscapedLcurl,
    /// Escaped right curly `}`
    EscapedRcurl,
    Ldot,
}

pub type LxMathPunctuationMap<T> = EnumFullVecMap<LxMathPunctuation, T>;

impl LxMathPunctuation {
    pub fn to_str(self) -> &'static str {
        match self {
            LxMathPunctuation::Add => "+",
            LxMathPunctuation::Sub => "-",
            LxMathPunctuation::Mul => "·",
            LxMathPunctuation::Div => "/",
            LxMathPunctuation::In => "∈",
            LxMathPunctuation::NotIn => "∉",
            LxMathPunctuation::Subset => "⊂",
            LxMathPunctuation::Superset => "⊃",
            LxMathPunctuation::SubsetEq => "⊆",
            LxMathPunctuation::SupersetEq => "⊇",
            LxMathPunctuation::ForAll => "∀",
            LxMathPunctuation::Exists => "∃",
            LxMathPunctuation::NotExists => "∄",
            LxMathPunctuation::Infinity => "∞",
            LxMathPunctuation::Equals => "=",
            LxMathPunctuation::NotEquals => "≠",
            LxMathPunctuation::LessThan => "<",
            LxMathPunctuation::GreaterThan => ">",
            LxMathPunctuation::LessEq => "≤",
            LxMathPunctuation::GreaterEq => "≥",
            LxMathPunctuation::PlusMinus => "±",
            LxMathPunctuation::Times => "×",
            LxMathPunctuation::Lpar => "(",
            LxMathPunctuation::Rpar => ")",
            LxMathPunctuation::Lbox => "[",
            LxMathPunctuation::Rbox => "]",
            LxMathPunctuation::EscapedLcurl => "\\{",
            LxMathPunctuation::EscapedRcurl => "\\}",
            LxMathPunctuation::Ldot => ".",
        }
    }

    pub fn try_from_char(c: char) -> Option<Self> {
        match c {
            '+' => Some(LxMathPunctuation::Add),
            '-' => Some(LxMathPunctuation::Sub),
            '·' => Some(LxMathPunctuation::Mul),
            '/' => Some(LxMathPunctuation::Div),
            '∈' => Some(LxMathPunctuation::In),
            '∉' => Some(LxMathPunctuation::NotIn),
            '⊂' => Some(LxMathPunctuation::Subset),
            '⊃' => Some(LxMathPunctuation::Superset),
            '⊆' => Some(LxMathPunctuation::SubsetEq),
            '⊇' => Some(LxMathPunctuation::SupersetEq),
            '∀' => Some(LxMathPunctuation::ForAll),
            '∃' => Some(LxMathPunctuation::Exists),
            '∄' => Some(LxMathPunctuation::NotExists),
            '∞' => Some(LxMathPunctuation::Infinity),
            '=' => Some(LxMathPunctuation::Equals),
            '≠' => Some(LxMathPunctuation::NotEquals),
            '<' => Some(LxMathPunctuation::LessThan),
            '>' => Some(LxMathPunctuation::GreaterThan),
            '≤' => Some(LxMathPunctuation::LessEq),
            '≥' => Some(LxMathPunctuation::GreaterEq),
            '±' => Some(LxMathPunctuation::PlusMinus),
            '×' => Some(LxMathPunctuation::Times),
            '(' => Some(LxMathPunctuation::Lpar),
            ')' => Some(LxMathPunctuation::Rpar),
            '[' => Some(LxMathPunctuation::Lbox),
            ']' => Some(LxMathPunctuation::Rbox),
            _ => None,
        }
    }
}

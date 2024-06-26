use crate::{TokenData, WordOpr};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Convexity {
    Convex,
    Concave,
    Any,
}
impl Convexity {
    pub fn compatible_with(self: Convexity, right: Convexity) -> bool {
        match self {
            Convexity::Convex => match right {
                Convexity::Convex => false,
                Convexity::Concave => true,
                Convexity::Any => true,
            },
            Convexity::Concave => match right {
                Convexity::Convex => true,
                Convexity::Concave => false,
                Convexity::Any => true,
            },
            Convexity::Any => true,
        }
    }
}

impl TokenData {
    pub fn right_convexity(&self) -> Convexity {
        match self {
            TokenData::Keyword(_) => Convexity::Concave,
            TokenData::Ident(_) | TokenData::Label(_) => Convexity::Convex,
            TokenData::Punctuation(punctuation) => punctuation.right_convexity(),
            TokenData::WordOpr(opr) => match opr {
                WordOpr::And => Convexity::Concave,
                WordOpr::Or => Convexity::Concave,
                WordOpr::As => Convexity::Concave,
                WordOpr::Of => Convexity::Concave,
                WordOpr::Be => Convexity::Concave,
            },
            TokenData::Literal(_) => Convexity::Convex,
            TokenData::Error(_) => Convexity::Any,
        }
    }
}

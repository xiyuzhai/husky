use ordered_float::OrderedFloat;
use std::fmt::Pointer;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Literal {
    Int(i32),
    Float(OrderedFloat<f32>),
}

impl std::fmt::Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Int(i) => i.fmt(f),
            Literal::Float(_) => todo!(),
        }
    }
}

impl std::fmt::Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Int(i) => f.write_fmt(format_args!("`{i}`")),
            Literal::Float(_) => todo!(),
        }
    }
}

impl Literal {
    pub fn repr(self) -> String {
        match self {
            Literal::Int(i) => i.to_string(),
            Literal::Float(_) => todo!(),
        }
    }
}

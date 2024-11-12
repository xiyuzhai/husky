pub mod code;
pub mod math;
pub mod rose;

use self::{math::LxMathTokenData, rose::LxRoseTokenData};
use crate::lexer::LxLexer;
#[cfg(test)]
use crate::*;
use code::LxCodeTokenData;
use latex_prelude::mode::LxMode;

#[enum_class::from_variants]
#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum LxTokenData {
    Math(LxMathTokenData),
    Rose(LxRoseTokenData),
    Code(LxCodeTokenData),
}

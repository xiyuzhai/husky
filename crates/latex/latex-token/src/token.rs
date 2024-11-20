pub mod lisp;
pub mod math;
pub mod name;
pub mod root;
pub mod rose;
pub mod spec;

use self::{
    lisp::LxLispTokenData, math::LxMathTokenData, name::LxNameTokenData, root::LxRootTokenData,
    rose::LxRoseTokenData,
};
use crate::lexer::LxLexer;
#[cfg(test)]
use crate::*;
use latex_prelude::mode::LxMode;
use spec::LxSpecTokenData;

#[enum_class::from_variants]
#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxTokenData {
    Lisp(LxLispTokenData),
    Math(LxMathTokenData),
    Name(LxNameTokenData),
    Root(LxRootTokenData),
    Rose(LxRoseTokenData),
    Spec(LxSpecTokenData),
}

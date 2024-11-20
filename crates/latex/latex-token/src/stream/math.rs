use crate::{idx::LxMathTokenIdx, lexer::LxLexer, token::math::LxMathTokenData};

pub struct LxMathTokenStream<'a> {
    lexer: LxLexer<'a>,
}

impl<'a> LxMathTokenStream<'a> {
    pub fn new(lexer: LxLexer<'a>) -> Self {
        Self { lexer }
    }
}

impl<'a> Iterator for LxMathTokenStream<'a> {
    type Item = (LxMathTokenIdx, LxMathTokenData);

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next_math_token()
    }
}

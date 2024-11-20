use crate::{idx::LxLispTokenIdx, lexer::LxLexer, token::lisp::LxLispTokenData};

pub struct LxLispTokenStream<'a> {
    lexer: LxLexer<'a>,
}

impl<'a> LxLispTokenStream<'a> {
    pub fn new(lexer: LxLexer<'a>) -> Self {
        Self { lexer }
    }
}

impl<'a> Iterator for LxLispTokenStream<'a> {
    type Item = (LxLispTokenIdx, LxLispTokenData);

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next_lisp_token()
    }
}

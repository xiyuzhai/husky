use crate::{idx::LxRootTokenIdx, lexer::LxLexer, token::root::LxRootTokenData};

pub struct LxRootTokenStream<'a> {
    lexer: LxLexer<'a>,
}

impl<'a> LxRootTokenStream<'a> {
    pub fn new(lexer: LxLexer<'a>) -> Self {
        Self { lexer }
    }
}

impl<'a> Iterator for LxRootTokenStream<'a> {
    type Item = (LxRootTokenIdx, LxRootTokenData);

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next_root_token()
    }
}

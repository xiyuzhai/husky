use crate::{data::code::LxCodeTokenData, idx::LxCodeTokenIdx, lexer::LxLexer};

pub struct LxCodeTokenStream<'a> {
    lexer: LxLexer<'a>,
}

impl<'a> LxCodeTokenStream<'a> {
    pub fn new(lexer: LxLexer<'a>) -> Self {
        Self { lexer }
    }
}

impl<'a> Iterator for LxCodeTokenStream<'a> {
    type Item = (LxCodeTokenIdx, LxCodeTokenData);

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next_code_token()
    }
}

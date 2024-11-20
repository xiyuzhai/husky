use crate::{idx::LxNameTokenIdx, lexer::LxLexer, token::name::LxNameTokenData};

pub struct LxWordTokenStream<'a> {
    lexer: LxLexer<'a>,
}

impl<'a> LxWordTokenStream<'a> {
    pub fn new(lexer: LxLexer<'a>) -> Self {
        Self { lexer }
    }
}

impl<'a> Iterator for LxWordTokenStream<'a> {
    type Item = (LxNameTokenIdx, LxNameTokenData);

    fn next(&mut self) -> Option<Self::Item> {
        self.lexer.next_name_token()
    }
}

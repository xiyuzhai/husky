use crate::{
    data::{NamAstArena, NamAstIdxRange},
    parser::NamParser,
};

pub struct NamAstSheet {
    arena: NamAstArena,
    root_asts: NamAstIdxRange,
}

impl NamAstSheet {
    pub fn from_input(input: &str) -> Self {
        let mut parser = NamParser::new(input);
        let root_asts = parser.parse_asts();
        let arena = parser.finish();
        Self { arena, root_asts }
    }
}

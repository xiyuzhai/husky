#[derive(Debug, PartialEq, Eq, Clone, Copy, PartialOrd, Ord)]
pub enum NamAstLevel {
    Book,
    Chapter,
    Section,
    Subsection,
    Subsubsection,
    Entry,
}

#[test]
fn nam_ast_level_ord_works() {
    assert!(NamAstLevel::Book < NamAstLevel::Chapter);
}

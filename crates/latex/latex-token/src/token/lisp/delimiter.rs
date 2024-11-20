#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxLispDelimiter {
    Parenthesis,
    Box,
}

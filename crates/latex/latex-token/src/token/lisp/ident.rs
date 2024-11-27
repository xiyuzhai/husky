use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LxLispIdent(Coword);

impl LxLispIdent {
    pub fn new(s: &str) -> Self {
        debug_assert!(s.chars().next().unwrap().is_ascii_alphabetic());
        fn is_valid_ident(s: &str) -> bool {
            s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        }
        debug_assert!(is_valid_ident(s));
        Self(Coword::from_ref(s))
    }
}

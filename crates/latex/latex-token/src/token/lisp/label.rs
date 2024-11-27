use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LxLispXlabel(Coword);

impl LxLispXlabel {
    pub fn new(s: &str) -> Self {
        fn is_valid_ident(s: &str) -> bool {
            s.chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == ':')
        }
        debug_assert!(is_valid_ident(s));
        Self(Coword::from_ref(s))
    }
}

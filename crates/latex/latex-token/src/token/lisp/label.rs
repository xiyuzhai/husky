use super::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct LxLispXlabel(Coword);

impl LxLispXlabel {
    pub fn new(s: &str, db: &::salsa::Db) -> Self {
        fn is_valid_ident(s: &str) -> bool {
            s.chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '-' || c == ':')
        }
        debug_assert!(is_valid_ident(s));
        Self(Coword::from_ref(db, s))
    }
}

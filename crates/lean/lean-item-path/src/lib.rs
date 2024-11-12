// TODO: ad hoc
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LnItemPath {
    Nat,
}

// TODO: maybe use menu?
impl LnItemPath {
    pub const NAT: Self = Self::Nat;
}

impl LnItemPath {
    pub fn show(&self, db: &::salsa::Db) -> String {
        match self {
            LnItemPath::Nat => "Nat".to_string(),
        }
    }
}

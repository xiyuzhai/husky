#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdCategoryPath {
    /// the category of sets
    Set,
    /// the category of propositions
    Proposition,
}

impl VdCategoryPath {
    pub const SET: Self = VdCategoryPath::Set;
    pub const PROPOSITION: Self = VdCategoryPath::Proposition;
}

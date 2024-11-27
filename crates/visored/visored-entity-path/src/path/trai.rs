/// We use `trait` instead of `class` to avoid confusion with the mathematical concept `class`.
// TODO: ad hoc implementation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdTraitPath {
    Group,
    AbelianGroup,
    Ring,
}

impl VdTraitPath {
    pub const GROUP: Self = VdTraitPath::Group;
    pub const ABELIAN_GROUP: Self = VdTraitPath::AbelianGroup;
    pub const RING: Self = VdTraitPath::Ring;
}

impl VdTraitPath {
    pub fn show_aux(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VdTraitPath::Group => write!(f, "Grp"),
            VdTraitPath::AbelianGroup => write!(f, "Ab"),
            VdTraitPath::Ring => write!(f, "Ring"),
        }
    }
}

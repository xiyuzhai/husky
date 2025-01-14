#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VdPropPath {
    True,
    False,
}

impl VdPropPath {
    pub const TRUE: Self = VdPropPath::True;
    pub const FALSE: Self = VdPropPath::False;
}

impl std::fmt::Debug for VdPropPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.show_fmt(f)
    }
}

impl VdPropPath {
    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VdPropPath::True => f.write_str("true"),
            VdPropPath::False => f.write_str("false"),
        }
    }
}

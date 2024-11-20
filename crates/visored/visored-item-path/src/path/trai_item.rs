/// We use `trait` instead of `class` to avoid confusion with the mathematical concept `class`.
// TODO: ad hoc implementation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdTraitItemPath {
    GroupMul,
    AbelianGroupAdd,
    RingAdd,
    RingMul,
    RingPower,
    RingPos,
    RingNeg,
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,
    FieldDiv,
    RealSqrt,
}

impl VdTraitItemPath {
    pub const GROUP_MUL: Self = VdTraitItemPath::GroupMul;
    pub const ABELIAN_GROUP_ADD: Self = VdTraitItemPath::AbelianGroupAdd;
    pub const RING_ADD: Self = VdTraitItemPath::RingAdd;
    pub const RING_MUL: Self = VdTraitItemPath::RingMul;
    pub const RING_POWER: Self = VdTraitItemPath::RingPower;
    pub const RING_POS: Self = VdTraitItemPath::RingPos;
    pub const RING_NEG: Self = VdTraitItemPath::RingNeg;
    pub const FIELD_DIV: Self = VdTraitItemPath::FieldDiv;
    pub const REAL_SQRT: Self = VdTraitItemPath::RealSqrt;
    pub const EQ: Self = VdTraitItemPath::Eq;
    pub const NE: Self = VdTraitItemPath::Ne;
    pub const LT: Self = VdTraitItemPath::Lt;
    pub const GT: Self = VdTraitItemPath::Gt;
    pub const LE: Self = VdTraitItemPath::Le;
    pub const GE: Self = VdTraitItemPath::Ge;
}

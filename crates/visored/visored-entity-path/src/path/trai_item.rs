/// We use `trait` instead of `class` to avoid confusion with the mathematical concept `class`.
// TODO: ad hoc implementation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdTraitItemPath {
    GroupMul,
    AbelianGroupAdd,
    NatAdd,
    NatMul,
    RingAdd,
    RingSub,
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
    pub const NAT_ADD: Self = VdTraitItemPath::NatAdd;
    pub const NAT_MUL: Self = VdTraitItemPath::NatMul;
    pub const RING_ADD: Self = VdTraitItemPath::RingAdd;
    pub const RING_SUB: Self = VdTraitItemPath::RingSub;
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

impl VdTraitItemPath {
    pub fn show_aux(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VdTraitItemPath::GroupMul => write!(f, "*"),
            VdTraitItemPath::AbelianGroupAdd => write!(f, "+(abelian_group_add)"),
            VdTraitItemPath::NatAdd => write!(f, "+(nat_add)"),
            VdTraitItemPath::NatMul => write!(f, "*"),
            VdTraitItemPath::RingAdd => write!(f, "+(ring_add)"),
            VdTraitItemPath::RingSub => write!(f, "-(ring_sub)"),
            VdTraitItemPath::RingMul => write!(f, "*(ring_mul)"),
            VdTraitItemPath::RingPower => write!(f, "^(ring_power)"),
            VdTraitItemPath::RingPos => write!(f, "+(ring_pos)"),
            VdTraitItemPath::RingNeg => write!(f, "-(ring_neg)"),
            VdTraitItemPath::Eq => write!(f, "=(eq)"),
            VdTraitItemPath::Ne => write!(f, "≠(ne)"),
            VdTraitItemPath::Lt => write!(f, "<(lt)"),
            VdTraitItemPath::Gt => write!(f, ">(gt)"),
            VdTraitItemPath::Le => write!(f, "≤(le)"),
            VdTraitItemPath::Ge => write!(f, "≥(ge)"),
            VdTraitItemPath::FieldDiv => write!(f, "/(field_div)"),
            VdTraitItemPath::RealSqrt => write!(f, "√(real_sqrt)"),
        }
    }
}

use visored_mir_opr::separator::VdMirBaseSeparator;
use visored_opr::separator::VdBaseSeparator;

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqComparisonOpr {
    Bound(VdBsqBoundOpr),
    Eq,
    Ne,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqBoundOpr {
    Lt,
    Gt,
    Le,
    Ge,
}

impl VdBsqComparisonOpr {
    pub const EQ: Self = VdBsqComparisonOpr::Eq;
    pub const NE: Self = VdBsqComparisonOpr::Ne;
    pub const LT: Self = VdBsqComparisonOpr::Bound(VdBsqBoundOpr::Lt);
    pub const GT: Self = VdBsqComparisonOpr::Bound(VdBsqBoundOpr::Gt);
    pub const LE: Self = VdBsqComparisonOpr::Bound(VdBsqBoundOpr::Le);
    pub const GE: Self = VdBsqComparisonOpr::Bound(VdBsqBoundOpr::Ge);
}

impl VdBsqBoundOpr {
    pub fn from_mir_base_separator(separator: VdMirBaseSeparator) -> Option<Self> {
        match separator {
            VdMirBaseSeparator::Lt => Some(Self::Lt),
            VdMirBaseSeparator::Gt => Some(Self::Gt),
            VdMirBaseSeparator::Le => Some(Self::Le),
            VdMirBaseSeparator::Ge => Some(Self::Ge),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum VdBsqBoundBoundaryKind {
    Closed,
    Open,
}

impl VdBsqBoundBoundaryKind {
    pub fn contains(self, other: Self) -> bool {
        match (self, other) {
            (VdBsqBoundBoundaryKind::Open, VdBsqBoundBoundaryKind::Closed) => false,
            _ => true,
        }
    }
}

#[test]
fn vd_bsq_bound_boundary_kind_contains_works() {
    assert!(VdBsqBoundBoundaryKind::Closed.contains(VdBsqBoundBoundaryKind::Open));
    assert!(!VdBsqBoundBoundaryKind::Open.contains(VdBsqBoundBoundaryKind::Closed));
    assert!(VdBsqBoundBoundaryKind::Closed.contains(VdBsqBoundBoundaryKind::Closed));
    assert!(VdBsqBoundBoundaryKind::Open.contains(VdBsqBoundBoundaryKind::Open));
}

impl VdBsqBoundOpr {
    pub fn boundary_kind(self) -> VdBsqBoundBoundaryKind {
        match self {
            VdBsqBoundOpr::Lt => VdBsqBoundBoundaryKind::Open,
            VdBsqBoundOpr::Gt => VdBsqBoundBoundaryKind::Open,
            VdBsqBoundOpr::Le => VdBsqBoundBoundaryKind::Closed,
            VdBsqBoundOpr::Ge => VdBsqBoundBoundaryKind::Closed,
        }
    }
}

impl Into<VdBaseSeparator> for VdBsqComparisonOpr {
    fn into(self) -> VdBaseSeparator {
        match self {
            VdBsqComparisonOpr::Eq => VdBaseSeparator::Eq,
            VdBsqComparisonOpr::Ne => VdBaseSeparator::Ne,
            VdBsqComparisonOpr::Bound(bound_opr) => bound_opr.into(),
        }
    }
}

impl Into<VdBaseSeparator> for VdBsqBoundOpr {
    fn into(self) -> VdBaseSeparator {
        match self {
            VdBsqBoundOpr::Lt => VdBaseSeparator::Lt,
            VdBsqBoundOpr::Gt => VdBaseSeparator::Gt,
            VdBsqBoundOpr::Le => VdBaseSeparator::Le,
            VdBsqBoundOpr::Ge => VdBaseSeparator::Ge,
        }
    }
}

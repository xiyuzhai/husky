use husky_control_flow_utils::require;
use visored_mir_opr::separator::{
    chaining::{
        VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
    },
    VdMirBaseSeparator,
};
use visored_opr::separator::VdBaseSeparator;

use crate::foundations::bound::VdBsqBoundKind;

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
        require!(let VdMirBaseSeparator::Chaining(separator) = separator );
        Self::from_mir_base_chaining_separator(separator)
    }

    pub fn from_mir_base_chaining_separator(separator: VdMirBaseChainingSeparator) -> Option<Self> {
        require!(let VdMirBaseChainingSeparator::Relation(VdMirBaseRelationSeparator::Comparison(separator)) = separator);
        match separator {
            VdMirBaseComparisonSeparator::Lt => Some(Self::Lt),
            VdMirBaseComparisonSeparator::Gt => Some(Self::Gt),
            VdMirBaseComparisonSeparator::Le => Some(Self::Le),
            VdMirBaseComparisonSeparator::Ge => Some(Self::Ge),
            _ => None,
        }
    }

    /// `x > 1` is a lower bound, `x < 1` is an upper bound
    pub(crate) fn bound_kind(self) -> VdBsqBoundKind {
        match self {
            VdBsqBoundOpr::Lt => VdBsqBoundKind::Upper,
            VdBsqBoundOpr::Gt => VdBsqBoundKind::Lower,
            VdBsqBoundOpr::Le => VdBsqBoundKind::Upper,
            VdBsqBoundOpr::Ge => VdBsqBoundKind::Lower,
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

impl Into<VdMirBaseComparisonSeparator> for VdBsqComparisonOpr {
    fn into(self) -> VdMirBaseComparisonSeparator {
        match self {
            VdBsqComparisonOpr::Bound(bound_opr) => bound_opr.into(),
            VdBsqComparisonOpr::Eq => VdMirBaseComparisonSeparator::Eq,
            VdBsqComparisonOpr::Ne => VdMirBaseComparisonSeparator::Ne,
        }
    }
}

impl Into<VdMirBaseComparisonSeparator> for VdBsqBoundOpr {
    fn into(self) -> VdMirBaseComparisonSeparator {
        match self {
            VdBsqBoundOpr::Lt => VdMirBaseComparisonSeparator::Lt,
            VdBsqBoundOpr::Gt => VdMirBaseComparisonSeparator::Gt,
            VdBsqBoundOpr::Le => VdMirBaseComparisonSeparator::Le,
            VdBsqBoundOpr::Ge => VdMirBaseComparisonSeparator::Ge,
        }
    }
}

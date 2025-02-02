use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VdBsqNormalizedLitnumBoundKey<'sess> {
    normalized_monomials: VdBsqComnumTerm<'sess>,
}

impl<'sess> VdBsqNormalizedLitnumBoundKey<'sess> {
    pub(super) fn new(normalized_monomials: VdBsqComnumTerm<'sess>) -> Self {
        Self {
            normalized_monomials,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VdBsqNormalizedLitnumBound<'sess> {
    src: VdBsqLitnumBoundSrc<'sess>,
    inner: VdBsqNormalizedLitnumBoundInner<'sess>,
}

/// always a lower bound
///
/// `litnum` is the right hand side constant
///
/// `boundary_kind` indicates whether it's closed or open
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct VdBsqNormalizedLitnumBoundInner<'sess> {
    lower_bound_litnum: VdBsqLitnumTerm<'sess>,
    boundary_kind: VdBsqBoundBoundaryKind,
}

impl<'sess> VdBsqNormalizedLitnumBound<'sess> {
    pub(super) fn new(
        src: VdBsqLitnumBoundSrc<'sess>,
        lower_bound_litnum: VdBsqLitnumTerm<'sess>,
        boundary_kind: VdBsqBoundBoundaryKind,
    ) -> Self {
        Self {
            src,
            inner: VdBsqNormalizedLitnumBoundInner {
                lower_bound_litnum,
                boundary_kind,
            },
        }
    }
}

impl<'sess> VdBsqNormalizedLitnumBound<'sess> {
    pub fn is_upgrade_of(self, other: Self) -> bool {
        if self.inner == other.inner {
            return false;
        }
        self.inner.is_upgrade_of(other.inner)
    }
}

impl<'sess> VdBsqNormalizedLitnumBoundInner<'sess> {
    pub fn is_upgrade_of(self, other: Self) -> bool {
        self > other
    }
}

impl<'sess> VdBsqNormalizedLitnumBound<'sess> {
    pub(super) fn unnormalize(
        self,
        litnum_factor: VdBsqLitnumTerm<'sess>,
        litnum_summand: VdBsqLitnumTerm<'sess>,
        opr: VdBsqBoundOpr,
        db: &'sess FloaterDb,
    ) -> VdBsqLitnumBound<'sess> {
        VdBsqLitnumBound {
            src: self.src,
            litnum_factor,
            litnum_summand,
            bound_litnum: self
                .inner
                .lower_bound_litnum
                .add(litnum_summand, db)
                .mul(litnum_factor, db),
            boundary_kind: self.inner.boundary_kind,
            query_opr: opr,
        }
    }
}

#[test]
fn vd_bsq_normalized_litnum_bound_is_upgrade_works() {
    fn t<'sess>(
        slf: VdBsqNormalizedLitnumBoundInner<'sess>,
        other: VdBsqNormalizedLitnumBoundInner<'sess>,
        expected: bool,
    ) {
        assert_eq!(slf.is_upgrade_of(other), expected);
    }
    fn c<'sess>(t: impl Into<VdBsqLitnumTerm<'sess>>) -> VdBsqNormalizedLitnumBoundInner<'sess> {
        VdBsqNormalizedLitnumBoundInner {
            lower_bound_litnum: t.into(),
            boundary_kind: VdBsqBoundBoundaryKind::Closed,
        }
    }
    fn o<'sess>(t: impl Into<VdBsqLitnumTerm<'sess>>) -> VdBsqNormalizedLitnumBoundInner<'sess> {
        VdBsqNormalizedLitnumBoundInner {
            lower_bound_litnum: t.into(),
            boundary_kind: VdBsqBoundBoundaryKind::Open,
        }
    }
    t(c(1), o(1), false);
    t(o(1), o(1), false);
    t(c(1), c(1), false);
    t(o(1), c(1), true);
    t(c(1), c(2), false);
    t(c(1), o(2), false);
    t(o(1), c(2), false);
    t(o(1), o(2), false);
    t(c(2), c(1), true);
    t(c(2), o(1), true);
    t(o(2), c(1), true);
    t(o(2), o(1), true);
}

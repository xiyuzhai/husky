use crate::term::litnum::VdBsqLitnumTerm;

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqBoundKind {
    Lower,
    Upper,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqLitnumUpperBoundWithInfinity<'sess> {
    FiniteOpen(VdBsqLitnumTerm<'sess>),
    FiniteClosed(VdBsqLitnumTerm<'sess>),
    PositiveInfinity,
}

#[derive(Debug, Clone, Copy, Hash, Eq, PartialEq, PartialOrd, Ord)]
pub enum VdBsqLitnumLowerBoundWithInfinity<'sess> {
    NegativeInfinity,
    Finite(VdBsqLitnumTerm<'sess>),
}

#[test]
fn vd_bsq_litnum_upper_bound_with_infinity_ord_works() {
    assert!(
        VdBsqLitnumUpperBoundWithInfinity::FiniteOpen(1.into())
            < VdBsqLitnumUpperBoundWithInfinity::PositiveInfinity
    );
    assert!(
        VdBsqLitnumUpperBoundWithInfinity::FiniteClosed(0.into())
            < VdBsqLitnumUpperBoundWithInfinity::PositiveInfinity
    );
}

fn litnum_lower_bound_with_infinity_ord_works() {
    assert!(
        VdBsqLitnumLowerBoundWithInfinity::NegativeInfinity
            < VdBsqLitnumLowerBoundWithInfinity::Finite(1.into())
    );
}

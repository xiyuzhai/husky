use super::*;

pub(super) fn calc_sum_trivial_bounds<'db, 'sess>(
    sum: VdBsqSumTerm<'sess>,
    elr: &mut Elr<'db, 'sess>,
) -> Vec<VdBsqHypothesisIdx<'sess>> {
    vec![]
}

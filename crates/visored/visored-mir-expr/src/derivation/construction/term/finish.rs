use super::*;

pub(super) fn check_non_trivial_finish<'db, Src>(
    lhs: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    rhs: VdMirExprIdx,
    src_nf: VdMirTermDerivationIdx,
    dst_nf: VdMirTermDerivationIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    assert_eq!(signature.separator(), VdMirBaseChainingSeparator::IFF);
    todo!()
}

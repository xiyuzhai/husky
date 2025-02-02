use super::*;
use crate::{
    derivation::VdMirDerivationIdx,
    expr::VdMirExprData,
    helpers::compare::{assert_deep_eq, vd_mir_expr_deep_eq},
    hypothesis::constructor::expr::ds,
};
use coercion::{
    VdMirBinaryOprCoercion, VdMirCoercion, VdMirPrefixOprCoercion, VdMirSeparatorCoercion,
};
use hypothesis::VdMirHypothesisIdx;
use term::VdMirTermDerivationIdx;
use visored_mir_opr::separator::{
    chaining::{
        VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
    },
    VdMirBaseSeparator,
};
use visored_signature::signature::separator::base::{
    chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
};
use visored_term::term::literal::VdLiteral;

#[derive(Debug, PartialEq, Eq, strum::IntoStaticStr)]
pub enum VdMirLitnumBoundDerivationConstruction {
    Finish {
        a_opr: VdMirBaseComparisonSeparator,
        b_opr: VdMirBaseComparisonSeparator,
        src: VdMirHypothesisIdx,
        src_nf_dn: VdMirLitnumBoundDerivationIdx,
        dst_nf_dn: VdMirLitnumBoundDerivationIdx,
        src_nf_and_dst_nf_equivalence_dn: VdMirTermDerivationIdx,
        src_sub_coercion: VdMirBinaryOprCoercion,
        dst_sub_coercion: VdMirBinaryOprCoercion,
        src_cmp_coercion: VdMirSeparatorCoercion,
        dst_cmp_coercion: VdMirSeparatorCoercion,
    },
    Normalize {
        separator: VdMirBaseComparisonSeparator,
    },
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct VdMirLitnumBoundDerivationIdx(VdMirDerivationIdx);

impl std::ops::Deref for VdMirLitnumBoundDerivationIdx {
    type Target = VdMirDerivationIdx;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<'db, Src> VdMirHypothesisConstructor<'db, Src> {
    pub fn alloc_litnum_bound_derivation(
        &mut self,
        prop: VdMirExprIdx,
        construction: VdMirLitnumBoundDerivationConstruction,
    ) -> VdMirLitnumBoundDerivationIdx {
        let idx = self.alloc_derivation(prop, construction.into());
        VdMirLitnumBoundDerivationIdx(idx)
    }
}

impl VdMirLitnumBoundDerivationConstruction {
    pub fn check<'db, Src>(
        &self,
        prop: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, Src>,
    ) {
        match *self {
            VdMirLitnumBoundDerivationConstruction::Normalize { separator } => {
                check_normalize(prop, separator, hc)
            }
            VdMirLitnumBoundDerivationConstruction::Finish {
                a_opr,
                b_opr,
                src,
                src_nf_dn,
                dst_nf_dn,
                src_nf_and_dst_nf_equivalence_dn,
                src_sub_coercion,
                dst_sub_coercion,
                src_cmp_coercion,
                dst_cmp_coercion,
            } => check_finish(
                prop,
                src,
                src_nf_dn,
                dst_nf_dn,
                src_nf_and_dst_nf_equivalence_dn,
                hc,
            ),
        }
    }
}

fn check_normalize<'db, Src>(
    prop: VdMirExprIdx,
    separator: VdMirBaseComparisonSeparator,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    // todo!()
}

fn check_finish<'db, Src>(
    prop: VdMirExprIdx,
    src: VdMirHypothesisIdx,
    src_nf: VdMirLitnumBoundDerivationIdx,
    dst_nf: VdMirLitnumBoundDerivationIdx,
    src_nf_and_dst_nf_equivalence: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    // todo!()
}

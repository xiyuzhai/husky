use super::*;
use crate::{
    derivation::VdMirDerivationIdx,
    expr::VdMirExprData,
    helpers::compare::{assert_deep_eq, vd_mir_expr_deep_eq},
    hypothesis::constructor::expr::ds,
};
use coercion::{VdMirCoercion, VdMirPrefixOprCoercion, VdMirSeparatorCoercion};
use hypothesis::VdMirHypothesisIdx;
use term::VdMirTermDerivationIdx;
use visored_mir_opr::separator::chaining::{
    VdMirBaseChainingSeparator, VdMirBaseComparisonSeparator, VdMirBaseRelationSeparator,
};
use visored_signature::signature::separator::base::{
    chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
};
use visored_term::term::literal::VdLiteral;

#[derive(Debug, PartialEq, Eq, strum::IntoStaticStr)]
pub enum VdMirLitnumBoundDerivationConstruction {
    Finish {
        src_nf_and_dst_nf_equivalence: VdMirTermDerivationIdx,
    },
}

impl VdMirLitnumBoundDerivationConstruction {
    pub fn check<'db, Src>(
        &self,
        prop: VdMirExprIdx,
        hc: &mut VdMirHypothesisConstructor<'db, Src>,
    ) {
        match *self {
            VdMirLitnumBoundDerivationConstruction::Finish {
                src_nf_and_dst_nf_equivalence,
            } => check_finish(prop, src_nf_and_dst_nf_equivalence, hc),
        }
    }
}

fn check_finish<'db, Src>(
    prop: VdMirExprIdx,
    src_nf_and_dst_nf_equivalence: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    // todo!()
}

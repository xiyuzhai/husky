use super::*;
use crate::expr::application::VdMirFunc;
use visored_mir_opr::opr::prefix::VdMirBasePrefixOpr;
use visored_opr::opr::prefix::VdBasePrefixOpr;
use visored_signature::signature::prefix_opr::VdBasePrefixOprSignature;
use visored_term::term::literal::{VdLiteral, VdLiteralData};

/// derive `-a => term` from `(-1) * a => term`
pub(super) fn check_neg_eqs_minus_one_mul<'db, Src>(
    prop: VdMirExprIdx,
    minus_one_mul_a_nf: VdMirTermDerivationIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (minus_a => term) = prop, hc);
    ds!(let (-a) = minus_a, hc);
    ds!(let (minus_one_mul_a => term1) = minus_one_mul_a_nf.prop(hc), hc);
    ds!(let (minus_one * a1) = minus_one_mul_a, hc);
    assert_deep_eq!(term, term1, hc);
    assert_deep_eq!(a1, a, hc);
}

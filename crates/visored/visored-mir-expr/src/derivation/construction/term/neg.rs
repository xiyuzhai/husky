use super::*;
use crate::expr::application::VdMirFunc;
use visored_mir_opr::opr::prefix::VdMirBasePrefixOpr;
use visored_opr::opr::prefix::VdBasePrefixOpr;
use visored_signature::signature::prefix_opr::VdBasePrefixOprSignature;
use visored_term::term::literal::{VdLiteral, VdLiteralData};

pub(super) fn check_neg_literal<'db, Src>(
    leader: VdMirExprIdx,
    signature: VdBaseChainingSeparatorSignature,
    follower: VdMirExprIdx,
    hc: &VdMirHypothesisConstructor<'db, Src>,
) {
    let VdMirExprData::Application {
        function: VdMirFunc::NormalBasePrefixOpr(signature),
        arguments,
    } = *hc.expr(leader).data()
    else {
        unreachable!(
            "leader is not a literal, but a `{:?}`",
            hc.expr(leader).data()
        )
    };
    assert_eq!(signature.opr(), VdMirBasePrefixOpr::RING_NEG);
    assert_eq!(arguments.len(), 1);
    let arg = arguments.first().unwrap();
    let VdMirExprData::Literal(arg) = *hc.expr(arg).data() else {
        unreachable!("arg is not a literal, but a `{:?}`", hc.expr(arg).data())
    };
    let VdMirExprData::Literal(follower) = *hc.expr(follower).data() else {
        unreachable!(
            "follower is not a literal, but a `{:?}`",
            hc.expr(follower).data()
        )
    };
    match *arg.data() {
        VdLiteralData::Int128(arg) => {
            if let Some(neg) = arg.checked_neg() {
                assert_eq!(follower.data(), &VdLiteralData::Int128(neg));
            } else {
                todo!()
            }
        }
        VdLiteralData::BigInt(ref arg) => todo!(),
        VdLiteralData::Float(_) => todo!(),
        VdLiteralData::SpecialConstant(vd_special_constant) => todo!(),
    }
}

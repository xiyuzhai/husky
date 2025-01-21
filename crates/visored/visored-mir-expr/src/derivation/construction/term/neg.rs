use super::*;
use crate::expr::application::VdMirFunc;
use visored_mir_opr::opr::prefix::VdMirBasePrefixOpr;
use visored_opr::opr::prefix::VdBasePrefixOpr;
use visored_signature::signature::prefix_opr::VdBasePrefixOprSignature;
use visored_term::term::literal::{VdLiteral, VdLiteralData};

pub(super) fn check_neg_literal<'db, Src>(
    prop: VdMirExprIdx,
    hc: &mut VdMirHypothesisConstructor<'db, Src>,
) {
    ds!(let (expr => term) = prop, hc);
    let VdMirExprData::Application {
        function: VdMirFunc::NormalBasePrefixOpr(signature),
        arguments,
    } = *hc.expr(expr).data()
    else {
        unreachable!(
            "leader is not a literal, but a `{:?}`",
            hc.expr(expr).data()
        )
    };
    assert_eq!(signature.opr(), VdMirBasePrefixOpr::RING_NEG);
    assert_eq!(arguments.len(), 1);
    let arg = arguments.first().unwrap();
    let VdMirExprData::Literal(arg) = *hc.expr(arg).data() else {
        unreachable!("arg is not a literal, but a `{:?}`", hc.expr(arg).data())
    };
    let VdMirExprData::Literal(term) = *hc.expr(term).data() else {
        unreachable!(
            "follower is not a literal, but a `{:?}`",
            hc.expr(term).data()
        )
    };
    match *arg.data() {
        VdLiteralData::Int(ref arg) => {
            assert_eq!(term.data(), &VdLiteralData::Int(-arg));
        }
        VdLiteralData::Frac(_) => todo!(),
    }
}

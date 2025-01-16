use super::*;
use visored_mir_opr::separator::chaining::VdMirBaseComparisonSeparator;

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct VdBaseComparisonSignature {
    instantiation: VdInstantiation,
    opr: VdMirBaseComparisonSeparator,
    item_ty: VdType,
    expr_ty: VdType,
}

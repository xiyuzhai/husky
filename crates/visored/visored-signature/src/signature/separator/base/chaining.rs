use super::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord)]
pub struct VdBaseChainingSeparatorSignature {
    instantiation: VdInstantiation,
    // TODO: replace this with something more ethereal
    opr: VdMirBaseSeparator,
    item_ty: VdType,
    expr_ty: VdType,
}

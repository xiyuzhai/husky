use super::*;
use visored_term::ty::VdType;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VdMirPowCoercion {
    pub src_base_ty: VdType,
    pub src_exponent_ty: VdType,
    pub dst_base_ty: VdType,
    pub dst_exponent_ty: VdType,
}

impl VdMirPowCoercion {
    pub fn new(
        src_base_ty: VdType,
        src_exponent_ty: VdType,
        dst_base_ty: VdType,
        dst_exponent_ty: VdType,
    ) -> Self {
        Self {
            src_base_ty,
            src_exponent_ty,
            dst_base_ty,
            dst_exponent_ty,
        }
    }
}

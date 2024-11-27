use super::*;
use either::*;
use visored_signature::signature::{
    attach::VdPowerSignature, binary_opr::base::VdBaseBinaryOprSignature,
    prefix_opr::VdBasePrefixOprSignature, separator::base::VdBaseSeparatorSignature,
    sqrt::VdBaseSqrtSignature,
};
use visored_term::instantiation::VdInstantiation;

pub mod menu;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdMirFunc {
    NormalBasePrefixOpr(VdBasePrefixOprSignature),
    NormalBaseSeparator(VdBaseSeparatorSignature),
    NormalBaseBinaryOpr(VdBaseBinaryOprSignature),
    Power(VdPowerSignature),
    InSet,
    NormalBaseSqrt(VdBaseSqrtSignature),
    NormalBaseFrac(VdBaseBinaryOprSignature),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdMirFuncKey {
    NormalBasePrefixOpr(VdInstantiation),
    NormalBaseSeparator(VdInstantiation),
    NormalBaseBinaryOpr(VdInstantiation),
    InSet,
    Power(VdInstantiation),
    NormalBaseSqrt(VdInstantiation),
    NormalBaseFrac(VdInstantiation),
}

impl VdMirFunc {
    pub fn key_or_expr(self) -> Either<VdMirFuncKey, VdMirExprIdx> {
        match self {
            VdMirFunc::NormalBaseSeparator(signature) => {
                Left(VdMirFuncKey::NormalBaseSeparator(signature.instantiation()))
            }
            VdMirFunc::NormalBaseBinaryOpr(signature) => {
                Left(VdMirFuncKey::NormalBaseBinaryOpr(signature.instantiation()))
            }
            VdMirFunc::NormalBasePrefixOpr(signature) => {
                Left(VdMirFuncKey::NormalBasePrefixOpr(signature.instantiation()))
            }
            VdMirFunc::Power(signature) => Left(VdMirFuncKey::Power(signature.instantiation())),
            VdMirFunc::InSet => Left(VdMirFuncKey::InSet),
            VdMirFunc::NormalBaseSqrt(signature) => {
                Left(VdMirFuncKey::NormalBaseSqrt(signature.instantiation()))
            }
            VdMirFunc::NormalBaseFrac(signature) => {
                Left(VdMirFuncKey::NormalBaseFrac(signature.instantiation()))
            }
        }
    }
}

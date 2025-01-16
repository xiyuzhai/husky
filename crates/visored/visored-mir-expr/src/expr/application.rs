use super::*;
use either::*;
use visored_opr::precedence::VdPrecedence;
use visored_signature::signature::{
    attach::VdPowerSignature, binary_opr::base::VdBaseBinaryOprSignature,
    prefix_opr::VdBasePrefixOprSignature, separator::base::VdBaseSeparatorSignature,
    sqrt::VdBaseSqrtSignature,
};
use visored_term::instantiation::VdInstantiation;

pub mod menu;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VdMirFunc {
    NormalBasePrefixOpr(VdBasePrefixOprSignature),
    NormalBaseSeparator(VdBaseSeparatorSignature),
    NormalBaseBinaryOpr(VdBaseBinaryOprSignature),
    Power(VdPowerSignature),
    InSet,
    NormalBaseSqrt(VdBaseSqrtSignature),
    // TODO: expr as func
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdMirFuncKey {
    NormalBasePrefixOpr(VdInstantiation),
    NormalBaseSeparator(VdInstantiation),
    NormalBaseBinaryOpr(VdInstantiation),
    InSet,
    Power(VdInstantiation),
    NormalBaseSqrt(VdInstantiation),
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
        }
    }

    pub fn expr(self) -> Option<VdMirExprIdx> {
        self.key_or_expr().right()
    }

    pub fn outer_precedence(&self) -> VdPrecedence {
        match self {
            VdMirFunc::NormalBasePrefixOpr(signature) => signature.opr.precedence(),
            VdMirFunc::NormalBaseSeparator(signature) => signature.separator().precedence(),
            VdMirFunc::NormalBaseBinaryOpr(signature) => signature.opr.precedence(),
            VdMirFunc::Power(signature) => VdPrecedence::ATOM,
            VdMirFunc::InSet => todo!(),
            VdMirFunc::NormalBaseSqrt(signature) => VdPrecedence::ATOM,
        }
    }
}

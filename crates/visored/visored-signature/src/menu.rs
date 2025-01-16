use crate::signature::{
    attach::VdPowerSignature,
    binary_opr::base::VdBaseBinaryOprSignature,
    frac::VdBaseFracSignature,
    prefix_opr::VdBasePrefixOprSignature,
    separator::base::{
        chaining::VdBaseChainingSeparatorSignature, folding::VdBaseFoldingSeparatorSignature,
        VdBaseSeparatorSignature,
    },
    sqrt::VdBaseSqrtSignature,
};
use eterned::{db::EternerDb, memo};
use lazy_static::lazy_static;
use visored_mir_opr::opr::prefix::VdMirBasePrefixOpr;
use visored_term::{
    instantiation::{
        menu::{vd_instantiation_menu, VdInstantiationMenu},
        VdInstantiation,
    },
    menu::{vd_ty_menu, VdTypeMenu},
    ty::VdType,
};

#[derive(Debug, PartialEq, Eq)]
pub struct VdSignatureMenu {
    /// # prefix
    /// ## pos
    pub int_pos: VdBasePrefixOprSignature,
    pub rat_pos: VdBasePrefixOprSignature,
    pub real_pos: VdBasePrefixOprSignature,
    pub complex_pos: VdBasePrefixOprSignature,
    /// ## neg
    pub int_neg: VdBasePrefixOprSignature,
    pub rat_neg: VdBasePrefixOprSignature,
    pub real_neg: VdBasePrefixOprSignature,
    pub complex_neg: VdBasePrefixOprSignature,
    /// # binary
    /// ## sub
    pub int_sub: VdBaseBinaryOprSignature,
    pub rat_sub: VdBaseBinaryOprSignature,
    pub real_sub: VdBaseBinaryOprSignature,
    pub complex_sub: VdBaseBinaryOprSignature,
    /// ## div
    pub rat_div: VdBaseBinaryOprSignature,
    pub real_div: VdBaseBinaryOprSignature,
    pub complex_div: VdBaseBinaryOprSignature,
    /// # separators
    /// iff
    pub iff: VdBaseChainingSeparatorSignature,
    /// ## add
    pub nat_add: VdBaseFoldingSeparatorSignature,
    pub int_add: VdBaseFoldingSeparatorSignature,
    pub rat_add: VdBaseFoldingSeparatorSignature,
    pub real_add: VdBaseFoldingSeparatorSignature,
    pub complex_add: VdBaseFoldingSeparatorSignature,
    /// ## mul
    pub nat_mul: VdBaseFoldingSeparatorSignature,
    pub int_mul: VdBaseFoldingSeparatorSignature,
    pub rat_mul: VdBaseFoldingSeparatorSignature,
    pub real_mul: VdBaseFoldingSeparatorSignature,
    pub complex_mul: VdBaseFoldingSeparatorSignature,
    /// ## power
    pub nat_to_the_power_of_nat: VdPowerSignature,
    pub int_to_the_power_of_nat: VdPowerSignature,
    pub rat_to_the_power_of_nat: VdPowerSignature,
    pub real_to_the_power_of_nat: VdPowerSignature,
    pub complex_to_the_power_of_nat: VdPowerSignature,
    /// ## eq
    pub nat_eq: VdBaseChainingSeparatorSignature,
    pub int_eq: VdBaseChainingSeparatorSignature,
    pub rat_eq: VdBaseChainingSeparatorSignature,
    pub real_eq: VdBaseChainingSeparatorSignature,
    pub complex_eq: VdBaseChainingSeparatorSignature,
    /// ## ne
    pub nat_ne: VdBaseChainingSeparatorSignature,
    pub int_ne: VdBaseChainingSeparatorSignature,
    pub rat_ne: VdBaseChainingSeparatorSignature,
    pub real_ne: VdBaseChainingSeparatorSignature,
    pub complex_ne: VdBaseChainingSeparatorSignature,
    /// ## lt
    pub nat_lt: VdBaseChainingSeparatorSignature,
    pub int_lt: VdBaseChainingSeparatorSignature,
    pub rat_lt: VdBaseChainingSeparatorSignature,
    pub real_lt: VdBaseChainingSeparatorSignature,
    /// ## gt
    pub nat_gt: VdBaseChainingSeparatorSignature,
    pub int_gt: VdBaseChainingSeparatorSignature,
    pub rat_gt: VdBaseChainingSeparatorSignature,
    pub real_gt: VdBaseChainingSeparatorSignature,
    /// ## le
    pub nat_le: VdBaseChainingSeparatorSignature,
    pub int_le: VdBaseChainingSeparatorSignature,
    pub rat_le: VdBaseChainingSeparatorSignature,
    pub real_le: VdBaseChainingSeparatorSignature,
    /// ## ge
    pub nat_ge: VdBaseChainingSeparatorSignature,
    pub int_ge: VdBaseChainingSeparatorSignature,
    pub rat_ge: VdBaseChainingSeparatorSignature,
    pub real_ge: VdBaseChainingSeparatorSignature,
    // # sqrt
    pub real_sqrt: VdBaseSqrtSignature,
}

impl VdSignatureMenu {
    fn new(db: &EternerDb) -> Self {
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            set,
            prop,
        } = *vd_ty_menu(db);
        let VdInstantiationMenu {
            int_pos,
            rat_pos,
            real_pos,
            complex_pos,
            int_neg,
            rat_neg,
            real_neg,
            complex_neg,
            int_sub,
            rat_sub,
            real_sub,
            complex_sub,
            rat_div,
            real_div,
            complex_div,
            iff,
            nat_add,
            int_add,
            rat_add,
            real_add,
            complex_add,
            nat_mul,
            int_mul,
            rat_mul,
            real_mul,
            complex_mul,
            nat_to_the_power_of_nat,
            int_to_the_power_of_nat,
            rat_to_the_power_of_nat,
            real_to_the_power_of_nat,
            complex_to_the_power_of_nat,
            nat_eq,
            int_eq,
            rat_eq,
            real_eq,
            complex_eq,
            nat_ne,
            int_ne,
            rat_ne,
            real_ne,
            complex_ne,
            nat_lt,
            int_lt,
            rat_lt,
            real_lt,
            nat_gt,
            int_gt,
            rat_gt,
            real_gt,
            nat_le,
            int_le,
            rat_le,
            real_le,
            nat_ge,
            int_ge,
            rat_ge,
            real_ge,
            real_sqrt,
        } = *vd_instantiation_menu(db);
        let pre = VdBasePrefixOprSignature::new;
        let bin = VdBaseBinaryOprSignature::new;
        let fsep = |instantiation: VdInstantiation, item_ty: VdType, expr_ty: VdType| {
            match VdBaseSeparatorSignature::new(instantiation, item_ty, expr_ty) {
                VdBaseSeparatorSignature::Chaining(_) => unreachable!(),
                VdBaseSeparatorSignature::Folding(signature) => signature,
            }
        };
        let csep = |instantiation: VdInstantiation, item_ty: VdType, expr_ty: VdType| {
            match VdBaseSeparatorSignature::new(instantiation, item_ty, expr_ty) {
                VdBaseSeparatorSignature::Chaining(signature) => signature,
                VdBaseSeparatorSignature::Folding(_) => unreachable!(),
            }
        };
        let pow = VdPowerSignature::new;
        Self {
            // # prefix operators
            // ## pos
            int_pos: pre(int_pos, int, int),
            rat_pos: pre(rat_pos, rat, rat),
            real_pos: pre(real_pos, real, real),
            complex_pos: pre(complex_pos, complex, complex),
            // ## neg
            int_neg: pre(int_neg, int, int),
            rat_neg: pre(rat_neg, rat, rat),
            real_neg: pre(real_neg, real, real),
            complex_neg: pre(complex_neg, complex, complex),
            // # binary operators
            // ## sub
            int_sub: bin(int_sub, int, int, int),
            rat_sub: bin(rat_sub, rat, rat, rat),
            real_sub: bin(real_sub, real, real, real),
            complex_sub: bin(complex_sub, complex, complex, complex),
            // ## div
            // TODO: use nzrat, i.e., non-zero rational numbers
            rat_div: bin(rat_div, rat, rat, rat),
            // TODO: use nzreal, i.e., non-zero real numbers
            real_div: bin(real_div, real, real, real),
            // TODO: use nzcomplex, i.e., non-zero complex numbers
            complex_div: bin(complex_div, complex, complex, complex),
            // # separators
            // ## iff
            iff: csep(iff, prop, prop),
            // ## add
            nat_add: fsep(nat_add, nat, nat),
            int_add: fsep(int_add, int, int),
            rat_add: fsep(rat_add, rat, rat),
            real_add: fsep(real_add, real, real),
            complex_add: fsep(complex_add, complex, complex),
            // ## mul
            nat_mul: fsep(nat_mul, nat, nat),
            int_mul: fsep(int_mul, int, int),
            rat_mul: fsep(rat_mul, rat, rat),
            real_mul: fsep(real_mul, real, real),
            complex_mul: fsep(complex_mul, complex, complex),
            // ## eq
            nat_eq: csep(nat_eq, nat, prop),
            int_eq: csep(int_eq, int, prop),
            rat_eq: csep(rat_eq, rat, prop),
            real_eq: csep(real_eq, real, prop),
            complex_eq: csep(complex_eq, complex, prop),
            // ## ne
            nat_ne: csep(nat_ne, nat, prop),
            int_ne: csep(int_ne, int, prop),
            rat_ne: csep(rat_ne, rat, prop),
            real_ne: csep(real_ne, real, prop),
            complex_ne: csep(complex_ne, complex, prop),
            // ## lt
            nat_lt: csep(nat_lt, nat, prop),
            int_lt: csep(int_lt, int, prop),
            rat_lt: csep(rat_lt, rat, prop),
            real_lt: csep(real_lt, real, prop),
            // ## gt
            nat_gt: csep(nat_gt, nat, prop),
            int_gt: csep(int_gt, int, prop),
            rat_gt: csep(rat_gt, rat, prop),
            real_gt: csep(real_gt, real, prop),
            // ## le
            nat_le: csep(nat_le, nat, prop),
            int_le: csep(int_le, int, prop),
            rat_le: csep(rat_le, rat, prop),
            real_le: csep(real_le, real, prop),
            // ## ge
            nat_ge: csep(nat_ge, nat, prop),
            int_ge: csep(int_ge, int, prop),
            rat_ge: csep(rat_ge, rat, prop),
            real_ge: csep(real_ge, real, prop),
            // # sqrt
            // TODO: use nnreal, i.e., non-negative real numbers
            real_sqrt: VdBaseSqrtSignature::new(real_sqrt, real, real),
            // # attach
            // ## power
            nat_to_the_power_of_nat: pow(nat_to_the_power_of_nat, nat, nat, nat),
            int_to_the_power_of_nat: pow(int_to_the_power_of_nat, int, nat, int),
            rat_to_the_power_of_nat: pow(rat_to_the_power_of_nat, rat, nat, rat),
            real_to_the_power_of_nat: pow(real_to_the_power_of_nat, real, nat, real),
            complex_to_the_power_of_nat: pow(complex_to_the_power_of_nat, complex, nat, complex),
        }
    }
}

#[memo(return_ref)]
pub fn vd_signature_menu(db: &EternerDb) -> VdSignatureMenu {
    VdSignatureMenu::new(db)
}

use crate::signature::{
    attach::VdPowerSignature, binary_opr::base::VdBaseBinaryOprSignature,
    frac::VdBaseFracSignature, prefix_opr::VdBasePrefixOprSignature,
    separator::base::VdBaseSeparatorSignature, sqrt::VdBaseSqrtSignature,
};
use lazy_static::lazy_static;
use visored_term::{
    instantiation::menu::{VdInstantiationMenu, VD_INSTANTIATION_MENU},
    menu::{VdTypeMenu, VD_TYPE_MENU},
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
    /// ## add
    pub nat_add: VdBaseSeparatorSignature,
    pub int_add: VdBaseSeparatorSignature,
    pub rat_add: VdBaseSeparatorSignature,
    pub real_add: VdBaseSeparatorSignature,
    pub complex_add: VdBaseSeparatorSignature,
    /// ## mul
    pub nat_mul: VdBaseSeparatorSignature,
    pub int_mul: VdBaseSeparatorSignature,
    pub rat_mul: VdBaseSeparatorSignature,
    pub real_mul: VdBaseSeparatorSignature,
    pub complex_mul: VdBaseSeparatorSignature,
    /// ## power
    pub nat_to_the_power_of_nat: VdPowerSignature,
    pub int_to_the_power_of_nat: VdPowerSignature,
    pub rat_to_the_power_of_nat: VdPowerSignature,
    pub real_to_the_power_of_nat: VdPowerSignature,
    pub complex_to_the_power_of_nat: VdPowerSignature,
    /// ## eq
    pub nat_eq: VdBaseSeparatorSignature,
    pub int_eq: VdBaseSeparatorSignature,
    pub rat_eq: VdBaseSeparatorSignature,
    pub real_eq: VdBaseSeparatorSignature,
    pub complex_eq: VdBaseSeparatorSignature,
    /// ## ne
    pub nat_ne: VdBaseSeparatorSignature,
    pub int_ne: VdBaseSeparatorSignature,
    pub rat_ne: VdBaseSeparatorSignature,
    pub real_ne: VdBaseSeparatorSignature,
    pub complex_ne: VdBaseSeparatorSignature,
    /// ## lt
    pub nat_lt: VdBaseSeparatorSignature,
    pub int_lt: VdBaseSeparatorSignature,
    pub rat_lt: VdBaseSeparatorSignature,
    pub real_lt: VdBaseSeparatorSignature,
    /// ## gt
    pub nat_gt: VdBaseSeparatorSignature,
    pub int_gt: VdBaseSeparatorSignature,
    pub rat_gt: VdBaseSeparatorSignature,
    pub real_gt: VdBaseSeparatorSignature,
    /// ## le
    pub nat_le: VdBaseSeparatorSignature,
    pub int_le: VdBaseSeparatorSignature,
    pub rat_le: VdBaseSeparatorSignature,
    pub real_le: VdBaseSeparatorSignature,
    /// ## ge
    pub nat_ge: VdBaseSeparatorSignature,
    pub int_ge: VdBaseSeparatorSignature,
    pub rat_ge: VdBaseSeparatorSignature,
    pub real_ge: VdBaseSeparatorSignature,
    // # sqrt
    pub real_sqrt: VdBaseSqrtSignature,
}

impl VdSignatureMenu {
    fn new() -> Self {
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            set,
            prop,
        } = *VD_TYPE_MENU;
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
        } = *VD_INSTANTIATION_MENU;
        let pre = VdBasePrefixOprSignature::new;
        let bin = VdBaseBinaryOprSignature::new;
        let sep = VdBaseSeparatorSignature::new;
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
            // ## add
            nat_add: sep(nat_add, nat, nat),
            int_add: sep(int_add, int, int),
            rat_add: sep(rat_add, rat, rat),
            real_add: sep(real_add, real, real),
            complex_add: sep(complex_add, complex, complex),
            // ## mul
            nat_mul: sep(nat_mul, nat, nat),
            int_mul: sep(int_mul, int, int),
            rat_mul: sep(rat_mul, rat, rat),
            real_mul: sep(real_mul, real, real),
            complex_mul: sep(complex_mul, complex, complex),
            // ## eq
            nat_eq: sep(nat_eq, nat, prop),
            int_eq: sep(int_eq, int, prop),
            rat_eq: sep(rat_eq, rat, prop),
            real_eq: sep(real_eq, real, prop),
            complex_eq: sep(complex_eq, complex, prop),
            // ## ne
            nat_ne: sep(nat_ne, nat, prop),
            int_ne: sep(int_ne, int, prop),
            rat_ne: sep(rat_ne, rat, prop),
            real_ne: sep(real_ne, real, prop),
            complex_ne: sep(complex_ne, complex, prop),
            // ## lt
            nat_lt: sep(nat_lt, nat, prop),
            int_lt: sep(int_lt, int, prop),
            rat_lt: sep(rat_lt, rat, prop),
            real_lt: sep(real_lt, real, prop),
            // ## gt
            nat_gt: sep(nat_gt, nat, prop),
            int_gt: sep(int_gt, int, prop),
            rat_gt: sep(rat_gt, rat, prop),
            real_gt: sep(real_gt, real, prop),
            // ## le
            nat_le: sep(nat_le, nat, prop),
            int_le: sep(int_le, int, prop),
            rat_le: sep(rat_le, rat, prop),
            real_le: sep(real_le, real, prop),
            // ## ge
            nat_ge: sep(nat_ge, nat, prop),
            int_ge: sep(int_ge, int, prop),
            rat_ge: sep(rat_ge, rat, prop),
            real_ge: sep(real_ge, real, prop),
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

lazy_static! {
    pub static ref vd_signature_menu: VdSignatureMenu = VdSignatureMenu::new();
}

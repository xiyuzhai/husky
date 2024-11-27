use super::{LnMirExprData, LnMirExprIdx};
use crate::builder::LnMirExprBuilder;
use lazy_static::lazy_static;
use lean_entity_path::{
    menu::{ln_item_path_menu, LnItemPathMenu},
    LnItemPath,
};
use lean_opr::{
    opr::{binary::LnBinaryOpr, prefix::LnPrefixOpr, suffix::LnSuffixOpr},
    precedence::LnPrecedence,
};
use lean_term::instantiation::{
    menu::{ln_instantiation_menu, LnInstantiationMenu},
    LnInstantiation,
};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LnMirFunc {
    PrefixOpr {
        opr: LnPrefixOpr,
        instantiation: LnInstantiation,
    },
    BinaryOpr {
        opr: LnBinaryOpr,
        instantiation: LnInstantiation,
    },
    SuffixOpr {
        opr: LnSuffixOpr,
        instantiation: LnInstantiation,
    },
    Expr(LnMirExprIdx),
    // ad hoc
    InSet,
}

impl LnMirFunc {
    pub fn expr(self) -> Option<LnMirExprIdx> {
        match self {
            LnMirFunc::Expr(expr) => Some(expr),
            _ => None,
        }
    }

    pub(crate) fn outer_precedence(self) -> LnPrecedence {
        match self {
            LnMirFunc::PrefixOpr { opr, instantiation } => opr.outer_precedence(),
            LnMirFunc::BinaryOpr { opr, instantiation } => opr.outer_precedence(),
            LnMirFunc::SuffixOpr { opr, instantiation } => opr.outer_precedence(),
            LnMirFunc::Expr(expr) => LnPrecedence::Application,
            LnMirFunc::InSet => LnPrecedence::Application,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum LnMirFuncKey {
    ItemPath(LnItemPath),
    PrefixOpr {
        opr: LnPrefixOpr,
        instantiation: LnInstantiation,
    },
    BinaryOpr {
        opr: LnBinaryOpr,
        instantiation: LnInstantiation,
    },
    SuffixOpr {
        opr: LnSuffixOpr,
        instantiation: LnInstantiation,
    },
}

impl LnMirExprBuilder {
    pub fn build_func_from_key(&mut self, key: LnMirFuncKey) -> LnMirFunc {
        match key {
            LnMirFuncKey::ItemPath(item_path) => {
                LnMirFunc::Expr(self.alloc_expr(LnMirExprData::ItemPath(item_path)))
            }
            LnMirFuncKey::BinaryOpr { opr, instantiation } => {
                LnMirFunc::BinaryOpr { opr, instantiation }
            }
            LnMirFuncKey::PrefixOpr { opr, instantiation } => {
                LnMirFunc::PrefixOpr { opr, instantiation }
            }
            LnMirFuncKey::SuffixOpr { opr, instantiation } => {
                LnMirFunc::SuffixOpr { opr, instantiation }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct LnMirFuncKeyMenu {
    pub int_pos: LnMirFuncKey,
    pub rat_pos: LnMirFuncKey,
    pub real_pos: LnMirFuncKey,
    pub complex_pos: LnMirFuncKey,
    pub int_neg: LnMirFuncKey,
    pub rat_neg: LnMirFuncKey,
    pub real_neg: LnMirFuncKey,
    pub complex_neg: LnMirFuncKey,
    pub int_sub: LnMirFuncKey,
    pub rat_sub: LnMirFuncKey,
    pub real_sub: LnMirFuncKey,
    pub complex_sub: LnMirFuncKey,
    pub rat_div: LnMirFuncKey,
    pub real_div: LnMirFuncKey,
    pub complex_div: LnMirFuncKey,
    pub nat_add: LnMirFuncKey,
    pub int_add: LnMirFuncKey,
    pub rat_add: LnMirFuncKey,
    pub real_add: LnMirFuncKey,
    pub complex_add: LnMirFuncKey,
    pub nat_mul: LnMirFuncKey,
    pub int_mul: LnMirFuncKey,
    pub rat_mul: LnMirFuncKey,
    pub real_mul: LnMirFuncKey,
    pub complex_mul: LnMirFuncKey,
    pub nat_to_the_power_of_nat: LnMirFuncKey,
    pub int_to_the_power_of_nat: LnMirFuncKey,
    pub rat_to_the_power_of_nat: LnMirFuncKey,
    pub real_to_the_power_of_nat: LnMirFuncKey,
    pub complex_to_the_power_of_nat: LnMirFuncKey,
    pub nat_eq: LnMirFuncKey,
    pub int_eq: LnMirFuncKey,
    pub rat_eq: LnMirFuncKey,
    pub real_eq: LnMirFuncKey,
    pub complex_eq: LnMirFuncKey,
    pub nat_ne: LnMirFuncKey,
    pub int_ne: LnMirFuncKey,
    pub rat_ne: LnMirFuncKey,
    pub real_ne: LnMirFuncKey,
    pub complex_ne: LnMirFuncKey,
    pub nat_lt: LnMirFuncKey,
    pub int_lt: LnMirFuncKey,
    pub rat_lt: LnMirFuncKey,
    pub real_lt: LnMirFuncKey,
    pub nat_gt: LnMirFuncKey,
    pub int_gt: LnMirFuncKey,
    pub rat_gt: LnMirFuncKey,
    pub real_gt: LnMirFuncKey,
    pub nat_le: LnMirFuncKey,
    pub int_le: LnMirFuncKey,
    pub rat_le: LnMirFuncKey,
    pub real_le: LnMirFuncKey,
    pub nat_ge: LnMirFuncKey,
    pub int_ge: LnMirFuncKey,
    pub rat_ge: LnMirFuncKey,
    pub real_ge: LnMirFuncKey,
    pub real_sqrt: LnMirFuncKey,
}

impl LnMirFuncKeyMenu {
    pub fn new() -> Self {
        use LnBinaryOpr::*;
        use LnPrefixOpr::*;

        let LnItemPathMenu { real_sqrt, .. } = *ln_item_path_menu;
        let LnInstantiationMenu {
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
        } = *ln_instantiation_menu;
        let i = |instantiation| LnMirFuncKey::ItemPath(instantiation);
        let p = |opr, instantiation| LnMirFuncKey::PrefixOpr { opr, instantiation };
        let b = |opr, instantiation| LnMirFuncKey::BinaryOpr { opr, instantiation };
        Self {
            int_pos: p(Pos, int_pos),
            rat_pos: p(Pos, rat_pos),
            real_pos: p(Pos, real_pos),
            complex_pos: p(Pos, complex_pos),
            int_neg: p(Neg, int_neg),
            rat_neg: p(Neg, rat_neg),
            real_neg: p(Neg, real_neg),
            complex_neg: p(Neg, complex_neg),
            int_sub: b(Sub, int_sub),
            rat_sub: b(Sub, rat_sub),
            real_sub: b(Sub, real_sub),
            complex_sub: b(Sub, complex_sub),
            rat_div: b(Div, rat_div),
            real_div: b(Div, real_div),
            complex_div: b(Div, complex_div),
            nat_add: b(Add, nat_add),
            int_add: b(Add, int_add),
            rat_add: b(Add, rat_add),
            real_add: b(Add, real_add),
            complex_add: b(Add, complex_add),
            nat_mul: b(Mul, nat_mul),
            int_mul: b(Mul, int_mul),
            rat_mul: b(Mul, rat_mul),
            real_mul: b(Mul, real_mul),
            complex_mul: b(Mul, complex_mul),
            nat_to_the_power_of_nat: b(Pow, nat_to_the_power_of_nat),
            int_to_the_power_of_nat: b(Pow, int_to_the_power_of_nat),
            rat_to_the_power_of_nat: b(Pow, rat_to_the_power_of_nat),
            real_to_the_power_of_nat: b(Pow, real_to_the_power_of_nat),
            complex_to_the_power_of_nat: b(Pow, complex_to_the_power_of_nat),
            nat_eq: b(Eq, nat_eq),
            int_eq: b(Eq, int_eq),
            rat_eq: b(Eq, rat_eq),
            real_eq: b(Eq, real_eq),
            complex_eq: b(Eq, complex_eq),
            nat_ne: b(Ne, nat_ne),
            int_ne: b(Ne, int_ne),
            rat_ne: b(Ne, rat_ne),
            real_ne: b(Ne, real_ne),
            complex_ne: b(Ne, complex_ne),
            nat_lt: b(Lt, nat_lt),
            int_lt: b(Lt, int_lt),
            rat_lt: b(Lt, rat_lt),
            real_lt: b(Lt, real_lt),
            nat_gt: b(Gt, nat_gt),
            int_gt: b(Gt, int_gt),
            rat_gt: b(Gt, rat_gt),
            real_gt: b(Gt, real_gt),
            nat_le: b(Le, nat_le),
            int_le: b(Le, int_le),
            rat_le: b(Le, rat_le),
            real_le: b(Le, real_le),
            nat_ge: b(Ge, nat_ge),
            int_ge: b(Ge, int_ge),
            rat_ge: b(Ge, rat_ge),
            real_ge: b(Ge, real_ge),
            real_sqrt: i(real_sqrt),
        }
    }
}

lazy_static! {
    pub static ref ln_mir_func_key_menu: LnMirFuncKeyMenu = LnMirFuncKeyMenu::new();
}

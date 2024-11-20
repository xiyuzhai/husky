use super::*;
use crate::{
    menu::{vd_ty_menu, VdTypeMenu},
    term::menu::{vd_term_menu, VdTermMenu},
};
use smallvec::{smallvec, SmallVec};
use visored_item_path::menu::{vd_item_path_menu, VdItemPathMenu};

#[derive(Debug, PartialEq, Eq)]
pub struct VdInstantiationMenu {
    /// # prefix
    /// ## pos
    pub int_pos: VdInstantiation,
    pub rat_pos: VdInstantiation,
    pub real_pos: VdInstantiation,
    pub complex_pos: VdInstantiation,
    /// ## neg
    pub int_neg: VdInstantiation,
    pub rat_neg: VdInstantiation,
    pub real_neg: VdInstantiation,
    pub complex_neg: VdInstantiation,
    /// # binary operators
    /// ## sub
    pub int_sub: VdInstantiation,
    pub rat_sub: VdInstantiation,
    pub real_sub: VdInstantiation,
    pub complex_sub: VdInstantiation,
    /// ## div
    pub rat_div: VdInstantiation,
    pub real_div: VdInstantiation,
    pub complex_div: VdInstantiation,
    /// # separators
    /// ## add
    pub nat_add: VdInstantiation,
    pub int_add: VdInstantiation,
    pub rat_add: VdInstantiation,
    pub real_add: VdInstantiation,
    pub complex_add: VdInstantiation,
    /// ## mul
    pub nat_mul: VdInstantiation,
    pub int_mul: VdInstantiation,
    pub rat_mul: VdInstantiation,
    pub real_mul: VdInstantiation,
    pub complex_mul: VdInstantiation,
    /// ## power
    pub nat_to_the_power_of_nat: VdInstantiation,
    pub int_to_the_power_of_nat: VdInstantiation,
    pub rat_to_the_power_of_nat: VdInstantiation,
    pub real_to_the_power_of_nat: VdInstantiation,
    pub complex_to_the_power_of_nat: VdInstantiation,
    /// ## eq
    pub nat_eq: VdInstantiation,
    pub int_eq: VdInstantiation,
    pub rat_eq: VdInstantiation,
    pub real_eq: VdInstantiation,
    pub complex_eq: VdInstantiation,
    /// ## ne
    pub nat_ne: VdInstantiation,
    pub int_ne: VdInstantiation,
    pub rat_ne: VdInstantiation,
    pub real_ne: VdInstantiation,
    pub complex_ne: VdInstantiation,
    /// ## lt
    pub nat_lt: VdInstantiation,
    pub int_lt: VdInstantiation,
    pub rat_lt: VdInstantiation,
    pub real_lt: VdInstantiation,
    /// ## gt
    pub nat_gt: VdInstantiation,
    pub int_gt: VdInstantiation,
    pub rat_gt: VdInstantiation,
    pub real_gt: VdInstantiation,
    /// ## le
    pub nat_le: VdInstantiation,
    pub int_le: VdInstantiation,
    pub rat_le: VdInstantiation,
    pub real_le: VdInstantiation,
    /// ## ge
    pub nat_ge: VdInstantiation,
    pub int_ge: VdInstantiation,
    pub rat_ge: VdInstantiation,
    pub real_ge: VdInstantiation,
    /// # sqrt
    pub real_sqrt: VdInstantiation,
}

impl VdInstantiationMenu {
    pub fn new(db: &salsa::Db) -> Self {
        let VdItemPathMenu {
            set,
            prop,
            nat,
            rat,
            int,
            real,
            complex,
            sin,
            cos,
            group,
            ring,
            group_mul,
            abelian_group_add,
            ring_add,
            ring_mul,
            ring_power,
            ring_pos,
            ring_neg,
            field_div,
            real_sqrt,
            eq,
            ne,
            lt,
            gt,
            le,
            ge,
        } = *vd_item_path_menu(db);
        let VdTermMenu {
            zero,
            one,
            two,
            nat,
            int,
            rat,
            real,
            complex,
        } = *vd_term_menu(db);
        macro_rules! ins{
            ($db: expr, $path: expr $(, $args: expr)*) => {
                VdInstantiation::new($db, $path.into(), smallvec![$($args),*])
            };
        }
        // # prefix
        // ## pos
        let int_pos = ins!(db, ring_pos, int);
        let rat_pos = ins!(db, ring_pos, rat);
        let real_pos = ins!(db, ring_pos, real);
        let complex_pos = ins!(db, ring_pos, complex);
        // ## neg
        let int_neg = ins!(db, ring_neg, int);
        let rat_neg = ins!(db, ring_neg, rat);
        let real_neg = ins!(db, ring_neg, real);
        let complex_neg = ins!(db, ring_neg, complex);
        // # binary operators
        // ## sub
        let int_sub = ins!(db, ring_add, int);
        let rat_sub = ins!(db, ring_add, rat);
        let real_sub = ins!(db, ring_add, real);
        let complex_sub = ins!(db, ring_add, complex);
        // ## div
        let rat_div = ins!(db, field_div, rat);
        let real_div = ins!(db, field_div, real);
        let complex_div = ins!(db, field_div, complex);
        // # separators
        // ## add
        let nat_add = ins!(db, ring_add, nat);
        let int_add = ins!(db, ring_add, int);
        let rat_add = ins!(db, ring_add, rat);
        let real_add = ins!(db, ring_add, real);
        let complex_add = ins!(db, ring_add, complex);
        // ## mul
        let nat_mul = ins!(db, ring_mul, nat);
        let int_mul = ins!(db, ring_mul, int);
        let rat_mul = ins!(db, ring_mul, rat);
        let real_mul = ins!(db, ring_mul, real);
        let complex_mul = ins!(db, ring_mul, complex);
        // ## power
        let nat_to_the_power_of_nat = ins!(db, ring_power, nat, nat);
        let int_to_the_power_of_nat = ins!(db, ring_power, int, nat);
        let rat_to_the_power_of_nat = ins!(db, ring_power, rat, nat);
        let real_to_the_power_of_nat = ins!(db, ring_power, real, nat);
        let complex_to_the_power_of_nat = ins!(db, ring_power, complex, nat);
        // ## eq
        let nat_eq = ins!(db, eq, nat);
        let int_eq = ins!(db, eq, int);
        let rat_eq = ins!(db, eq, rat);
        let real_eq = ins!(db, eq, real);
        let complex_eq = ins!(db, eq, complex);
        // ## ne
        let nat_ne = ins!(db, ne, nat);
        let int_ne = ins!(db, ne, int);
        let rat_ne = ins!(db, ne, rat);
        let real_ne = ins!(db, ne, real);
        let complex_ne = ins!(db, ne, complex);
        // ## lt
        let nat_lt = ins!(db, lt, nat);
        let int_lt = ins!(db, lt, int);
        let rat_lt = ins!(db, lt, rat);
        let real_lt = ins!(db, lt, real);
        // ## gt
        let nat_gt = ins!(db, gt, nat);
        let int_gt = ins!(db, gt, int);
        let rat_gt = ins!(db, gt, rat);
        let real_gt = ins!(db, gt, real);
        // ## le
        let nat_le = ins!(db, le, nat);
        let int_le = ins!(db, le, int);
        let rat_le = ins!(db, le, rat);
        let real_le = ins!(db, le, real);
        // ## ge
        let nat_ge = ins!(db, ge, nat);
        let int_ge = ins!(db, ge, int);
        let rat_ge = ins!(db, ge, rat);
        let real_ge = ins!(db, ge, real);
        // # sqrt
        let real_sqrt = ins!(db, real_sqrt);
        Self {
            // # prefix
            // ## pos
            int_pos,
            rat_pos,
            real_pos,
            complex_pos,
            // ## neg
            int_neg,
            rat_neg,
            real_neg,
            complex_neg,
            // # binary operators
            // ## sub
            int_sub,
            rat_sub,
            real_sub,
            complex_sub,
            // ## div
            rat_div,
            real_div,
            complex_div,
            // ## add
            nat_add,
            int_add,
            rat_add,
            real_add,
            complex_add,
            // ## mul
            nat_mul,
            int_mul,
            rat_mul,
            real_mul,
            complex_mul,
            // ## power
            nat_to_the_power_of_nat,
            int_to_the_power_of_nat,
            rat_to_the_power_of_nat,
            real_to_the_power_of_nat,
            complex_to_the_power_of_nat,
            // ## eq
            nat_eq,
            int_eq,
            rat_eq,
            real_eq,
            complex_eq,
            // ## ne
            nat_ne,
            int_ne,
            rat_ne,
            real_ne,
            complex_ne,
            // ## lt
            nat_lt,
            int_lt,
            rat_lt,
            real_lt,
            // ## gt
            nat_gt,
            int_gt,
            rat_gt,
            real_gt,
            // ## le
            nat_le,
            int_le,
            rat_le,
            real_le,
            // ## ge
            nat_ge,
            int_ge,
            rat_ge,
            real_ge,
            // # sqrt
            real_sqrt,
        }
    }
}

#[salsa::tracked(return_ref)]
pub fn vd_instantiation_menu(db: &::salsa::Db) -> VdInstantiationMenu {
    VdInstantiationMenu::new(db)
}

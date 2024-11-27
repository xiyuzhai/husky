use super::*;
use lazy_static::lazy_static;
use visored_entity_path::menu::{VdItemPathMenu, VD_ITEM_PATH_MENU};

#[derive(Debug, PartialEq, Eq)]
pub struct VdTermMenu {
    /// ## literals
    pub zero: VdLiteral,
    pub one: VdLiteral,
    pub two: VdLiteral,
    /// ## types as terms
    pub nat: VdTerm,
    pub int: VdTerm,
    pub rat: VdTerm,
    pub real: VdTerm,
    pub complex: VdTerm,
}

impl VdTermMenu {
    fn new() -> Self {
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
            nat_add,
            nat_mul,
            ring_sub,
            ring_add,
            ring_mul,
            ring_power,
            ring_pos,
            ring_neg,
            field_div,
            eq,
            ne,
            lt,
            gt,
            le,
            ge,
            real_sqrt,
        } = *VD_ITEM_PATH_MENU;

        let zero = VdLiteral::new(VdLiteralData::NaturalNumber("0".to_string()));
        let one = VdLiteral::new(VdLiteralData::NaturalNumber("1".to_string()));
        let two = VdLiteral::new(VdLiteralData::NaturalNumber("2".to_string()));
        let nat = VdTerm::new_item_path(nat.into());
        let int = VdTerm::new_item_path(int.into());
        let rat = VdTerm::new_item_path(rat.into());
        let real = VdTerm::new_item_path(real.into());
        let complex = VdTerm::new_item_path(complex.into());
        Self {
            zero,
            one,
            two,
            nat,
            int,
            rat,
            real,
            complex,
        }
    }
}

lazy_static! {
    pub static ref VD_TERM_MENU: VdTermMenu = VdTermMenu::new();
}

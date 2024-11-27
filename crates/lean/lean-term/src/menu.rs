use crate::term::LnTerm;
use crate::*;
use lazy_static::lazy_static;
use lean_entity_path::menu::{ln_item_path_menu, LnItemPathMenu};

#[derive(Debug, PartialEq, Eq)]
pub struct LnTermMenu {
    pub nat: LnTerm,
    pub int: LnTerm,
    pub rat: LnTerm,
    pub real: LnTerm,
    pub complex: LnTerm,
}

impl LnTermMenu {
    pub fn new() -> Self {
        let LnItemPathMenu {
            nat,
            rat,
            int,
            real,
            complex,
            ring_add,
            ring_mul,
            ring_pos,
            ring_neg,
            field_div,
            le,
            ge,
            eq,
            real_sqrt,
        } = *ln_item_path_menu;
        Self {
            nat: LnTerm::new_item_path(nat),
            int: LnTerm::new_item_path(int),
            rat: LnTerm::new_item_path(rat),
            real: LnTerm::new_item_path(real),
            complex: LnTerm::new_item_path(complex),
        }
    }
}

lazy_static! {
    pub static ref ln_term_menu: LnTermMenu = LnTermMenu::new();
}

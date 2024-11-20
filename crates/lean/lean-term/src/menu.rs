use lean_item_path::menu::{ln_item_path_menu, LnItemPathMenu};

use crate::term::LnTerm;
use crate::*;

#[derive(Debug, PartialEq, Eq)]
pub struct LnTermMenu {
    pub nat: LnTerm,
    pub int: LnTerm,
    pub rat: LnTerm,
    pub real: LnTerm,
    pub complex: LnTerm,
}

impl LnTermMenu {
    pub fn new(db: &::salsa::Db) -> Self {
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
        } = *ln_item_path_menu(db);
        Self {
            nat: LnTerm::new_item_path(nat),
            int: LnTerm::new_item_path(int),
            rat: LnTerm::new_item_path(rat),
            real: LnTerm::new_item_path(real),
            complex: LnTerm::new_item_path(complex),
        }
    }
}

#[salsa::tracked(return_ref)]
pub fn ln_term_menu(db: &::salsa::Db) -> LnTermMenu {
    LnTermMenu::new(db)
}

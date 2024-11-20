use super::*;
use visored_item_path::menu::{vd_item_path_menu, VdItemPathMenu};

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
    fn new(db: &::salsa::Db) -> Self {
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
            eq,
            ne,
            lt,
            gt,
            le,
            ge,
            real_sqrt,
        } = *vd_item_path_menu(db);

        let zero = VdLiteral::new(VdLiteralData::NaturalNumber("0".to_string()), db);
        let one = VdLiteral::new(VdLiteralData::NaturalNumber("1".to_string()), db);
        let two = VdLiteral::new(VdLiteralData::NaturalNumber("2".to_string()), db);
        let nat = VdTerm::new_item_path(nat.into(), db);
        let int = VdTerm::new_item_path(int.into(), db);
        let rat = VdTerm::new_item_path(rat.into(), db);
        let real = VdTerm::new_item_path(real.into(), db);
        let complex = VdTerm::new_item_path(complex.into(), db);
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

#[salsa::tracked(return_ref)]
pub fn vd_term_menu(db: &::salsa::Db) -> VdTermMenu {
    VdTermMenu::new(db)
}

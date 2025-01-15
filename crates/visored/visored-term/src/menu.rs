use crate::{
    instantiation::VdInstantiation,
    term::{
        literal::{VdLiteral, VdLiteralData},
        VdTerm,
    },
    ty::{VdType, VdTypeData},
};
use eterned::{db::EternerDb, memo};
use lazy_static::lazy_static;
use smallvec::{smallvec, SmallVec};
use visored_entity_path::{
    menu::{VdItemPathMenu, VD_ITEM_PATH_MENU},
    path::VdItemPath,
};

#[derive(Debug, PartialEq, Eq)]
pub struct VdTypeMenu {
    /// natural numbers as a type
    pub nat: VdType,
    /// integers as a type
    pub int: VdType,
    /// rational numbers as a type
    pub rat: VdType,
    /// real numbers as a type
    pub real: VdType,
    /// complex numbers as a type
    pub complex: VdType,
    /// the category of sets as a type
    pub set: VdType,
    /// the category of propositions as a type
    pub prop: VdType,
}

impl VdTypeMenu {
    fn new(db: &EternerDb) -> Self {
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
            iff,
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

        let nat = VdType::new_item_path(nat.into(), db);
        let int = VdType::new_item_path(int.into(), db);
        let rat = VdType::new_item_path(rat.into(), db);
        let real = VdType::new_item_path(real.into(), db);
        let complex = VdType::new_item_path(complex.into(), db);
        let set = VdType::new_item_path(set.into(), db);
        let prop = VdType::new_item_path(prop.into(), db);

        Self {
            nat,
            int,
            rat,
            real,
            complex,
            set,
            prop,
        }
    }
}

#[memo(return_ref)]
pub fn vd_ty_menu(db: &EternerDb) -> VdTypeMenu {
    VdTypeMenu::new(db)
}

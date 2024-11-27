use crate::{
    instantiation::VdInstantiation,
    term::{
        literal::{VdLiteral, VdLiteralData},
        VdTerm,
    },
    ty::{VdType, VdTypeData},
};
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

        let nat = VdType::new_item_path(nat.into());
        let int = VdType::new_item_path(int.into());
        let rat = VdType::new_item_path(rat.into());
        let real = VdType::new_item_path(real.into());
        let complex = VdType::new_item_path(complex.into());
        let set = VdType::new_item_path(set.into());
        let prop = VdType::new_item_path(prop.into());

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

lazy_static! {
    pub static ref VD_TYPE_MENU: VdTypeMenu = VdTypeMenu::new();
}

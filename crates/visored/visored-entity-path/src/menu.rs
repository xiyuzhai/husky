use crate::path::{
    category::VdCategoryPath, function::VdFunctionPath, set::VdSetPath, trai::VdTraitPath,
    trai_item::VdTraitItemPath,
};
use lazy_static::lazy_static;

#[derive(Debug, PartialEq, Eq)]
pub struct VdItemPathMenu {
    // # categories
    pub set: VdCategoryPath,
    pub prop: VdCategoryPath,
    // # sets
    pub nat: VdSetPath,
    pub rat: VdSetPath,
    pub int: VdSetPath,
    pub real: VdSetPath,
    pub complex: VdSetPath,
    // # functions
    pub sin: VdFunctionPath,
    pub cos: VdFunctionPath,
    // # traits
    pub group: VdTraitPath,
    pub ring: VdTraitPath,
    // # trait items
    pub group_mul: VdTraitItemPath,
    pub abelian_group_add: VdTraitItemPath,
    pub nat_add: VdTraitItemPath,
    pub nat_mul: VdTraitItemPath,
    pub ring_sub: VdTraitItemPath,
    pub ring_add: VdTraitItemPath,
    pub ring_mul: VdTraitItemPath,
    pub ring_power: VdTraitItemPath,
    pub ring_pos: VdTraitItemPath,
    pub ring_neg: VdTraitItemPath,
    pub field_div: VdTraitItemPath,
    pub real_sqrt: VdTraitItemPath,
    pub eq: VdTraitItemPath,
    pub ne: VdTraitItemPath,
    pub lt: VdTraitItemPath,
    pub gt: VdTraitItemPath,
    pub le: VdTraitItemPath,
    pub ge: VdTraitItemPath,
}

impl VdItemPathMenu {
    pub fn new() -> Self {
        Self {
            // # categories
            set: VdCategoryPath::SET,
            prop: VdCategoryPath::PROPOSITION,
            // # sets
            nat: VdSetPath::NATURAL_NUMBER,
            rat: VdSetPath::RATIONAL_NUMBER,
            int: VdSetPath::INTEGER,
            real: VdSetPath::REAL_NUMBER,
            complex: VdSetPath::COMPLEX_NUMBER,
            // # functions
            sin: VdFunctionPath::SIN,
            cos: VdFunctionPath::COS,
            // # traits
            group: VdTraitPath::GROUP,
            ring: VdTraitPath::RING,
            // # trait items
            group_mul: VdTraitItemPath::GROUP_MUL,
            abelian_group_add: VdTraitItemPath::ABELIAN_GROUP_ADD,
            nat_add: VdTraitItemPath::NAT_ADD,
            nat_mul: VdTraitItemPath::NAT_MUL,
            ring_sub: VdTraitItemPath::RING_SUB,
            ring_add: VdTraitItemPath::RING_ADD,
            ring_mul: VdTraitItemPath::RING_MUL,
            ring_power: VdTraitItemPath::RING_POWER,
            ring_pos: VdTraitItemPath::RING_POS,
            ring_neg: VdTraitItemPath::RING_NEG,
            field_div: VdTraitItemPath::FIELD_DIV,
            real_sqrt: VdTraitItemPath::REAL_SQRT,
            eq: VdTraitItemPath::EQ,
            ne: VdTraitItemPath::NE,
            lt: VdTraitItemPath::LT,
            gt: VdTraitItemPath::GT,
            le: VdTraitItemPath::LE,
            ge: VdTraitItemPath::GE,
        }
    }
}

lazy_static! {
    pub static ref VD_ITEM_PATH_MENU: VdItemPathMenu = VdItemPathMenu::new();
}

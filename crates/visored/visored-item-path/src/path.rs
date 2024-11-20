pub mod category;
pub mod function;
pub mod set;
pub mod trai;
pub mod trai_item;

use self::{category::*, function::*, set::*, trai::*, trai_item::*};

#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdItemPath {
    Category(VdCategoryPath),
    Set(VdSetPath),
    Function(VdFunctionPath),
    Trait(VdTraitPath),
    TraitItem(VdTraitItemPath),
}

impl VdItemPath {
    // # categories
    pub const SET: Self = VdItemPath::Category(VdCategoryPath::SET);
    pub const PROPOSITION: Self = VdItemPath::Category(VdCategoryPath::PROPOSITION);
    // # sets
    pub const NAT: Self = VdItemPath::Set(VdSetPath::NATURAL_NUMBER);
    pub const RAT: Self = VdItemPath::Set(VdSetPath::RATIONAL_NUMBER);
    pub const INT: Self = VdItemPath::Set(VdSetPath::INTEGER);
    pub const REAL: Self = VdItemPath::Set(VdSetPath::REAL_NUMBER);
    pub const COMPLEX: Self = VdItemPath::Set(VdSetPath::COMPLEX_NUMBER);
    // # functions
    pub const SIN: Self = VdItemPath::Function(VdFunctionPath::SIN);
    pub const COS: Self = VdItemPath::Function(VdFunctionPath::COS);
}

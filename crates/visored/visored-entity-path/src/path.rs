pub mod category;
pub mod function;
pub mod prop;
pub mod set;
pub mod trai;
pub mod trai_item;

use self::{category::*, function::*, prop::*, set::*, trai::*, trai_item::*};
use eterned::db::EternerDb;
use lisp_csv::expr::{LpCsvExpr, LpCsvExprData};

#[enum_class::from_variants]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VdItemPath {
    Prop(VdPropPath),
    Category(VdCategoryPath),
    Set(VdSetPath),
    Function(VdFunctionPath),
    Trait(VdTraitPath),
    TraitItem(VdTraitItemPath),
}

impl std::fmt::Display for VdItemPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.show_fmt(f)
    }
}

impl VdItemPath {
    // # prop
    pub const TRUE: Self = VdItemPath::Prop(VdPropPath::TRUE);
    pub const FALSE: Self = VdItemPath::Prop(VdPropPath::FALSE);
    // # categories
    pub const SET: Self = VdItemPath::Category(VdCategoryPath::SET);
    pub const PROP: Self = VdItemPath::Category(VdCategoryPath::PROP);
    // # sets
    pub const NAT: Self = VdItemPath::Set(VdSetPath::NATURAL_NUMBER);
    pub const RAT: Self = VdItemPath::Set(VdSetPath::RATIONAL_NUMBER);
    pub const INT: Self = VdItemPath::Set(VdSetPath::INTEGER);
    pub const REAL: Self = VdItemPath::Set(VdSetPath::REAL_NUMBER);
    pub const COMPLEX: Self = VdItemPath::Set(VdSetPath::COMPLEX_NUMBER);
    // # functions
    pub const SIN: Self = VdItemPath::Function(VdFunctionPath::SIN);
    pub const COS: Self = VdItemPath::Function(VdFunctionPath::COS);
    // # trait items
    pub const EQ: Self = VdItemPath::TraitItem(VdTraitItemPath::EQ);
    pub const NE: Self = VdItemPath::TraitItem(VdTraitItemPath::NE);
    pub const LT: Self = VdItemPath::TraitItem(VdTraitItemPath::LT);
    pub const GT: Self = VdItemPath::TraitItem(VdTraitItemPath::GT);
    pub const LE: Self = VdItemPath::TraitItem(VdTraitItemPath::LE);
    pub const GE: Self = VdItemPath::TraitItem(VdTraitItemPath::GE);
    pub const NAT_ADD: Self = VdItemPath::TraitItem(VdTraitItemPath::NAT_ADD);
    pub const NAT_MUL: Self = VdItemPath::TraitItem(VdTraitItemPath::NAT_MUL);
    pub const RING_ADD: Self = VdItemPath::TraitItem(VdTraitItemPath::RING_ADD);
    pub const RING_MUL: Self = VdItemPath::TraitItem(VdTraitItemPath::RING_MUL);
    pub const RING_POWER: Self = VdItemPath::TraitItem(VdTraitItemPath::RING_POWER);
    pub const RING_POS: Self = VdItemPath::TraitItem(VdTraitItemPath::RING_POS);
    pub const RING_NEG: Self = VdItemPath::TraitItem(VdTraitItemPath::RING_NEG);
    pub const RING_SUB: Self = VdItemPath::TraitItem(VdTraitItemPath::RING_SUB);
    pub const FIELD_DIV: Self = VdItemPath::TraitItem(VdTraitItemPath::FIELD_DIV);
    pub const REAL_SQRT: Self = VdItemPath::TraitItem(VdTraitItemPath::REAL_SQRT);
    pub const IN_SET: Self = VdItemPath::TraitItem(VdTraitItemPath::IN_SET);
    pub const IFF: Self = VdItemPath::TraitItem(VdTraitItemPath::IFF);
}

impl VdItemPath {
    pub fn from_lp_csv_expr(expr: &LpCsvExpr, db: &EternerDb) -> Self {
        let LpCsvExprData::Ident(ref ident) = expr.data else {
            todo!("expected identifier but got {:#?}", expr.data)
        };
        match ident as &str {
            "eq" => VdItemPath::EQ,
            "ne" => VdItemPath::NE,
            "lt" => VdItemPath::LT,
            "gt" => VdItemPath::GT,
            "le" => VdItemPath::LE,
            "ge" => VdItemPath::GE,
            "ring_pos" => VdItemPath::RING_POS,
            "ring_neg" => VdItemPath::RING_NEG,
            "ring_sub" => VdItemPath::RING_SUB,
            "nat_add" => VdItemPath::NAT_ADD,
            "nat_mul" => VdItemPath::NAT_MUL,
            "ring_add" => VdItemPath::RING_ADD,
            "ring_mul" => VdItemPath::RING_MUL,
            "ring_power" => VdItemPath::RING_POWER,
            "field_div" => VdItemPath::FIELD_DIV,
            "real_sqrt" => VdItemPath::REAL_SQRT,
            "in_set" => VdItemPath::IN_SET,
            "iff" => VdItemPath::IFF,
            s => todo!("s = {s:?} not handled"),
        }
    }
}

impl std::fmt::Debug for VdItemPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.show_fmt(f)
    }
}

impl VdItemPath {
    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VdItemPath::Prop(prop_path) => prop_path.show_fmt(f),
            VdItemPath::Category(category_path) => category_path.show_fmt(f),
            VdItemPath::Set(set_path) => set_path.show_fmt(f),
            VdItemPath::Function(function_path) => function_path.show_fmt(f),
            VdItemPath::Trait(trait_path) => trait_path.show_fmt(f),
            VdItemPath::TraitItem(trait_item_path) => trait_item_path.show_fmt(f),
        }
    }
}

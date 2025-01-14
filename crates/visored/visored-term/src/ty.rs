pub mod table;

use crate::{
    menu::{vd_ty_menu, VdTypeMenu},
    term::{VdTerm, VdTermData, VdTermId},
};
use eterned::db::EternerDb;
use lisp_csv::expr::{LpCsvExpr, LpCsvExprData};
use smallvec::{smallvec, SmallVec};
use visored_coword::namae::VdNamae;
use visored_entity_path::path::{
    set::{VdPreludeSetPath, VdSetPath},
    VdItemPath,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VdType(VdTerm);

impl std::ops::Deref for VdType {
    type Target = VdTerm;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl std::fmt::Debug for VdType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.show_aux(f)
    }
}

impl VdType {
    pub fn show_aux(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.show_fmt(f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VdTypeData {
    ItemPath(VdItemPath), // TODO: do we need a path here?
}

impl VdType {
    pub fn new_item_path(item_path: VdItemPath, db: &EternerDb) -> Self {
        // TODO: check this is actually a type?
        VdType(VdTerm::new_item_path(item_path, db))
    }

    pub fn new(term: VdTerm) -> Self {
        // TODO: check this is actually a type?
        VdType(term)
    }
}

impl VdType {
    pub fn is_function_like(self, db: &EternerDb) -> bool {
        is_vd_ty_function_like(**self, db)
    }

    pub fn is_numeric(self, db: &EternerDb) -> bool {
        is_vd_ty_numeric(**self, db)
    }
}

#[eterned::memo]
fn is_vd_ty_function_like(ty: VdTermId, db: &EternerDb) -> bool {
    match *ty.data() {
        VdTermData::ItemPath(_) => false,
        VdTermData::Literal(_) => todo!(),
        VdTermData::ForAll(_) => todo!(),
        VdTermData::Exists(_) => todo!(),
        VdTermData::Limit(_) => todo!(),
        VdTermData::Eval(_) => todo!(),
        VdTermData::SymbolicVariable(_) => todo!(),
        VdTermData::AbstractVariable(_) => todo!(),
        VdTermData::StackVariable(_) => todo!(),
        VdTermData::Application(_) => todo!(),
        VdTermData::Abstraction(_) => todo!(),
    }
}

#[eterned::memo]
fn is_vd_ty_numeric(ty: VdTermId, db: &EternerDb) -> bool {
    match *ty.data() {
        VdTermData::ItemPath(ref data) => match data.item_path() {
            VdItemPath::Prop(vd_prop_path) => todo!(),
            VdItemPath::Category(vd_category_path) => todo!(),
            VdItemPath::Set(vd_set_path) => match vd_set_path {
                VdSetPath::Prelude(vd_prelude_set_path) => match vd_prelude_set_path {
                    VdPreludeSetPath::NaturalNumber
                    | VdPreludeSetPath::RationalNumber
                    | VdPreludeSetPath::Integer
                    | VdPreludeSetPath::RealNumber
                    | VdPreludeSetPath::ComplexNumber => true,
                    _ => todo!(),
                },
            },
            VdItemPath::Function(vd_function_path) => todo!(),
            VdItemPath::Trait(vd_trait_path) => todo!(),
            VdItemPath::TraitItem(vd_trait_item_path) => todo!(),
        },
        VdTermData::Literal(_) => todo!(),
        VdTermData::ForAll(_) => todo!(),
        VdTermData::Exists(_) => todo!(),
        VdTermData::Limit(_) => todo!(),
        VdTermData::Eval(_) => todo!(),
        VdTermData::SymbolicVariable(_) => todo!(),
        VdTermData::AbstractVariable(_) => todo!(),
        VdTermData::StackVariable(_) => todo!(),
        VdTermData::Application(_) => todo!(),
        VdTermData::Abstraction(_) => todo!(),
    }
}

impl VdType {
    pub fn from_lp_csv_expr(expr: &LpCsvExpr, db: &EternerDb) -> Self {
        match expr.data {
            LpCsvExprData::Literal(ref literal) => todo!(),
            LpCsvExprData::Application(ref app) => todo!(),
            LpCsvExprData::List(ref vec) => todo!(),
            LpCsvExprData::Ident(ref ident) => Self::from_lp_csv_ident(ident, db),
            LpCsvExprData::Parenthesized(ref lp_csv_expr) => todo!(),
        }
    }

    pub fn from_lp_csv_ident(ident: &str, db: &EternerDb) -> Self {
        let VdTypeMenu {
            nat,
            int,
            rat,
            real,
            complex,
            set,
            prop,
        } = *vd_ty_menu(db);
        match ident as &str {
            "true" => todo!(),
            "false" => todo!(),
            "nat" => nat,
            "int" => int,
            "rat" => rat,
            "real" => real,
            "complex" => complex,
            "set" => set,
            "prop" => prop,
            s => todo!("s = {s:?} not handled"),
        }
    }
}

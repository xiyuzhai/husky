pub mod abstract_variable;
pub mod abstraction;
pub mod application;
pub mod eval;
pub mod exists;
pub mod forall;
pub mod item_path;
pub mod limit;
pub mod literal;
pub mod menu;
pub mod stack_variable;
pub mod symbolic_variable;

use self::{
    abstract_variable::{VdAbstractVariable, VdAbstractVariableData},
    abstraction::{VdAbstraction, VdAbstractionData},
    application::{VdApplication, VdApplicationData},
    eval::{VdEval, VdEvalData},
    exists::{VdExists, VdExistsData},
    forall::{VdForAll, VdForAllData},
    item_path::VdItemPathTerm,
    limit::{VdLimit, VdLimitData},
    literal::{VdLiteral, VdLiteralData},
    stack_variable::{VdStackVariable, VdStackVariableData},
    symbolic_variable::{VdSymbolicVariable, VdSymbolicVariableData},
};
use crate::{ty::VdType, *};
use eterned::db::EternerDb;
use item_path::VdItemPathTermData;
use lisp_csv::expr::{LpCsvExpr, LpCsvExprData};
use menu::{vd_term_menu, VdTermMenu};
use smallvec::SmallVec;
use visored_entity_path::path::VdItemPath;

#[enum_class::from_variants]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VdTerm {
    Literal(VdLiteral),
    ItemPath(VdItemPathTerm),
    ForAll(VdForAll),
    Exists(VdExists),
    Limit(VdLimit),
    Eval(VdEval),
    SymbolicVariable(VdSymbolicVariable),
    AbstractVariable(VdAbstractVariable),
    StackVariable(VdStackVariable),
    Application(VdApplication),
    Abstraction(VdAbstraction),
}

impl std::fmt::Debug for VdTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.show_fmt(f)
    }
}

impl VdTerm {
    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data().show_fmt(f)
    }
}

impl VdTermData {
    pub fn show_fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VdTermData::Literal(_) => todo!(),
            VdTermData::ItemPath(ref data) => data.item_path().show_fmt(f),
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
}

impl std::ops::Deref for VdTerm {
    type Target = VdTermId;
    fn deref(&self) -> &Self::Target {
        match self {
            VdTerm::Literal(literal) => literal,
            VdTerm::ItemPath(item_path) => item_path,
            VdTerm::ForAll(for_all) => for_all,
            VdTerm::Exists(exists) => exists,
            VdTerm::Limit(limit) => limit,
            VdTerm::Eval(eval) => eval,
            VdTerm::SymbolicVariable(symbolic_variable) => symbolic_variable,
            VdTerm::AbstractVariable(abstract_variable) => abstract_variable,
            VdTerm::StackVariable(stack_variable) => stack_variable,
            VdTerm::Application(application) => application,
            VdTerm::Abstraction(abstraction) => abstraction,
        }
    }
}

pub type ZfcTerms = SmallVec<[VdTerm; 4]>;

#[eterned::eterned]
pub struct VdTermId {
    #[return_ref]
    pub data: VdTermData,
}

impl std::fmt::Debug for VdTermId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.data().show_fmt(f)
    }
}

#[enum_class::from_variants]
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum VdTermData {
    Literal(VdLiteralData),
    ItemPath(VdItemPathTermData),
    ForAll(VdForAllData),
    Exists(VdExistsData),
    Limit(VdLimitData),
    Eval(VdEvalData),
    SymbolicVariable(VdSymbolicVariableData),
    AbstractVariable(VdAbstractVariableData),
    StackVariable(VdStackVariableData),
    Application(VdApplicationData),
    Abstraction(VdAbstractionData),
}

impl VdTermData {
    pub const PROP: Self = Self::ItemPath(VdItemPathTermData::PROP);
}

impl VdTerm {
    pub fn to_ty(self) -> VdType {
        VdType::new(self)
    }
}

impl VdTerm {
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
        let VdTermMenu {
            zero,
            one,
            two,
            nat,
            int,
            rat,
            real,
            complex,
        } = *vd_term_menu(db);
        match ident as &str {
            "true" => todo!(),
            "false" => todo!(),
            "nat" => nat,
            "int" => int,
            "rat" => rat,
            "real" => real,
            "complex" => complex,
            s => todo!("s = {s:?} not handled"),
        }
    }
}

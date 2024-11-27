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
use crate::ty::VdType;
use item_path::VdItemPathTermData;
use lisp_csv::expr::{LpCsvExpr, LpCsvExprData};
use menu::{VdTermMenu, VD_TERM_MENU};
use smallvec::SmallVec;
use visored_entity_path::path::VdItemPath;

#[enum_class::from_variants]
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
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
        self.show_aux(f)
    }
}

impl VdTerm {
    pub fn show_aux(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self.data() {
            VdTermData::Literal(_) => todo!(),
            VdTermData::ItemPath(ref data) => data.item_path().show_aux(f),
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

#[interned::interned]
pub struct VdTermId {
    pub data: VdTermData,
}

#[enum_class::from_variants]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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

impl VdTerm {
    pub fn to_ty(self) -> VdType {
        VdType::new(self)
    }
}

impl VdTerm {
    pub fn from_lp_csv_expr(expr: &LpCsvExpr) -> Self {
        match expr.data {
            LpCsvExprData::Literal(ref literal) => todo!(),
            LpCsvExprData::Application(ref app) => todo!(),
            LpCsvExprData::List(ref vec) => todo!(),
            LpCsvExprData::Ident(ref ident) => Self::from_lp_csv_ident(ident),
            LpCsvExprData::Parenthesized(ref lp_csv_expr) => todo!(),
        }
    }

    pub fn from_lp_csv_ident(ident: &str) -> Self {
        let VdTermMenu {
            zero,
            one,
            two,
            nat,
            int,
            rat,
            real,
            complex,
        } = *VD_TERM_MENU;
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

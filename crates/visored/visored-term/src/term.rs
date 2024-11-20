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
use smallvec::SmallVec;
use visored_item_path::path::VdItemPath;

#[salsa::derive_debug_with_db]
#[enum_class::from_variants]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

impl std::ops::Deref for VdTerm {
    type Target = VdTermId;
    fn deref(&self) -> &Self::Target {
        match self {
            VdTerm::Literal(literal) => &*literal,
            VdTerm::ItemPath(item_path) => &*item_path,
            VdTerm::ForAll(for_all) => &*for_all,
            VdTerm::Exists(exists) => &*exists,
            VdTerm::Limit(limit) => &*limit,
            VdTerm::Eval(eval) => &*eval,
            VdTerm::SymbolicVariable(symbolic_variable) => &*symbolic_variable,
            VdTerm::AbstractVariable(abstract_variable) => &*abstract_variable,
            VdTerm::StackVariable(stack_variable) => &*stack_variable,
            VdTerm::Application(application) => &*application,
            VdTerm::Abstraction(abstraction) => &*abstraction,
        }
    }
}

pub type ZfcTerms = SmallVec<[VdTerm; 4]>;

#[salsa::interned]
pub struct VdTermId {
    #[return_ref]
    data: VdTermData,
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
    pub fn to_ty(self, db: &::salsa::Db) -> VdType {
        zfc_term_to_ty(db, *self)
    }
}

#[salsa::tracked]
fn zfc_term_to_ty(db: &::salsa::Db, term_id: VdTermId) -> VdType {
    match *term_id.data(db) {
        VdTermData::Literal(ref data) => todo!(),
        VdTermData::ItemPath(ref data) => VdType::new_item_path(data.item_path(), db),
        VdTermData::ForAll(ref data) => todo!(),
        VdTermData::Exists(ref data) => todo!(),
        VdTermData::Limit(ref data) => todo!(),
        VdTermData::Eval(ref data) => todo!(),
        VdTermData::SymbolicVariable(ref data) => todo!(),
        VdTermData::AbstractVariable(ref data) => todo!(),
        VdTermData::StackVariable(ref data) => todo!(),
        VdTermData::Application(ref data) => todo!(),
        VdTermData::Abstraction(ref data) => todo!(),
    }
}

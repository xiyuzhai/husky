pub mod abstract_variable;
pub mod abstraction;
pub mod application;
pub mod eval;
pub mod exists;
pub mod forall;
pub mod limit;
pub mod literal;
pub mod stack_variable;
pub mod symbolic_variable;

use self::{
    abstract_variable::{VdZfcAbstractVariable, VdZfcAbstractVariableData},
    abstraction::{VdZfcAbstraction, VdZfcAbstractionData},
    application::{VdZfcApplication, VdZfcApplicationData},
    eval::{VdZfcEval, VdZfcEvalData},
    exists::{VdZfcExists, VdZfcExistsData},
    forall::{VdZfcForAll, VdZfcForAllData},
    limit::{VdZfcLimit, VdZfcLimitData},
    literal::{VdZfcLiteral, VdZfcLiteralData},
    stack_variable::{VdZfcStackVariable, VdZfcStackVariableData},
    symbolic_variable::{VdZfcSymbolicVariable, VdZfcSymbolicVariableData},
};
use smallvec::SmallVec;

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VdZfcTerm {
    Literal(VdZfcLiteral),
    ForAll(VdZfcForAll),
    Exists(VdZfcExists),
    Limit(VdZfcLimit),
    Eval(VdZfcEval),
    SymbolicVariable(VdZfcSymbolicVariable),
    AbstractVariable(VdZfcAbstractVariable),
    StackVariable(VdZfcStackVariable),
    Application(VdZfcApplication),
    Abstraction(VdZfcAbstraction),
}

pub type ZfcTerms = SmallVec<[VdZfcTerm; 4]>;

#[salsa::interned]
pub struct VdZfcTermId {
    #[return_ref]
    data: VdZfcTermData,
}

#[enum_class::from_variants]
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum VdZfcTermData {
    Literal(VdZfcLiteralData),
    ForAll(VdZfcForAllData),
    Exists(VdZfcExistsData),
    Limit(VdZfcLimitData),
    Eval(VdZfcEvalData),
    SymbolicVariable(VdZfcSymbolicVariableData),
    AbstractVariable(VdZfcAbstractVariableData),
    StackVariable(VdZfcStackVariableData),
    Application(VdZfcApplicationData),
    Abstraction(VdZfcAbstractionData),
}

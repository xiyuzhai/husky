use super::*;

#[enum_class::from_variants]
#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PlotClassTerm {
    Literal(PlotClass),
    NonLiteral(NonLiteralPlotClassTerm),
}

#[salsa::interned]
pub struct NonLiteralPlotClassTerm {
    #[return_ref]
    data: PlotClassTermData,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PlotClassTermData {
    Literal(PlotClass),
    SymbolicVariable(EthSymbolicVariable),
    AbstractVariable(EthAbstractVariable),
    Group(Vec<PlotClassTerm>),
}

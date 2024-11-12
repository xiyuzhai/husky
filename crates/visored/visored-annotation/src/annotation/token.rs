#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[repr(u8)]
pub enum VdTokenAnnotation {
    Integral(LxIntegralAnnotation) = 1,
    Variable(LxVariableAnnotation),
    Differential,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxIntegralAnnotation {
    SingleVariableDefiniteIntegralOverReal,
    SingleVariableIndefiniteIntegralOverReal,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum LxVariableAnnotation {
    Usage,
    SingleVariableIntegralVariableDecl,
}

pub const VARIABLE_USAGE: VdTokenAnnotation =
    VdTokenAnnotation::Variable(LxVariableAnnotation::Usage);
pub const SINGLE_VARIABLE_INTEGRAL_VARIABLE_DECL: VdTokenAnnotation =
    VdTokenAnnotation::Variable(LxVariableAnnotation::SingleVariableIntegralVariableDecl);
pub const DIFFERENTIAL: VdTokenAnnotation = VdTokenAnnotation::Differential;

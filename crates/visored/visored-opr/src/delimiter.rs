#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdBaseLeftDelimiter {
    Lpar,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdBaseRightDelimiter {
    Rpar,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdCompositeLeftDelimiter {}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdCompositeRightDelimiter {}

impl VdBaseLeftDelimiter {
    pub const LPAR: Self = VdBaseLeftDelimiter::Lpar;
}

impl VdBaseRightDelimiter {
    pub const RPAR: Self = VdBaseRightDelimiter::Rpar;

    pub fn latex_code(&self) -> &'static str {
        match self {
            VdBaseRightDelimiter::Rpar => ")",
        }
    }
}

impl VdBaseLeftDelimiter {
    pub fn latex_code(self) -> &'static str {
        match self {
            VdBaseLeftDelimiter::Lpar => "(",
        }
    }
}

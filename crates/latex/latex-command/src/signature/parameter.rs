use latex_prelude::mode::LxMode;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LxCommandParameter {
    mode: LxCommandParameterMode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LxCommandParameterMode {
    Name,
    Math,
    Rose,
    SingleLetter,
}

impl LxCommandParameter {
    pub fn new(mode: LxCommandParameterMode) -> Self {
        Self { mode }
    }
}

impl LxCommandParameter {
    pub fn mode(&self) -> LxCommandParameterMode {
        self.mode
    }
}

pub type LxCommandParameters = Vec<LxCommandParameter>;

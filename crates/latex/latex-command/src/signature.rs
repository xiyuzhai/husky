pub mod parameter;
pub mod table;

use self::parameter::LxCommandParameters;
use crate::path::LxCommandPath;
use crate::*;
use latex_math_letter::letter::styled::LxMathLetterStyle;
use latex_prelude::mode::LxModeSet;
use parameter::LxCommandParameter;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LxCommandSignature {
    Complete(LxCompleteCommandSignature),
    MathLetterStyle(LxMathLetterStyle),
    Begin,
    End,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LxCompleteCommandSignature {
    path: LxCommandPath,
    // the modes that allow the usage of this command
    allowed_modes: LxModeSet,
    // TODO: ad hoc
    options: (),
    parameters: LxCommandParameters,
}

impl LxCompleteCommandSignature {
    pub fn path(&self) -> LxCommandPath {
        self.path
    }

    pub fn parameters(&self) -> &[LxCommandParameter] {
        &self.parameters
    }
}

pub mod table;

use crate::path::LxEnvironmentPath;
use latex_prelude::mode::{LxMode, LxModeSet};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LxEnvironmentSignature {
    path: LxEnvironmentPath,
    allowed_modes: LxModeSet,
    body_mode: LxMode,
}

impl LxEnvironmentSignature {
    pub fn new(path: LxEnvironmentPath, allowed_modes: &[LxMode], body_mode: LxMode) -> Self {
        Self {
            path,
            allowed_modes: allowed_modes.iter().copied().collect(),
            body_mode,
        }
    }
}

impl LxEnvironmentSignature {
    pub fn path(&self) -> LxEnvironmentPath {
        self.path
    }

    pub fn allowed_in_math(&self) -> bool {
        self.allowed_modes.allowed_in_math()
    }

    pub fn allowed_in_rose(&self) -> bool {
        self.allowed_modes.allowed_in_rose()
    }

    pub fn allowed_in_root(&self) -> bool {
        self.allowed_modes.allowed_in_root()
    }

    pub fn body_mode(&self) -> LxMode {
        self.body_mode
    }
}

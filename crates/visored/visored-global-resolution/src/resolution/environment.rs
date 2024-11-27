use super::*;
use latex_environment::path::LxEnvironmentPath;
use rustc_hash::FxHashMap;
use visored_entity_path::environment::VdEnvironmentPath;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdEnvironmentGlobalResolution {
    Environment(VdEnvironmentPath),
}

pub type VdEnvironmentGlobalResolutionMap =
    FxHashMap<LxEnvironmentPath, VdEnvironmentGlobalResolution>;

impl VdEnvironmentGlobalResolution {
    pub const DOCUMENT: Self =
        VdEnvironmentGlobalResolution::Environment(VdEnvironmentPath::Document);
    pub const EXAMPLE: Self =
        VdEnvironmentGlobalResolution::Environment(VdEnvironmentPath::Example);
    pub const EQUATION: Self =
        VdEnvironmentGlobalResolution::Environment(VdEnvironmentPath::Equation);
}

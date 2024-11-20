use super::*;
use latex_environment::path::LxEnvironmentPath;
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdEnvironmentGlobalResolution {
    Document,
}

pub type VdEnvironmentGlobalResolutionMap =
    FxHashMap<LxEnvironmentPath, VdEnvironmentGlobalResolution>;

impl VdEnvironmentGlobalResolution {
    pub const DOCUMENT: Self = VdEnvironmentGlobalResolution::Document;
}

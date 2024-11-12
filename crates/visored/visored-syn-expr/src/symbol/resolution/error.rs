use super::*;
use thiserror::Error;

#[derive(Debug, PartialEq, Eq, Error)]
pub enum VdSynSymbolResolutionError {
    #[error("{0}")]
    Origin(#[from] OriginalVdSynSymbolResolutionError),
    #[error("{0}")]
    Derived(#[from] DerivedVdSynSymbolResolutionError),
}

#[derive(Debug, PartialEq, Eq, Error)]
pub enum OriginalVdSynSymbolResolutionError {
    #[error("Visored Symbol Resolution Error: ambiguous resolutions")]
    AmbiguousResolutions { resolutions: VdSynSymbolResolutions },
    #[error("Visored Symbol Resolution Error: no resolution")]
    NoResolution,
}

#[derive(Debug, PartialEq, Eq, Error)]
pub enum DerivedVdSynSymbolResolutionError {}

pub type VdSynSymbolResolutionResult<T> = Result<T, VdSynSymbolResolutionError>;

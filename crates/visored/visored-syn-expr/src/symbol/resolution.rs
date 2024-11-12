pub mod error;
pub mod letter;
pub mod punctuation;

use visored_global_resolution::resolution::letter::VdLetterGlobalResolution;

use self::{error::*, letter::*, punctuation::*};
use super::*;
use crate::expr::VdSynExprMap;
use crate::expr::*;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq)]
pub enum VdSynSymbolResolution {
    Letter(VdSynLetterSymbolResolution),
}

impl From<VdLetterGlobalResolution> for VdSynSymbolResolution {
    fn from(resolution: VdLetterGlobalResolution) -> Self {
        VdSynSymbolResolution::Letter(resolution.into())
    }
}

pub type VdSynSymbolResolutions = SmallVec<[VdSynSymbolResolution; 4]>;

pub struct VdSynSymbolResolutionsTable {
    expr_resolutions: VdSynExprMap<VdSynSymbolResolutionResult<VdSynSymbolResolution>>,
}

impl std::ops::Index<VdSynExprIdx> for VdSynSymbolResolutionsTable {
    type Output = VdSynSymbolResolutionResult<VdSynSymbolResolution>;

    fn index(&self, index: VdSynExprIdx) -> &Self::Output {
        &self.expr_resolutions[index]
    }
}

impl VdSynSymbolResolutionsTable {
    pub fn new(expr_arena: VdSynExprArenaRef) -> Self {
        Self {
            expr_resolutions: VdSynExprMap::new2(expr_arena),
        }
    }
}

/// # actions
impl VdSynSymbolResolutionsTable {
    /// Do nothing if the resolution result is `Ok(None)`.
    pub(crate) fn add_expr_symbol_resolutions(
        &mut self,
        expr: VdSynExprIdx,
        resolutions: VdSynSymbolResolutionResult<Option<VdSynSymbolResolutions>>,
    ) {
        let resolution = match resolutions {
            Ok(None) => return,
            Ok(Some(resolutions)) => match resolutions.len() {
                0 => Err(OriginalVdSynSymbolResolutionError::NoResolution.into()),
                1 => Ok(resolutions.into_iter().next().unwrap()),
                _ => Err(
                    OriginalVdSynSymbolResolutionError::AmbiguousResolutions { resolutions }.into(),
                ),
            },
            Err(error) => Err(error),
        };
        self.expr_resolutions.insert_new(expr, resolution);
    }
}

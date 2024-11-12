use super::*;
use pattern::VdSynPattern;
use symbol::{
    builder::VdSynSymbolBuilder,
    local_defn::{VdSynSymbolLocalDefnBody, VdSynSymbolLocalDefnHead},
};

#[derive(Debug, PartialEq, Eq)]
pub struct VdSynLetAssignedResolution {
    pattern: VdSynPattern,
    pattern_expr: VdSynExprIdx,
    assignment: VdSynExprIdx,
}

/// # getters
impl VdSynLetAssignedResolution {
    pub fn pattern(&self) -> &VdSynPattern {
        &self.pattern
    }

    pub fn assignment(&self) -> VdSynExprIdx {
        self.assignment
    }
}

impl<'db> VdSynExprBuilder<'db> {
    pub fn build_let_assigned_resolution(
        &self,
        pattern_expr: VdSynExprIdx,
        assignment: VdSynExprIdx,
    ) -> VdSynLetAssignedResolution {
        VdSynLetAssignedResolution {
            pattern: self.build_pattern(pattern_expr),
            pattern_expr,
            assignment,
        }
    }
}

impl<'db> VdSynSymbolBuilder<'db> {
    /// Order matters!
    ///
    /// - First, build the assignment.
    /// - Then define the symbols in the pattern.
    pub(crate) fn build_let_assigned_resolution(
        &mut self,
        clause: VdSynClauseIdx,
        resolution: &VdSynLetAssignedResolution,
    ) {
        self.build_expr(resolution.assignment);
        match resolution.pattern {
            VdSynPattern::Letter(token_idx_range, letter) => {
                self.define_symbol(
                    VdSynSymbolLocalDefnHead::Letter {
                        token_idx_range,
                        letter,
                    },
                    VdSynSymbolLocalDefnBody::Assigned,
                    clause.into(),
                );
            }
        }
        self.build_expr(resolution.pattern_expr);
    }
}

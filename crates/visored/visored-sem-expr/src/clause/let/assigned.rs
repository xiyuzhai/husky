use super::*;
use pattern::VdSemPattern;
use visored_syn_expr::clause::r#let::assigned::VdSynLetAssignedResolution;

#[derive(Debug, PartialEq, Eq)]
pub struct VdSemLetAssignedDispatch {
    pattern: VdSemPattern,
    assignment: VdSemExprIdx,
}

impl ToVdSem<VdSemLetAssignedDispatch> for &VdSynLetAssignedResolution {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemLetAssignedDispatch {
        let pattern = self.pattern().to_vd_sem(builder);
        let assignment = builder.build_expr_entry(self.assignment());
        let ty = assignment.ty();
        let assignment = builder.alloc_expr(self.assignment(), assignment);
        builder.infer_pattern_symbol_tys(&pattern, ty);
        VdSemLetAssignedDispatch {
            pattern,
            assignment,
        }
    }
}

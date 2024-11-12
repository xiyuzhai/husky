use super::*;
use visored_syn_expr::clause::r#let::placeholder::VdSynLetPlaceholderResolution;

#[derive(Debug, PartialEq, Eq)]
pub struct VdSemLetPlaceholderDispatch {}

impl ToVdSem<VdSemLetPlaceholderDispatch> for &VdSynLetPlaceholderResolution {
    fn to_vd_sem(self, builder: &mut VdSemExprBuilder) -> VdSemLetPlaceholderDispatch {
        VdSemLetPlaceholderDispatch {}
    }
}

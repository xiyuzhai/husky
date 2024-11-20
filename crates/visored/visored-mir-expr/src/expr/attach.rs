use super::*;
use latex_prelude::script::LxScriptKind;
use visored_global_dispatch::dispatch::attach::VdAttachGlobalDispatch;
use visored_sem_expr::expr::attach::VdSemAttachDispatch;

impl<'db> VdMirExprBuilder<'db> {
    pub fn build_attach(
        &mut self,
        base: VdSemExprIdx,
        scripts: &[(LxScriptKind, VdSemExprIdx)],
        dispatch: VdSemAttachDispatch,
    ) -> VdMirExprData {
        match dispatch {
            VdSemAttachDispatch::GlobalPower {
                signature,
                exponent,
            } => VdMirExprData::Application {
                function: VdMirFunc::Power(signature),
                arguments: [base, exponent].to_vd_mir(self),
            },
        }
    }
}

use super::*;
use visored_global_dispatch::dispatch::attach::VdAttachGlobalDispatch;
use visored_signature::signature::attach::{VdAttachSignature, VdPowerSignature};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemAttachDispatch {
    GlobalPower {
        signature: VdPowerSignature,
        exponent: VdSemExprIdx,
    },
}

impl<'a> VdSemExprBuilder<'a> {
    pub(super) fn build_attach(
        &mut self,
        base: VdSynExprIdx,
        scripts: &[(LxScriptKind, VdSynExprIdx)],
    ) -> (VdSemExprData, VdType) {
        if let Some(data_and_ty) = self.try_build_power(base, scripts) {
            return data_and_ty;
        }
        todo!()
    }

    fn try_build_power(
        &mut self,
        syn_base: VdSynExprIdx,
        scripts: &[(LxScriptKind, VdSynExprIdx)],
    ) -> Option<(VdSemExprData, VdType)> {
        let [(LxScriptKind::Superscript, syn_exponent)] = *scripts else {
            return None;
        };
        match self.syn_expr_arena()[syn_exponent] {
            VdSynExprData::Delimited { .. } => todo!(),
            VdSynExprData::Err(_) => todo!(),
            _ => (),
        }
        // TODO: consider annotation
        // avoid allocation because we're not certain at this point
        let base = self.build_expr_entry(syn_base);
        let exponent = self.build_expr_entry(syn_exponent);
        if let Some(dispatch) = self
            .default_global_dispatch_table()
            .power_default_dispatch(base.ty, exponent.ty)
        {
            let base = self.alloc_expr(syn_base, base);
            let exponent = self.alloc_expr(syn_exponent, exponent);
            match dispatch {
                VdAttachGlobalDispatch::Normal { signature } => {
                    let VdAttachSignature::Power(signature) = signature else {
                        unreachable!()
                    };
                    return Some((
                        VdSemExprData::Attach {
                            base,
                            scripts: vec![(LxScriptKind::Superscript, exponent)],
                            dispatch: VdSemAttachDispatch::GlobalPower {
                                signature,
                                exponent,
                            },
                        },
                        dispatch.expr_ty(),
                    ));
                }
            }
        }
        todo!()
    }
}

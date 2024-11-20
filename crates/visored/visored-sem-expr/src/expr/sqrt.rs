use super::*;
use visored_global_dispatch::dispatch::sqrt::VdSqrtGlobalDispatch;
use visored_signature::signature::sqrt::VdBaseSqrtSignature;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemSqrtDispatch {
    Base { signature: VdBaseSqrtSignature },
}

impl<'a> VdSemExprBuilder<'a> {
    pub fn build_sqrt(
        &mut self,
        command_token_idx: LxMathTokenIdx,
        radicand_lcurl_token_idx: LxMathTokenIdx,
        syn_radicand: VdSynExprIdx,
        radicand_rcurl_token_idx: LxMathTokenIdx,
    ) -> (VdSemExprData, VdType) {
        let radicand = self.build_expr_entry(syn_radicand);
        if let Some(dispatch) = self
            .default_global_dispatch_table()
            .sqrt_default_dispatch(radicand.ty)
        {
            match dispatch {
                VdSqrtGlobalDispatch::Base { signature } => {
                    let expr_ty = signature.expr_ty();
                    let radicand = self.alloc_expr(syn_radicand, radicand);
                    let expr_data = VdSemExprData::Sqrt {
                        command_token_idx,
                        radicand_lcurl_token_idx,
                        radicand,
                        radicand_rcurl_token_idx,
                        dispatch: VdSemSqrtDispatch::Base { signature },
                    };
                    (expr_data, expr_ty)
                }
            }
        } else {
            todo!()
        }
    }
}

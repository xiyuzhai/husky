use super::*;
use visored_global_dispatch::dispatch::binary_opr::VdBinaryOprGlobalDispatch;
use visored_syn_expr::expr::VdSynBinaryOpr;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemBinaryOpr {
    Base(LxTokenIdxRange, VdBaseBinaryOpr),
    Composite(VdSemExprIdx, VdCompositeBinaryOpr),
}

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemBinaryDispatch {
    Global(VdBinaryOprGlobalDispatch),
}

impl<'a> VdSemExprBuilder<'a> {
    pub fn build_binary(
        &mut self,
        syn_lopd: VdSynExprIdx,
        syn_opr: VdSynBinaryOpr,
        syn_ropd: VdSynExprIdx,
    ) -> (VdSemExprData, VdType) {
        match syn_opr {
            VdSynBinaryOpr::Base(range, opr) => {
                self.build_base_binary(syn_lopd, range, opr, syn_ropd)
            }
            _ => todo!(),
        }
    }

    fn build_base_binary(
        &mut self,
        syn_lopd: VdSynExprIdx,
        range: LxTokenIdxRange,
        base_opr: VdBaseBinaryOpr,
        syn_ropd: VdSynExprIdx,
    ) -> (VdSemExprData, VdType) {
        let opr = VdSemBinaryOpr::Base(range, base_opr);
        let lopd = self.build_expr_entry(syn_lopd);
        let ropd = self.build_expr_entry(syn_ropd);
        if let Some(dispatch) = self
            .default_global_dispatch_table()
            .base_binary_opr_default_dispatch(lopd.ty, base_opr, ropd.ty)
        {
            let expr_ty = dispatch.expr_ty();
            let lopd = self.alloc_expr(syn_lopd, lopd);
            let ropd = self.alloc_expr(syn_ropd, ropd);
            (
                VdSemExprData::Binary {
                    lopd,
                    opr,
                    ropd,
                    dispatch: dispatch.into(),
                },
                expr_ty,
            )
        } else {
            todo!(
                "no default dispatch for lopd_ty = {:?}, base_opr = {:?}, ropd_ty = {:?}",
                lopd.ty,
                base_opr,
                ropd.ty
            )
        }
    }
}

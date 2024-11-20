use super::*;
use visored_global_dispatch::dispatch::prefix_opr::VdPrefixOprGlobalDispatch;
use visored_syn_expr::expr::VdSynPrefixOpr;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemPrefixOpr {
    Base(LxTokenIdxRange, VdBasePrefixOpr),
    Composite(VdSemExprIdx, VdCompositePrefixOpr),
}

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemPrefixDispatch {
    Global(VdPrefixOprGlobalDispatch),
}

impl<'a> VdSemExprBuilder<'a> {
    pub fn build_prefix(
        &mut self,
        syn_opr: VdSynPrefixOpr,
        syn_opd: VdSynExprIdx,
    ) -> (VdSemExprData, VdType) {
        match syn_opr {
            VdSynPrefixOpr::Base(opr_range, base_opr) => {
                self.build_base_prefix(opr_range, base_opr, syn_opd)
            }
            VdSynPrefixOpr::Composite(arena_idx, opr) => todo!(),
        }
    }

    fn build_base_prefix(
        &mut self,
        opr_range: LxTokenIdxRange,
        base_opr: VdBasePrefixOpr,
        syn_opd: VdSynExprIdx,
    ) -> (VdSemExprData, VdType) {
        let opr = VdSemPrefixOpr::Base(opr_range, base_opr);
        let opd = self.build_expr_entry(syn_opd);
        if let Some(dispatch) = self
            .default_global_dispatch_table()
            .base_prefix_opr_default_dispatch(base_opr, opd.ty())
        {
            let expr_ty = dispatch.expr_ty();
            let opd = self.alloc_expr(syn_opd, opd);
            (
                VdSemExprData::Prefix {
                    opr,
                    opd,
                    dispatch: dispatch.into(),
                },
                expr_ty,
            )
        } else {
            use salsa::DebugWithDb;
            todo!(
                "no default dispatch for base_opr = {:?}, opd_ty = {:?}",
                base_opr,
                opd.ty.debug(self.db())
            )
        }
    }
}

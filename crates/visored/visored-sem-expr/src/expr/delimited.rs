use visored_syn_expr::expr::{VdSynLeftDelimiter, VdSynRightDelimiter};

use super::*;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemLeftDelimiter {
    Base(LxTokenIdxRange, VdBaseLeftDelimiter),
    Composite(VdSemExprIdx, VdCompositeLeftDelimiter),
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum VdSemRightDelimiter {
    Base(LxTokenIdxRange, VdBaseRightDelimiter),
    Composite(VdSemExprIdx, VdCompositeRightDelimiter),
}

impl<'a> VdSemExprBuilder<'a> {
    pub fn build_delimited(
        &mut self,
        left_delimiter: VdSynLeftDelimiter,
        syn_item: VdSynExprIdx,
        right_delimiter: VdSynRightDelimiter,
    ) -> (VdSemExprData, VdType) {
        let left_delimiter = match left_delimiter {
            VdSynLeftDelimiter::Base(range, VdBaseLeftDelimiter::Lpar) => {
                VdSemLeftDelimiter::Base(range, VdBaseLeftDelimiter::Lpar)
            }
            _ => todo!(),
        };
        let right_delimiter = match right_delimiter {
            VdSynRightDelimiter::Base(range, VdBaseRightDelimiter::Rpar) => {
                VdSemRightDelimiter::Base(range, VdBaseRightDelimiter::Rpar)
            }
            _ => todo!(),
        };
        let item = self.build_expr_entry(syn_item);
        //
        let ty = item.ty();
        let item = self.alloc_expr(syn_item, item);
        (
            VdSemExprData::Delimited {
                left_delimiter,
                item,
                right_delimiter,
            },
            ty,
        )
    }
}

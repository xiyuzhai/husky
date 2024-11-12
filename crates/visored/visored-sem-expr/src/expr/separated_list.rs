use super::*;
use smallvec::{smallvec, SmallVec};
use visored_syn_expr::expr::VdSynExprIdxRange;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VdSemSeparatedListDispatch {
    IntAdd,
    IntMul,
    Eq,
    In,
}

impl<'db> VdSemExprBuilder<'db> {
    pub(super) fn build_separated_list(
        &mut self,
        separator_class: VdSeparatorClass,
        items: VdSynExprIdxRange,
        separators: &[VdSynSeparator],
    ) -> VdSemExprData {
        // TODO: ad hoc,should consider more based on type information, especially space.
        let dispatch = match separators.len() {
            0 => todo!(),
            1 => match separators[0] {
                VdSynSeparator::Base(_, base_separator) => match base_separator {
                    VdBaseSeparator::Space => VdSemSeparatedListDispatch::IntMul,
                    VdBaseSeparator::Comma => todo!(),
                    VdBaseSeparator::Semicolon => todo!(),
                    VdBaseSeparator::Add => VdSemSeparatedListDispatch::IntAdd,
                    VdBaseSeparator::Mul => VdSemSeparatedListDispatch::IntMul,
                    VdBaseSeparator::Dot => todo!(),
                    VdBaseSeparator::Eq => VdSemSeparatedListDispatch::Eq,
                    VdBaseSeparator::Subset => todo!(),
                    VdBaseSeparator::Supset => todo!(),
                    VdBaseSeparator::Subseteq => todo!(),
                    VdBaseSeparator::Supseteq => todo!(),
                    VdBaseSeparator::Subseteqq => todo!(),
                    VdBaseSeparator::Supseteqq => todo!(),
                    VdBaseSeparator::Subsetneq => todo!(),
                    VdBaseSeparator::Supsetneq => todo!(),
                    VdBaseSeparator::In => VdSemSeparatedListDispatch::In,
                    VdBaseSeparator::Notin => todo!(),
                    VdBaseSeparator::Times => todo!(),
                    VdBaseSeparator::Otimes => todo!(),
                    VdBaseSeparator::Ne => todo!(),
                },
                VdSynSeparator::Composite(arena_idx, vd_separator_class) => todo!(),
            },
            2 => todo!(),
            _ => todo!(),
        };
        VdSemExprData::SeparatedList {
            separator_class,
            // TODO: ad hoc, what to do for separators?
            items: items.to_vd_sem(self),
            // TODO: ad hoc, should consider much more based on type information, especially space.
            dispatch,
        }
    }
}

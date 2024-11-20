pub mod assigned;
pub mod placeholder;

use self::{assigned::VdSynLetAssignedResolution, placeholder::VdSynLetPlaceholderResolution};
use super::*;
use expr::{VdSynExprData, VdSynExprIdxRange, VdSynSeparator};
use visored_opr::separator::VdBaseSeparator;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq)]
pub enum VdSynLetClauseResolution {
    Assigned(VdSynLetAssignedResolution),
    Placeholder(VdSynLetPlaceholderResolution),
}

impl<'db> VdSynExprBuilder<'db> {
    pub(crate) fn build_let_stmt_resolution(
        &self,
        formula: VdSynExprIdx,
    ) -> VdSynLetClauseResolution {
        match self.expr_arena()[formula] {
            VdSynExprData::Literal {
                token_idx_range,
                literal,
            } => todo!(),
            VdSynExprData::Letter {
                token_idx_range,
                letter,
            } => todo!(),
            VdSynExprData::BaseOpr { opr } => todo!(),
            VdSynExprData::Binary { lopd, opr, ropd } => todo!(),
            VdSynExprData::Prefix { opr, opd } => todo!(),
            VdSynExprData::Suffix { opd, opr } => todo!(),
            VdSynExprData::SeparatedList {
                separator_class,
                items,
                ref separators,
            } => self.build_let_stmt_resolution_from_separated_list(items, separators),
            VdSynExprData::LxDelimited {
                left_delimiter_token_idx,
                left_delimiter,
                item,
                right_delimiter_token_idx,
                right_delimiter,
            } => todo!(),
            VdSynExprData::Delimited {
                left_delimiter,
                item,
                right_delimiter,
            } => todo!(),
            VdSynExprData::Attach { base, ref scripts } => todo!(),
            VdSynExprData::Fraction {
                command_token_idx,
                numerator,
                denominator,
                denominator_rcurl_token_idx,
            } => todo!(),
            VdSynExprData::Sqrt {
                command_token_idx,
                radicand_lcurl_token_idx,
                radicand,
                radicand_rcurl_token_idx,
            } => todo!(),
            VdSynExprData::UniadicChain => todo!(),
            VdSynExprData::VariadicChain => todo!(),
            VdSynExprData::UniadicArray => todo!(),
            VdSynExprData::VariadicArray => todo!(),
            VdSynExprData::Err(ref error) => todo!(),
        }
    }

    fn build_let_stmt_resolution_from_separated_list(
        &self,
        items: VdSynExprIdxRange,
        separators: &[VdSynSeparator],
    ) -> VdSynLetClauseResolution {
        match items.len() {
            0 | 1 => unreachable!(),
            2 => {
                debug_assert_eq!(separators.len(), 1);
                self.build_let_stmt_resolution_from_separated_two_items(
                    items.first().unwrap(),
                    items.last().unwrap(),
                    separators[0],
                )
            }
            _ => todo!(),
        }
    }

    fn build_let_stmt_resolution_from_separated_two_items(
        &self,
        fst: VdSynExprIdx,
        snd: VdSynExprIdx,
        separator: VdSynSeparator,
    ) -> VdSynLetClauseResolution {
        match separator {
            VdSynSeparator::Base(_, base_separator) => match base_separator {
                VdBaseSeparator::Space => todo!(),
                VdBaseSeparator::Comma => todo!(),
                VdBaseSeparator::Semicolon => todo!(),
                VdBaseSeparator::Add => todo!(),
                VdBaseSeparator::Mul => todo!(),
                VdBaseSeparator::Dot => todo!(),
                VdBaseSeparator::Eq => self.build_let_assigned_resolution(fst, snd).into(),
                VdBaseSeparator::Ne => todo!(),
                VdBaseSeparator::Lt => todo!(),
                VdBaseSeparator::Gt => todo!(),
                VdBaseSeparator::Le => todo!(),
                VdBaseSeparator::Ge => todo!(),
                VdBaseSeparator::Subset => todo!(),
                VdBaseSeparator::Supset => todo!(),
                VdBaseSeparator::Subseteq => todo!(),
                VdBaseSeparator::Supseteq => todo!(),
                VdBaseSeparator::Subseteqq => todo!(),
                VdBaseSeparator::Supseteqq => todo!(),
                VdBaseSeparator::Subsetneq => todo!(),
                VdBaseSeparator::Supsetneq => todo!(),
                VdBaseSeparator::In => self
                    .build_let_placeholder_resolution(fst, snd.into())
                    .into(),
                VdBaseSeparator::Notin => todo!(),
                VdBaseSeparator::Times => todo!(),
                VdBaseSeparator::Otimes => todo!(),
                VdBaseSeparator::Ne => todo!(),
            },
            VdSynSeparator::Composite(_, separator_class) => todo!(),
        }
    }
}

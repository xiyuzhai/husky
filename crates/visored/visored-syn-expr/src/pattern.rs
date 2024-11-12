use crate::{
    builder::VdSynExprBuilder,
    expr::{VdSynExprData, VdSynExprIdx},
};
use latex_math_letter::letter::LxMathLetter;
use latex_token::idx::LxTokenIdxRange;

#[enum_class::from_variants]
#[derive(Debug, PartialEq, Eq)]
pub enum VdSynPattern {
    Letter(LxTokenIdxRange, LxMathLetter),
}

impl<'db> VdSynExprBuilder<'db> {
    pub fn build_pattern(&self, pattern_expr: VdSynExprIdx) -> VdSynPattern {
        match self.expr_arena()[pattern_expr] {
            VdSynExprData::Literal {
                token_idx_range,
                literal,
            } => todo!(),
            VdSynExprData::Letter {
                token_idx_range,
                letter,
            } => VdSynPattern::Letter(token_idx_range, letter),
            VdSynExprData::BaseOpr { opr } => todo!(),
            VdSynExprData::Binary { lopd, opr, ropd } => todo!(),
            VdSynExprData::Prefix { opr, opd } => todo!(),
            VdSynExprData::Suffix { opd, opr } => todo!(),
            VdSynExprData::SeparatedList {
                separator_class,
                items,
                ref separators,
            } => todo!(),
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
}

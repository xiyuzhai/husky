use super::*;
use expr::{VdSynExprData, VdSynPrefixOpr};
use expr_stack::TopVdSynExpr;
use incomplete_expr::IncompleteVdSynExprData;
use latex_token::idx::LxTokenIdx;

impl<'a, 'db> VdSynExprParser<'a, 'db> {
    pub(super) fn calc_top_expr_first_token_idx(&self, top_expr: &TopVdSynExpr) -> LxTokenIdx {
        match top_expr {
            TopVdSynExpr::Complete(expr) => self.calc_expr_data_first_token_idx(expr),
            TopVdSynExpr::Incomplete(expr) => self.calc_incomplete_expr_first_token_idx(expr),
        }
    }

    pub(super) fn calc_expr_data_first_token_idx(&self, expr: &VdSynExprData) -> LxTokenIdx {
        match expr {
            VdSynExprData::Literal {
                token_idx_range, ..
            }
            | VdSynExprData::Letter {
                token_idx_range, ..
            } => token_idx_range.start(),
            VdSynExprData::BaseOpr { opr } => todo!(),
            VdSynExprData::Binary { lopd, opr, ropd } => todo!(),
            VdSynExprData::Prefix { opr, opd } => todo!(),
            VdSynExprData::Suffix { opd, opr } => todo!(),
            VdSynExprData::SeparatedList {
                separator_class,
                items,
                separators,
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
            VdSynExprData::Attach { base, scripts } => todo!(),
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
            VdSynExprData::Err(vd_syn_expr_error) => todo!(),
        }
    }

    fn calc_expr_first_token_idx(&self, expr: VdSynExprIdx) -> LxTokenIdx {
        self.calc_expr_data_first_token_idx(&self.builder.expr_arena()[expr])
    }

    fn calc_incomplete_expr_first_token_idx(&self, expr: &IncompleteVdSynExprData) -> LxTokenIdx {
        match *expr {
            IncompleteVdSynExprData::Binary { lopd, opr } => todo!(),
            IncompleteVdSynExprData::Prefix { opr } => self.calc_prefix_opr_first_token_idx(opr),
            IncompleteVdSynExprData::SeparatedList {
                separator_class,
                ref items,
                ref separators,
            } => todo!(),
            IncompleteVdSynExprData::Delimited { left_delimiter } => todo!(),
        }
    }

    fn calc_prefix_opr_first_token_idx(&self, opr: VdSynPrefixOpr) -> LxTokenIdx {
        match opr {
            VdSynPrefixOpr::Base(token_idx_range, _) => token_idx_range.start(),
            VdSynPrefixOpr::Composite(expr, _) => self.calc_expr_first_token_idx(expr),
        }
    }
}

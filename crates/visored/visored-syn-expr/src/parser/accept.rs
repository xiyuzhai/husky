use super::*;
use disambiguate::DisambiguatedAst;
use either::*;
use error::OriginalVdSynExprError;
use expr::{
    list_item::VdSynSeparatedListItem, VdSynBinaryOpr, VdSynExprClass, VdSynExprData,
    VdSynLeftDelimiter, VdSynPrefixOpr, VdSynRightDelimiter, VdSynSeparator, VdSynSuffixOpr,
};
use expr_stack::TopVdSynExpr;
use incomplete_expr::{IncompleteCallListOpr, IncompleteSeparatedListOpr, IncompleteVdSynExprData};
use latex_token::idx::{LxTokenIdx, LxTokenIdxRange};
use smallvec::smallvec;
use visored_annotation::annotation::space::VdSpaceAnnotation;
use visored_opr::{
    delimiter::{VdBaseLeftDelimiter, VdBaseRightDelimiter},
    opr::{binary::VdBaseBinaryOpr, prefix::VdBasePrefixOpr, suffix::VdBaseSuffixOpr, VdBaseOpr},
    precedence::VdPrecedence,
    separator::{VdBaseSeparator, VdSeparatorClass},
};

impl<'a, 'db> VdSynExprParser<'a, 'db> {
    pub(crate) fn accept_ast(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        token_idx_range: LxTokenIdxRange,
        ast: DisambiguatedAst,
    ) {
        match ast {
            DisambiguatedAst::Expr(expr, class) => match class {
                VdSynExprClass::Complete(_) => {
                    self.accept_complete_expr(preceding_space_annotation, expr)
                }
                VdSynExprClass::PrefixOpr => todo!(),
                VdSynExprClass::SuffixOpr => todo!(),
                VdSynExprClass::Separator => todo!(),
                VdSynExprClass::BinaryOpr => todo!(),
            },
            DisambiguatedAst::Opr(opr) => {
                self.accept_opr(preceding_space_annotation, token_idx_range, opr)
            }
            DisambiguatedAst::Separator(sep) => self.accept_separator(
                preceding_space_annotation,
                token_idx_range,
                VdSynSeparator::Base(token_idx_range, sep),
            ),
            DisambiguatedAst::LeftDelimiter(left_delimiter) => self.accept_left_delimiter(
                preceding_space_annotation,
                VdSynLeftDelimiter::Base(token_idx_range, left_delimiter),
            ),
            DisambiguatedAst::RightDelimiter(right_delimiter) => self.accept_right_delimiter(
                preceding_space_annotation,
                VdSynRightDelimiter::Base(token_idx_range, right_delimiter),
            ),
        }
    }

    fn accept_complete_expr(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        expr: VdSynExprData,
    ) {
        self.push_top_expr(preceding_space_annotation, expr.into())
    }

    fn accept_opr(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        token_idx_range: LxTokenIdxRange,
        opr: VdBaseOpr,
    ) {
        match opr {
            VdBaseOpr::Binary(opr) => self.accept_binary_opr(
                preceding_space_annotation,
                VdSynBinaryOpr::Base(token_idx_range, opr),
            ),
            VdBaseOpr::Prefix(opr) => self.accept_prefix_opr(
                preceding_space_annotation,
                VdSynPrefixOpr::Base(token_idx_range, opr),
            ),
            VdBaseOpr::Suffix(opr) => self.accept_suffix_opr(
                preceding_space_annotation,
                VdSynSuffixOpr::Base(token_idx_range, opr),
            ),
        }
    }

    fn accept_prefix_opr(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        opr: VdSynPrefixOpr,
    ) {
        if let Some(annotation) = preceding_space_annotation {
            todo!()
        }
        self.push_top_expr(
            preceding_space_annotation,
            IncompleteVdSynExprData::Prefix { opr }.into(),
        )
    }

    fn accept_suffix_opr(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        opr: VdSynSuffixOpr,
    ) {
        if let Some(annotation) = preceding_space_annotation {
            todo!()
        }
        self.take_complete_and_push_to_top(|slf, top_expr| match top_expr {
            Some(expr) => VdSynExprData::Suffix {
                opd: slf.builder.alloc_expr(expr),
                opr,
            }
            .into(),
            None => todo!(),
        })
    }

    fn accept_separator(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        token_idx_range: LxTokenIdxRange,
        separator: VdSynSeparator,
    ) {
        if let Some(annotation) = preceding_space_annotation {
            todo!()
        }
        self.reduce(separator.left_precedence_range(), Some(separator.class()));
        if separator.class() == VdSeparatorClass::SPACE {
            todo!()
        }
        match self.take_complete_expr() {
            Some(item) => {
                match self.last_incomplete_expr_mut() {
                    Some(&mut IncompleteVdSynExprData::SeparatedList {
                        separator_class,
                        ref items,
                        ref mut separators,
                    }) if separator.class() == separator_class => {
                        match items.len() > separators.len() {
                            true => separators.push(separator),
                            // `,,`
                            false => todo!("repeated separator"),
                        }
                    }
                    _ => self.push_top_expr(
                        preceding_space_annotation,
                        IncompleteVdSynExprData::SeparatedList {
                            separator_class: separator.class(),
                            items: smallvec![item],
                            separators: smallvec![separator],
                        }
                        .into(),
                    ),
                }
            }
            None => match self.last_incomplete_expr_mut() {
                Some(expr) => match *expr {
                    IncompleteVdSynExprData::Binary { lopd, opr } => todo!(),
                    IncompleteVdSynExprData::Prefix { opr } => todo!(),
                    IncompleteVdSynExprData::SeparatedList {
                        separator_class,
                        ref items,
                        ref mut separators,
                    } => {
                        if items.len() > separators.len() {
                            if separator_class == separator.class() {
                                separators.push(separator);
                            } else {
                                todo!()
                            }
                        } else {
                            todo!()
                        }
                    }
                    IncompleteVdSynExprData::Delimited {
                        left_delimiter: bra,
                    } => todo!(),
                },
                None => todo!(),
            },
        }
    }

    fn accept_binary_opr(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        opr: VdSynBinaryOpr,
    ) {
        if let Some(annotation) = preceding_space_annotation {
            todo!()
        }
        self.reduce(opr.left_precedence_range(), None);
        let lopd = self.take_complete_expr().unwrap_or(VdSynExprData::Err(
            OriginalVdSynExprError::NoLeftOperandForBinaryOperator { opr }.into(),
        ));
        let lopd = self.builder.alloc_expr(lopd);
        let incomplete_expr = IncompleteVdSynExprData::Binary { lopd, opr };
        self.push_top_expr(None, incomplete_expr.into());
    }

    fn accept_left_delimiter(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        left_delimiter: VdSynLeftDelimiter,
    ) {
        self.push_top_expr(
            preceding_space_annotation,
            IncompleteVdSynExprData::Delimited { left_delimiter }.into(),
        );
    }

    fn accept_right_delimiter(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        right_delimiter: VdSynRightDelimiter,
    ) {
        if let Some(annotation) = preceding_space_annotation {
            todo!()
        }
        self.reduce(VdPrecedenceRange::RIGHT_DELIMITER_LEFT, None);
        let Some(item) = self.take_complete_expr() else {
            use husky_print_utils::{p, DisplayIt};
            p!(self.show());
            todo!()
        };
        let Some(IncompleteVdSynExprData::Delimited { left_delimiter }) =
            self.take_last_incomplete_expr()
        else {
            todo!()
        };
        let item = self.builder.alloc_expr(item);
        let expr = VdSynExprData::Delimited {
            left_delimiter,
            item,
            right_delimiter,
        };
        self.set_complete_expr(expr);
    }
}

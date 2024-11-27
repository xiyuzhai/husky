use super::{
    error::{OriginalVdSynExprError, VdSynExprResult},
    expr::{VdSynExprArenaRef, VdSynExprData, VdSynExprIdx, VdSynSeparator},
    incomplete_expr::IncompleteVdSynExprData,
    VdSynExprParser,
};
use crate::expr::VdSynExprClass;
use either::*;
use latex_token::idx::LxTokenIdxRange;
use smallvec::{smallvec, SmallVec};
use visored_annotation::annotation::space::VdSpaceAnnotation;
use visored_opr::{
    delimiter::VdBaseLeftDelimiter,
    precedence::{VdPrecedence, VdPrecedenceRange},
    separator::{VdBaseSeparator, VdSeparatorClass},
};

#[derive(Default, Debug)]
pub(crate) struct VdSynExprStack {
    incomplete_exprs: Vec<(IncompleteVdSynExprData, VdPrecedence)>,
    complete_expr: Option<VdSynExprData>,
}

impl VdSynExprStack {
    pub fn finish(self) -> VdSynExprData {
        assert!(self.complete_expr.is_some());
        assert!(
            self.incomplete_exprs.is_empty(),
            "incomplete exprs should be empty but {:?}, complete expr: {:?}",
            self.incomplete_exprs,
            self.complete_expr
        );
        self.complete_expr.unwrap()
    }
}

#[derive(Debug)]
pub(super) enum TopVdSynExpr {
    Incomplete(IncompleteVdSynExprData),
    Complete(VdSynExprData),
}

impl From<VdSynExprData> for TopVdSynExpr {
    fn from(expr: VdSynExprData) -> Self {
        TopVdSynExpr::Complete(expr)
    }
}

impl From<IncompleteVdSynExprData> for TopVdSynExpr {
    fn from(v: IncompleteVdSynExprData) -> Self {
        TopVdSynExpr::Incomplete(v)
    }
}

impl VdSynExprStack {
    pub(super) fn prev_incomplete_expr_precedence(&self) -> Option<VdPrecedence> {
        self.incomplete_exprs
            .last()
            .map(|(_, precedence)| *precedence)
    }
}

impl<'a, 'db> VdSynExprParser<'a, 'db> {
    pub(super) fn complete_expr(&self) -> Option<&VdSynExprData> {
        self.stack.complete_expr.as_ref()
    }

    pub(super) fn incomplete_exprs(&self) -> &[(IncompleteVdSynExprData, VdPrecedence)] {
        &self.stack.incomplete_exprs
    }

    pub(super) fn might_accept_new_binary_opr_or_non_space_separator(&self) -> bool {
        self.stack.complete_expr.is_some()
            || matches!(
                self.stack.incomplete_exprs.last(),
                Some(&(
                    IncompleteVdSynExprData::SeparatedList {
                        separator_class: VdSeparatorClass::Space,
                        ..
                    },
                    _
                ))
            )
    }

    pub(super) fn take_last_incomplete_expr(&mut self) -> Option<IncompleteVdSynExprData> {
        self.stack.incomplete_exprs.pop().map(|(expr, _)| expr)
    }

    fn push_incomplete_expr(&mut self, incomplete_expr: IncompleteVdSynExprData) {
        assert!(self.stack.complete_expr.is_none());
        let precedence = incomplete_expr.precedence();
        self.stack
            .incomplete_exprs
            .push((incomplete_expr, precedence))
    }

    pub(super) fn last_incomplete_expr(&self) -> Option<&IncompleteVdSynExprData> {
        self.stack.incomplete_exprs.last().map(|(opr, _)| opr)
    }

    pub(super) fn last_incomplete_expr_mut(&mut self) -> Option<&mut IncompleteVdSynExprData> {
        self.stack.incomplete_exprs.last_mut().map(|(opr, _)| opr)
    }

    /// make `top_expr` the top expression.
    /// - if there is already a finished expression, interpret it as a function,
    /// and `top_expr` as an argument;
    /// - otherwise just adds it in the trivial way
    pub(super) fn push_top_expr(
        &mut self,
        preceding_space_annotation: Option<VdSpaceAnnotation>,
        top_expr: TopVdSynExpr,
    ) {
        if self.complete_expr().is_some() {
            match preceding_space_annotation {
                Some(annotation) => todo!(),
                _ => {
                    self.reduce(VdPrecedenceRange::SPACE_LEFT, Some(VdSeparatorClass::SPACE));
                }
            }
        };
        // Now reduction is done. If the complete expr is still not none, it means that we should start a new separated list.
        if let Some(expr) = self.take_complete_expr() {
            match preceding_space_annotation {
                Some(annotation) => todo!(),
                _ => self.push_incomplete_expr(IncompleteVdSynExprData::SeparatedList {
                    separator_class: VdSeparatorClass::SPACE,
                    items: smallvec![expr],
                    separators: smallvec![VdSynSeparator::Base(
                        LxTokenIdxRange::new_single(self.calc_top_expr_first_token_idx(&top_expr)),
                        VdBaseSeparator::Space,
                    )],
                }),
            }
        }
        match top_expr {
            TopVdSynExpr::Incomplete(incomplete_expr) => self.push_incomplete_expr(incomplete_expr),
            TopVdSynExpr::Complete(expr) => self.set_complete_expr(expr),
        }
    }

    pub(super) fn take_complete_expr(&mut self) -> Option<VdSynExprData> {
        std::mem::take(&mut self.stack.complete_expr)
    }

    pub(super) fn set_complete_expr(&mut self, expr: VdSynExprData) {
        debug_assert!(self.complete_expr().is_none());
        self.stack.complete_expr = Some(expr)
    }

    // fn reduce_aux(
    //     &mut self,
    //     f: impl Fn(&mut Self, Option<VdSynExprData>, IncompleteVdSynExprData) -> TopVdSynExpr,
    // ) {
    //     let complete_expr = self.take_complete_expr();
    //     let Some((incomplete_expr, _)) = self.stack.incomplete_exprs.pop() else {
    //         unreachable!()
    //     };
    //     let top_expr = f(self, complete_expr, incomplete_expr);
    //     self.push_top_expr(top_expr)
    // }

    pub(super) fn reduce(
        &mut self,
        precedence_range: VdPrecedenceRange,
        incoming_separator_class: Option<VdSeparatorClass>,
    ) {
        while let Some(prev_precedence) = self.stack.prev_incomplete_expr_precedence() {
            if !precedence_range.contains(prev_precedence) {
                break;
            }
            // TODO: maybe it's better to use `last_mut` first
            let (incomplete_expr, precedence) = self.stack.incomplete_exprs.pop().unwrap();
            match incomplete_expr {
                IncompleteVdSynExprData::Binary { lopd, opr } => {
                    let complete_expr = self.take_complete_expr();
                    self.stack.complete_expr = Some(match complete_expr {
                        Some(ropd) => VdSynExprData::Binary {
                            lopd,
                            opr,
                            ropd: self.builder.alloc_expr(ropd),
                        },
                        None => VdSynExprData::Err(
                            OriginalVdSynExprError::NoRightOperandForBinaryOperator { opr }.into(),
                        ),
                    })
                }
                IncompleteVdSynExprData::Prefix { opr } => {
                    let expr = self.take_complete_expr();
                    self.stack.complete_expr = Some(match expr {
                        Some(opd) => VdSynExprData::Prefix {
                            opr,
                            opd: self.builder.alloc_expr(opd),
                        },
                        None => VdSynExprData::Err(
                            OriginalVdSynExprError::NoOperandForPrefixOperator { opr }.into(),
                        ),
                    })
                }
                IncompleteVdSynExprData::SeparatedList {
                    separator_class,
                    items,
                    separators,
                } => match self.reduce_separated_list(
                    separator_class,
                    items,
                    separators,
                    incoming_separator_class,
                ) {
                    TopVdSynExpr::Incomplete(incomplete_expr) => {
                        self.push_incomplete_expr(incomplete_expr);
                        break;
                    }
                    TopVdSynExpr::Complete(complete_expr) => {
                        self.stack.complete_expr = Some(complete_expr);
                    }
                },
                IncompleteVdSynExprData::Delimited {
                    left_delimiter: bra,
                } => todo!(),
            }
        }
    }

    // assumes that the precedence of the incoming separator is higher
    fn reduce_separated_list(
        &mut self,
        separator_class: VdSeparatorClass,
        mut items: SmallVec<[VdSynExprData; 4]>,
        mut separators: SmallVec<[VdSynSeparator; 4]>,
        incoming_separator_class: Option<VdSeparatorClass>,
    ) -> TopVdSynExpr {
        let complete_expr = self.take_complete_expr();
        if let Some(expr) = complete_expr {
            match expr.class() {
                VdSynExprClass::Complete(_) => {
                    debug_assert!(
                        items.len() == separators.len() || items.len() == separators.len() + 1
                    );
                    let last_fragment_is_separator = items.len() == separators.len();
                    if last_fragment_is_separator {
                        items.push(expr);
                    } else {
                        if separator_class == VdSeparatorClass::SPACE {
                            separators.push(VdSynSeparator::Base(
                                LxTokenIdxRange::new_single(
                                    self.calc_expr_data_first_token_idx(&expr),
                                ),
                                VdBaseSeparator::Space,
                            ));
                            items.push(expr);
                        } else {
                            use husky_print_utils::p;
                            p!(self.show(), items, separators, expr, separator_class);
                            todo!("report error")
                        }
                    }
                }
                VdSynExprClass::PrefixOpr => todo!(),
                VdSynExprClass::SuffixOpr => todo!(),
                VdSynExprClass::Separator => {
                    use husky_print_utils::p;
                    p!(expr);
                    todo!()
                }
                VdSynExprClass::BinaryOpr => todo!(),
            }
        }
        if incoming_separator_class == Some(separator_class) {
            // keep collecting the separated list
            IncompleteVdSynExprData::SeparatedList {
                separator_class,
                items,
                separators,
            }
            .into()
        } else {
            // finish the separated list
            let items = self.builder.alloc_exprs(items);
            VdSynExprData::SeparatedList {
                separator_class,
                items,
                separators,
            }
            .into()
        }
    }

    /// use this when the incoming token might change the nature of the top expression
    pub(super) fn take_complete_and_push_to_top(
        &mut self,
        f: impl FnOnce(&mut Self, Option<VdSynExprData>) -> TopVdSynExpr,
    ) {
        let complete_expr = self.take_complete_expr();
        let top_expr = f(self, complete_expr);
        self.push_top_expr(None, top_expr)
    }

    pub(super) fn finish_batch(&mut self) -> Option<VdSynExprIdx> {
        assert!(self.stack.incomplete_exprs.len() == 0);
        std::mem::take(&mut self.stack.complete_expr).map(|expr| self.builder.alloc_expr(expr))
    }

    pub(super) fn last_left_delimiter(&self) -> Option<VdBaseLeftDelimiter> {
        todo!()
        // for (incomplete_expr, _) in self.stack.incomplete_exprs.iter().rev() {
        //     match incomplete_expr {
        //         IncompleteVdSynExprData::SeparatedList { bra, .. } => return Some(*bra),
        //         IncompleteVdSynExprData::CallList { .. } => todo!(),
        //         //  return Some(Delimiter::Par),
        //         _ => (),
        //     }
        // }
        // None
    }
}

impl VdSynExprStack {
    pub fn show(&self, arena: VdSynExprArenaRef) -> String {
        use std::fmt::Write;

        let mut s = "Stack { incomplete: [".to_string();
        // Show incomplete expressions with precedence
        for (i, (expr, precedence)) in self.incomplete_exprs.iter().enumerate() {
            if i > 0 {
                s += ", ";
            }
            write!(s, "(\"{}\", {})", expr.show(arena), precedence.to_string()).unwrap();
        }
        s += "], complete: ";
        if let Some(expr) = &self.complete_expr {
            write!(s, "\"{}\"", expr.show(arena)).unwrap();
        } else {
            s += "None";
        };
        s += " }";
        s
    }
}

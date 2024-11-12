use super::*;
use husky_token_data::delimiter::Delimiter;

/// stack based expression parsing.
///
/// finished expression if exists, sits on top of unfinished ones.
///
/// For example,
/// ```husky
/// a + b * (c + d
/// ```
/// in the above `c + d` would be the finished expression, `a +`, `b *` and `(c + d` would be unfinished expressions.
#[derive(Default, Debug)]
pub(crate) struct SynExprStack {
    incomplete_exprs: Vec<(IncompleteSynExprData, Precedence)>,
    complete_expr: Option<SynExprData>,
}

pub(super) enum TopSynExpr {
    Incomplete(IncompleteSynExprData),
    Complete(SynExprData),
}

pub(super) enum TopExprRef<'a> {
    Incomplete(&'a IncompleteSynExprData),
    Finished(&'a SynExprData),
    None,
}

impl From<SynExprResult<SynExprData>> for TopSynExpr {
    fn from(result: SynExprResult<SynExprData>) -> Self {
        TopSynExpr::Complete(match result {
            Ok(data) => data,
            Err(e) => SynExprData::Err(e),
        })
    }
}

impl From<SynExprData> for TopSynExpr {
    fn from(v: SynExprData) -> Self {
        TopSynExpr::Complete(v)
    }
}

impl From<IncompleteSynExprData> for TopSynExpr {
    fn from(v: IncompleteSynExprData) -> Self {
        TopSynExpr::Incomplete(v)
    }
}

impl SynExprStack {
    pub(super) fn prev_incomplete_expr_precedence(&self) -> Option<Precedence> {
        self.incomplete_exprs
            .last()
            .map(|(_, precedence)| *precedence)
    }
}

impl SynExprData {
    pub fn base_item_path(&self, db: &::salsa::Db, arena: &SynExprArena) -> BaseEntityPath {
        match self {
            SynExprData::Literal(_, _) => BaseEntityPath::None,
            SynExprData::PrincipalEntityPath {
                path_expr_idx: _,
                opt_path,
            } => match opt_path {
                &Some(path) => BaseEntityPath::Some(path.into()),
                None => todo!(),
            },
            SynExprData::MajorItemPathAssocItem {
                parent_expr_idx: _,
                parent_path: _,
                colon_colon_regional_token: _,
                ident_token: _,
            } => todo!(),
            SynExprData::TypeAsTargetItem {
                lpar_regional_token_idx,
                ty,
                as_region_token_idx,
                target: trai,
                rpar_regional_token_idx,
                colon_colon_regional_token_idx,
                ident,
                ident_regional_token_idx,
            } => todo!(),
            SynExprData::AssocItem {
                parent_expr_idx,
                colon_colon_regional_token_idx,
                ident,
                ident_regional_token_idx,
            } => todo!(),
            SynExprData::InheritedVariable { .. } | SynExprData::CurrentVariable { .. } => {
                BaseEntityPath::None
            }
            SynExprData::SelfValue(_) => todo!(),
            SynExprData::SelfType(_) => BaseEntityPath::SelfType,
            SynExprData::Binary { .. }
            | SynExprData::Prefix { .. }
            | SynExprData::Suffix { .. }
            | SynExprData::Field { .. }
            | SynExprData::MethodApplicationOrCall { .. } => BaseEntityPath::None,
            SynExprData::ExplicitApplication { .. } => todo!(),
            SynExprData::FunctionApplicationOrCall { .. } => todo!(),
            SynExprData::At {
                at_regional_token_idx: _,
                place_label_regional_token: _,
            } => todo!(),
            // although unit is a valid item,
            // but unit doesn't contains any subitem, so effectively none
            // ad hoc
            SynExprData::Unit { .. } => BaseEntityPath::None,
            SynExprData::NewTuple { .. } => todo!(),
            SynExprData::List { .. } => BaseEntityPath::None,
            SynExprData::Delimitered { item, .. } => arena[item].base_item_path(db, arena),
            SynExprData::Err(e) => BaseEntityPath::UncertainDueToError {
                inclination: match e {
                    SynExprError::Original(OriginalSynExprError::UnrecognizedIdent {
                        ident,
                        ..
                    }) => BaseEntityPathInclination::from_case(ident.case(db)),
                    // ad hoc
                    _ => BaseEntityPathInclination::FunctionOrLocalValue,
                },
            },
            SynExprData::TemplateInstantiation { template, .. } => {
                arena[template].base_item_path(db, arena)
            }
            SynExprData::Block { .. } => BaseEntityPath::None,
            SynExprData::Be { .. } => BaseEntityPath::None,
            SynExprData::BoxColonList { .. } => todo!(),
            SynExprData::FrameVarDecl { .. } => BaseEntityPath::None,
            SynExprData::IndexOrCompositionWithList { owner, .. } => {
                arena[owner].base_item_path(db, arena)
            }
            SynExprData::EmptyHtmlTag { .. } => BaseEntityPath::Err,
            SynExprData::FunctionCall { .. } => BaseEntityPath::None,
            SynExprData::Ritchie { .. }
            | SynExprData::Sorry { .. }
            | SynExprData::Todo { .. }
            | SynExprData::Unreachable { .. }
            | SynExprData::NestedBlock { .. } => BaseEntityPath::None,
            SynExprData::Closure { .. } => BaseEntityPath::None,
        }
    }
}

impl<'a, C> SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    pub(super) fn complete_expr(&self) -> Option<&SynExprData> {
        self.stack.complete_expr.as_ref()
    }

    pub(super) fn incomplete_exprs(&self) -> &[(IncompleteSynExprData, Precedence)] {
        &self.stack.incomplete_exprs
    }

    pub(super) fn take_last_incomplete_expr(&mut self) -> Option<IncompleteSynExprData> {
        self.stack.incomplete_exprs.pop().map(|(expr, _)| expr)
    }

    fn push_incomplete_expr(&mut self, incomplete_expr: IncompleteSynExprData) {
        assert!(self.stack.complete_expr.is_none());
        let precedence = incomplete_expr.precedence();
        self.stack
            .incomplete_exprs
            .push((incomplete_expr, precedence))
    }

    pub(super) fn last_incomplete_expr(&self) -> Option<&IncompleteSynExprData> {
        self.stack.incomplete_exprs.last().map(|(opr, _)| opr)
    }

    pub(super) fn last_incomplete_expr_mut(&mut self) -> Option<&mut IncompleteSynExprData> {
        self.stack.incomplete_exprs.last_mut().map(|(opr, _)| opr)
    }

    /// make `top_expr` the top expression.
    /// - if there is already a finished expression, interpret it as a function,
    /// and `top_expr` as an argument;
    /// - otherwise just adds it in the trivial way
    pub(super) fn push_top_expr(&mut self, top_expr: TopSynExpr) {
        // this is for guaranteeing that application is left associative
        if self.complete_expr().is_some() {
            self.reduce(Precedence::Application)
        };
        if let Some(function) = self.take_complete_expr() {
            self.push_incomplete_expr(IncompleteSynExprData::Application { function });
        }
        match top_expr {
            TopSynExpr::Incomplete(incomplete_expr) => self.push_incomplete_expr(incomplete_expr),
            TopSynExpr::Complete(complete_expr) => self.stack.complete_expr = Some(complete_expr),
        }
    }

    /// if there's no need for the information of unfinished expressions, call `complete_expr` would be faster
    pub(super) fn top_expr<'d>(&'d self) -> TopExprRef<'d> {
        if let Some(ref complete_expr) = self.stack.complete_expr {
            TopExprRef::Finished(complete_expr)
        } else if let Some((incomplete_expr, _)) = self.stack.incomplete_exprs.last() {
            TopExprRef::Incomplete(incomplete_expr)
        } else {
            TopExprRef::None
        }
    }

    pub(super) fn take_complete_expr(&mut self) -> Option<SynExprData> {
        std::mem::take(&mut self.stack.complete_expr)
    }

    pub(super) fn set_complete_expr(&mut self, expr: SynExprData) {
        debug_assert!(self.complete_expr().is_none());
        self.stack.complete_expr = Some(expr)
    }

    fn reduce_aux(
        &mut self,
        f: impl Fn(&mut Self, Option<SynExprData>, IncompleteSynExprData) -> TopSynExpr,
    ) {
        let complete_expr = self.take_complete_expr();
        let Some((incomplete_expr, _)) = self.stack.incomplete_exprs.pop() else {
            unreachable!()
        };
        let top_expr = f(self, complete_expr, incomplete_expr);
        self.push_top_expr(top_expr)
    }

    pub(super) fn reduce(&mut self, next_precedence: Precedence) {
        while let Some(prev_precedence) = self.stack.prev_incomplete_expr_precedence() {
            if prev_precedence < next_precedence {
                break;
            }
            // curry is right associative
            if prev_precedence == Precedence::Curry && next_precedence == Precedence::Curry {
                break;
            }
            match self.stack.incomplete_exprs.pop().unwrap().0 {
                IncompleteSynExprData::Binary {
                    lopd,
                    punctuation,
                    punctuation_regional_token_idx,
                } => {
                    let lopd = self.context_mut().alloc_expr(lopd);
                    let complete_expr = self.take_complete_expr();
                    self.stack.complete_expr = Some(match complete_expr {
                        Some(ropd) => SynExprData::Binary {
                            lopd,
                            opr: punctuation,
                            opr_regional_token_idx: punctuation_regional_token_idx,
                            ropd: self.context_mut().alloc_expr(ropd),
                        },
                        None => SynExprData::Err(
                            OriginalSynExprError::NoRightOperandForBinaryOperator {
                                punctuation,
                                punctuation_regional_token_idx,
                            }
                            .into(),
                        ),
                    })
                }
                IncompleteSynExprData::Application { function } => {
                    let argument = self.take_complete_expr().expect("");
                    let function = self.context_mut().alloc_expr(function);
                    let argument = self.context_mut().alloc_expr(argument);
                    self.stack.complete_expr = Some(SynExprData::ExplicitApplication {
                        function_expr_idx: function,
                        argument_expr_idx: argument,
                    })
                }
                IncompleteSynExprData::Prefix {
                    punctuation,
                    punctuation_regional_token_idx,
                } => {
                    let complete_expr = self.take_complete_expr();
                    self.stack.complete_expr = Some(match complete_expr {
                        Some(opd) => SynExprData::Prefix {
                            opr: punctuation,
                            opr_regional_token_idx: punctuation_regional_token_idx,
                            opd: self.context_mut().alloc_expr(opd),
                        },
                        None => SynExprData::Err(
                            OriginalSynExprError::NoOperandForPrefixOperator {
                                prefix: punctuation,
                                prefix_regional_token_idx: punctuation_regional_token_idx,
                            }
                            .into(),
                        ),
                    })
                }
                IncompleteSynExprData::CommaList {
                    bra_regional_token_idx,
                    ..
                } => {
                    self.stack.complete_expr = Some(SynExprData::Err(
                        OriginalSynExprError::UnterminatedList {
                            bra_regional_token_idx,
                        }
                        .into(),
                    ))
                }
                IncompleteSynExprData::CallList { .. } => todo!(),
                IncompleteSynExprData::Ritchie {
                    ritchie_kind_regional_token_idx,
                    ritchie_kind,
                    lpar_token,
                    argument_tys,
                    rpar_regional_token_idx,
                    light_arrow_token,
                } => {
                    let complete_expr = self.take_complete_expr();
                    self.stack.complete_expr = Some(match complete_expr {
                        Some(return_ty) => SynExprData::Ritchie {
                            ritchie_kind_regional_token_idx,
                            ritchie_kind,
                            lpar_token,
                            parameter_ty_items: argument_tys,
                            rpar_regional_token_idx,
                            light_arrow_token: Some(light_arrow_token),
                            return_ty_syn_expr_idx: Some(self.context_mut().alloc_expr(return_ty)),
                        },
                        None => SynExprData::Err(
                            OriginalSynExprError::ExpectedTypeAfterLightArrow { light_arrow_token }
                                .into(),
                        ),
                    })
                }
                IncompleteSynExprData::KeyedArgument {
                    key_regional_token_idx,
                    key,
                    eq_token: _,
                } => {
                    self.reduce_aux(|this, opt_complete_expr, incomplete_expr| {
                        let Some(argument_expr) = opt_complete_expr else {
                            todo!()
                        };
                        let argument_expr_idx = this.context_mut().alloc_expr(argument_expr);
                        match incomplete_expr {
                            IncompleteSynExprData::CommaList {
                                opr: IncompleteCommaListOpr::FunctionApplicationOrCall { function },
                                bra: _,
                                bra_regional_token_idx,
                                items,
                            } => {
                                let mut items: SmallVec<[SynCallListItem; 4]> =
                                    items.into_iter().map(Into::into).collect();
                                items.push(
                                    SynKeyedCallListItem::new(
                                        key_regional_token_idx,
                                        key,
                                        argument_expr_idx,
                                        CallListSeparator::None,
                                    )
                                    .into(),
                                );
                                IncompleteSynExprData::CallList {
                                    opr: IncompleteCallListOpr::FunctionCall {
                                        function,
                                        generic_arguments: /* ad hoc */ None,
                                    },
                                    lpar_regional_token_idx: bra_regional_token_idx,
                                    items,
                                }
                                .into()
                            }
                            IncompleteSynExprData::CommaList {
                                opr:
                                    IncompleteCommaListOpr::MethodApplicationOrCall {
                                        self_expr: _,
                                        dot_regional_token_idx: _,
                                        ident_token: _,
                                        template_arguments: _,
                                    },
                                bra: _,
                                bra_regional_token_idx: _,
                                items: _,
                            } => todo!(),
                            IncompleteSynExprData::CallList { .. } => todo!(),
                            _ => unreachable!(),
                        }
                    })
                }
            }
        }
    }

    /// use this when the incoming token might change the nature of the top expression
    pub(super) fn take_complete_and_push_to_top(
        &mut self,
        f: impl FnOnce(&mut Self, Option<SynExprData>) -> TopSynExpr,
    ) {
        let complete_expr = self.take_complete_expr();
        let top_expr = f(self, complete_expr);
        self.push_top_expr(top_expr)
    }

    pub(super) fn finish_batch(&mut self) -> Option<SynExprIdx> {
        assert!(self.stack.incomplete_exprs.len() == 0);
        std::mem::take(&mut self.stack.complete_expr)
            .map(|expr| self.context_mut().alloc_expr(expr))
    }

    pub(super) fn last_bra(&self) -> Option<Delimiter> {
        for (incomplete_expr, _) in self.stack.incomplete_exprs.iter().rev() {
            match incomplete_expr {
                IncompleteSynExprData::CommaList { bra, .. } => return Some(*bra),
                IncompleteSynExprData::CallList { .. } => return Some(Delimiter::Par),
                _ => (),
            }
        }
        None
    }

    pub(super) fn last_two_bras(&self) -> Vec<Delimiter> {
        let mut bras = vec![];
        for (incomplete_expr, _) in self.stack.incomplete_exprs.iter().rev() {
            match incomplete_expr {
                IncompleteSynExprData::CommaList { bra, .. } => {
                    bras.push(*bra);
                    if bras.len() >= 2 {
                        return bras;
                    }
                }
                _ => (),
            }
        }
        bras
    }
}

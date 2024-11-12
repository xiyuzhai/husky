use super::*;
use husky_entity_tree::helpers::tokra_region::TokraRegionDataRef;
use husky_print_utils::p;
use husky_term_prelude::ritchie::RitchieKind;
use husky_token_data::delimiter::Delimiter;
use parsec::parse_consecutive_vec_map;
use smallvec::smallvec;

impl<'a, C> SynExprParser<'a, C>
where
    C: IsSynExprContext<'a>,
{
    pub(crate) fn accept_token(&mut self, token: DisambiguatedTokenData) {
        match token {
            DisambiguatedTokenData::Literal(regional_token_idx, lit) => {
                self.accept_atom(SynExprData::Literal(regional_token_idx, lit))
            }
            DisambiguatedTokenData::IdentifiableEntityPath(expr) => self.accept_atom(expr.into()),
            DisambiguatedTokenData::InheritedVariable {
                ident,
                regional_token_idx,
                inherited_variable_idx,
                inherited_variable_kind,
            } => self.accept_atom(SynExprData::InheritedVariable {
                ident,
                regional_token_idx,
                inherited_variable_idx,
                inherited_variable_kind,
            }),
            DisambiguatedTokenData::CurrentVariable {
                ident,
                regional_token_idx,
                current_variable_idx,
                current_variable_kind,
            } => self.accept_atom(SynExprData::CurrentVariable {
                ident,
                regional_token_idx,
                current_variable_idx,
                current_variable_kind,
            }),
            DisambiguatedTokenData::SelfType(regional_token_idx) => {
                self.accept_atom(SynExprData::SelfType(regional_token_idx))
            }
            DisambiguatedTokenData::SelfValue(regional_token_idx) => {
                self.accept_atom(SynExprData::SelfValue(regional_token_idx))
            }
            DisambiguatedTokenData::Sorry { regional_token_idx } => {
                self.accept_atom(SynExprData::Sorry { regional_token_idx })
            }
            DisambiguatedTokenData::Todo { regional_token_idx } => {
                self.accept_atom(SynExprData::Todo { regional_token_idx })
            }
            DisambiguatedTokenData::Unreachable { regional_token_idx } => {
                self.accept_atom(SynExprData::Unreachable { regional_token_idx })
            }
            DisambiguatedTokenData::UnrecognizedIdent {
                regional_token_idx,
                ident,
            } => self.accept_atom(SynExprData::Err(
                OriginalSynExprError::UnrecognizedIdent {
                    regional_token_idx,
                    ident,
                }
                .into(),
            )),
            DisambiguatedTokenData::Err(e) => self.accept_atom(SynExprData::Err(e)),
            // self.accept_atom(atom),
            DisambiguatedTokenData::SynBinaryOpr(regional_token_idx, opr) => {
                self.accept_binary_opr(opr, regional_token_idx)
            }
            DisambiguatedTokenData::SynPrefixOpr(regional_token_idx, opr) => {
                self.accept_prefix_opr(opr, regional_token_idx)
            }
            DisambiguatedTokenData::SynSuffixOpr(regional_token_idx, opr) => {
                self.accept_suffix_opr(opr, regional_token_idx)
            }
            DisambiguatedTokenData::LeftDelimiter(regional_token_idx, Delimiter::NestedCurl) => {
                self.accept_block_lcurl(regional_token_idx)
            }
            DisambiguatedTokenData::RightDelimiter(_, Delimiter::NestedCurl) => {
                unreachable!()
            }
            DisambiguatedTokenData::LeftDelimiter(regional_token_idx, bra) => {
                self.accept_list_start(bra, regional_token_idx)
            }
            DisambiguatedTokenData::RightDelimiter(regional_token_idx, ket) => {
                self.accept_list_end(ket, regional_token_idx)
            }
            DisambiguatedTokenData::Dot(regional_token_idx) => {
                self.accept_dot_opr(regional_token_idx)
            }
            DisambiguatedTokenData::Comma(regional_token_idx) => {
                self.accept_comma(regional_token_idx)
            }
            DisambiguatedTokenData::Be(regional_token_idx) => {
                self.accept_be_pattern(regional_token_idx)
            }
            DisambiguatedTokenData::ColonRightAfterLbox(colon_regional_token_idx) => {
                self.accept_colon_right_after_lbox(colon_regional_token_idx)
            }
            DisambiguatedTokenData::Ritchie(regional_token_idx, ritchie_kind) => {
                self.accept_ritchie(regional_token_idx, ritchie_kind)
            }
            DisambiguatedTokenData::IncompleteKeywordArgument {
                regional_token_idx,
                ident,
                eq_token,
            } => self.accept_incomplete_keyword_argument(regional_token_idx, ident, eq_token),
            DisambiguatedTokenData::At(regional_token_idx) => self.accept_at(regional_token_idx),
            DisambiguatedTokenData::AssocItem {
                ident,
                regional_token_idx,
            } => self.accept_assoc_item(ident, regional_token_idx),
        }
    }

    fn accept_list_end(&mut self, ket: Delimiter, ket_regional_token_idx: RegionalTokenIdx) {
        self.reduce(Precedence::ListItem);
        let last_incomplete_expr = self.take_last_incomplete_expr().unwrap();
        match last_incomplete_expr {
            IncompleteSynExprData::CommaList {
                opr,
                bra,
                bra_regional_token_idx,
                mut items,
            } => {
                if bra != ket {
                    todo!()
                }
                self.take_complete_and_push_to_top(|this, complete_expr| {
                    if let Some(expr) = complete_expr {
                        items.push(SynCommaListItem::new(
                            this.context_mut().alloc_expr(expr),
                            None,
                        ))
                    }
                    match opr {
                        IncompleteCommaListOpr::UnitOrDelimiteredOrNewTuple => match items.last() {
                            None => SynExprData::Unit {
                                lpar_regional_token_idx: bra_regional_token_idx,
                                rpar_regional_token_idx: ket_regional_token_idx,
                            },
                            Some(last_item) => {
                                if items.len() == 1
                                    && last_item.comma_regional_token_idx().is_none()
                                {
                                    SynExprData::Delimitered {
                                        lpar_regional_token_idx: bra_regional_token_idx,
                                        item: last_item.syn_expr_idx(),
                                        rpar_regional_token_idx: ket_regional_token_idx,
                                    }
                                } else {
                                    SynExprData::NewTuple {
                                        lpar_regional_token_idx: bra_regional_token_idx,
                                        items,
                                        rpar_regional_token_idx: ket_regional_token_idx,
                                    }
                                }
                            }
                        }
                        .into(),
                        IncompleteCommaListOpr::Index { owner } => {
                            SynExprData::IndexOrCompositionWithList {
                                owner,
                                lbox_regional_token_idx: bra_regional_token_idx,
                                items,
                                rbox_regional_token_idx: ket_regional_token_idx,
                            }
                            .into()
                        }
                        IncompleteCommaListOpr::BoxList => SynExprData::List {
                            lbox_regional_token_idx: bra_regional_token_idx,
                            items,
                            rbox_regional_token_idx: ket_regional_token_idx,
                        }
                        .into(),
                        IncompleteCommaListOpr::BoxColonList {
                            colon_regional_token_idx,
                        } => SynExprData::BoxColonList {
                            lbox_regional_token_idx: bra_regional_token_idx,
                            colon_regional_token_idx,
                            items,
                            rbox_regional_token_idx: ket_regional_token_idx,
                        }
                        .into(),
                        IncompleteCommaListOpr::FunctionApplicationOrCall { function } => {
                            // ad hoc
                            let generic_arguments: Option<SynTemplateArguments> = None;
                            SynExprData::FunctionApplicationOrCall {
                                function,
                                template_arguments: generic_arguments,
                                lpar_regional_token_idx: bra_regional_token_idx,
                                items,
                                rpar_regional_token_idx: ket_regional_token_idx,
                            }
                            .into()
                        }
                        IncompleteCommaListOpr::MethodInstantiation { .. } => {
                            todo!()
                        }
                        IncompleteCommaListOpr::MethodApplicationOrCall {
                            self_expr,
                            dot_regional_token_idx,
                            ident_token,
                            template_arguments,
                        } => SynExprData::MethodApplicationOrCall {
                            self_argument: self_expr,
                            dot_regional_token_idx,
                            ident_token,
                            template_arguments,
                            lpar_regional_token_idx: bra_regional_token_idx,
                            items,
                            rpar_regional_token_idx: ket_regional_token_idx,
                        }
                        .into(),
                        IncompleteCommaListOpr::TemplateInstantiation { template } => {
                            SynExprData::TemplateInstantiation {
                                template,
                                template_arguments: SynTemplateArguments::new(
                                    bra_regional_token_idx,
                                    items,
                                    ket_regional_token_idx,
                                ),
                            }
                            .into()
                        }
                        IncompleteCommaListOpr::RitchieArguments {
                            ritchie_kind_regional_token_idx,
                            ritchie_kind,
                            lpar_token,
                        } => match this.try_parse_option::<LightArrowRegionalToken>() {
                            Ok(Some(light_arrow_token)) => IncompleteSynExprData::Ritchie {
                                ritchie_kind_regional_token_idx,
                                ritchie_kind,
                                lpar_token,
                                argument_tys: items,
                                rpar_regional_token_idx: ket_regional_token_idx,
                                light_arrow_token,
                            }
                            .into(),
                            Ok(None) => todo!(),
                            Err(_) => todo!(),
                        },
                    }
                })
            }
            IncompleteSynExprData::CallList {
                opr,
                lpar_regional_token_idx,
                items,
            } => match opr {
                IncompleteCallListOpr::FunctionCall {
                    function,
                    generic_arguments,
                } => self.set_complete_expr(SynExprData::FunctionCall {
                    function,
                    template_arguments: generic_arguments,
                    lpar_regional_token_idx,
                    items,
                    rpar_regional_token_idx: ket_regional_token_idx,
                }),
                IncompleteCallListOpr::MethodCall { .. } => todo!(),
            },
            _ => {
                p!(last_incomplete_expr);
                // p!(self.context.path.debug(self.db()));
                p!(ket_regional_token_idx);
                todo!()
            }
        }
    }

    fn accept_atom(&mut self, atom: SynExprData) {
        self.push_top_expr(atom.into())
    }

    fn accept_prefix_opr(
        &mut self,
        prefix: SynPrefixOpr,
        prefix_regional_token_idx: RegionalTokenIdx,
    ) {
        self.push_top_expr(
            IncompleteSynExprData::Prefix {
                punctuation: prefix,
                punctuation_regional_token_idx: prefix_regional_token_idx,
            }
            .into(),
        )
    }

    fn accept_suffix_opr(
        &mut self,
        punctuation: SynSuffixOpr,
        punctuation_regional_token_idx: RegionalTokenIdx,
    ) {
        self.take_complete_and_push_to_top(|this, top_expr| match top_expr {
            Some(expr) => SynExprData::Suffix {
                opd: this.context_mut().alloc_expr(expr),
                opr: punctuation,
                opr_regional_token_idx: punctuation_regional_token_idx,
            }
            .into(),
            None => todo!(),
        })
    }

    fn accept_dot_opr(&mut self, dot_regional_token_idx: RegionalTokenIdx) {
        self.take_complete_and_push_to_top(|this, complete_expr| match complete_expr {
            Some(self_expr) => {
                let self_expr = this.context_mut().alloc_expr(self_expr);
                match this.try_parse_option::<IdentRegionalToken>() {
                    Ok(Some(ident_token)) => match this.try_parse_option::<LparRegionalToken>() {
                        Ok(Some(lpar)) => IncompleteSynExprData::CommaList {
                            opr: IncompleteCommaListOpr::MethodApplicationOrCall {
                                self_expr,
                                dot_regional_token_idx,
                                ident_token,
                                template_arguments: None,
                            },
                            bra: Delimiter::Par,
                            bra_regional_token_idx: lpar.regional_token_idx(),
                            items: smallvec![],
                        }
                        .into(),
                        Ok(None) => match this.try_parse_option::<ColonColonLaRegionalToken>() {
                            Ok(Some(langle)) => IncompleteSynExprData::CommaList {
                                opr: IncompleteCommaListOpr::MethodInstantiation {
                                    self_expr,
                                    dot_regional_token_idx,
                                    ident_token,
                                },
                                bra: Delimiter::TurboFish,
                                bra_regional_token_idx: langle.regional_token_idx(),
                                items: smallvec![],
                            }
                            .into(),
                            Ok(None) => SynExprData::Field {
                                owner: self_expr,
                                dot_regional_token_idx,
                                ident_token,
                            }
                            .into(),
                            Err(_) => todo!(),
                        },
                        Err(e) => {
                            p!(e);
                            todo!()
                        }
                    },
                    _ => SynExprData::Err(
                        OriginalSynExprError::ExpectedIdentAfterDot {
                            dot_regional_token_idx,
                        }
                        .into(),
                    )
                    .into(),
                }
            }
            None => SynExprData::Err(
                OriginalSynExprError::ExpectedExprBeforeDot {
                    dot_regional_token_idx,
                }
                .into(),
            )
            .into(),
        })
    }

    fn accept_comma(&mut self, comma_regional_token_idx: RegionalTokenIdx) {
        match self.take_complete_expr() {
            Some(item) => {
                let item = self.context_mut().alloc_expr(item);
                match self.last_incomplete_expr_mut() {
                    Some(expr) => match expr {
                        IncompleteSynExprData::CommaList {
                            opr: _,
                            bra: _,
                            bra_regional_token_idx: _,
                            items,
                        } => {
                            items.push(SynCommaListItem::new(item, Some(comma_regional_token_idx)))
                        }
                        IncompleteSynExprData::CallList { items, .. } => items.push(
                            SynSimpleOrVariadicCallListItem::new(
                                item,
                                CallListSeparator::Comma(comma_regional_token_idx),
                            )
                            .into(),
                        ),
                        _ => unreachable!(),
                    },
                    None => unreachable!(),
                }
            }
            None => match self.last_incomplete_expr_mut() {
                Some(expr) => match expr {
                    IncompleteSynExprData::CommaList {
                        opr: _,
                        bra: _,
                        bra_regional_token_idx: _,
                        items: _,
                    } => todo!(),
                    IncompleteSynExprData::CallList { items, .. } => match items.last_mut() {
                        Some(last_item) => match last_item.separator() {
                            CallListSeparator::None => last_item
                                .set_separator(CallListSeparator::Comma(comma_regional_token_idx)),
                            CallListSeparator::Comma(_) => todo!(),
                            CallListSeparator::Semicolon(_) => todo!(),
                        },
                        None => todo!(),
                    },
                    _ => unreachable!(),
                },
                None => unreachable!(),
            },
        }
    }

    fn accept_be_pattern(&mut self, be_regional_token_idx: RegionalTokenIdx) {
        self.reduce(Precedence::Be);
        let src = self.take_complete_expr().unwrap_or(SynExprData::Err(
            OriginalSynExprError::ExpectedItemBeforeBe {
                be_regional_token_idx,
            }
            .into(),
        ));
        let src = self.context_mut().alloc_expr(src);
        let end = match self.env() {
            Some(env) => match env {
                ExprEnvironment::TypeBeforeEq => todo!(),
                ExprEnvironment::WithinDelimiteredParameterList(_) => todo!(),
                ExprEnvironment::Condition(end) => end,
            },
            None => todo!(),
        };
        let expr = SynExprData::Be {
            src,
            be_regional_token_idx,
            target: self.parse_be_variables_pattern_expected(end),
        };
        self.push_top_expr(expr.into())
    }

    fn accept_binary_opr(
        &mut self,
        binary: SynBinaryOpr,
        binary_regional_token_idx: RegionalTokenIdx,
    ) {
        self.reduce(binary.precedence());
        let lopd = self.take_complete_expr().unwrap_or(SynExprData::Err(
            OriginalSynExprError::NoLeftOperandForBinaryOperator {
                binary_regional_token_idx,
            }
            .into(),
        ));
        let incomplete_expr = IncompleteSynExprData::Binary {
            lopd,
            punctuation: binary,
            punctuation_regional_token_idx: binary_regional_token_idx,
        };
        self.push_top_expr(incomplete_expr.into())
    }

    fn accept_colon_right_after_lbox(&mut self, colon_regional_token_idx: RegionalTokenIdx) {
        #[cfg(test)]
        assert!(self.complete_expr().is_none());
        let incomplete_expr = self.take_last_incomplete_expr().unwrap();
        match incomplete_expr {
            IncompleteSynExprData::CommaList {
                opr: IncompleteCommaListOpr::BoxList,
                bra,
                bra_regional_token_idx,
                items,
            } => {
                assert!(items.is_empty());
                self.push_top_expr(
                    IncompleteSynExprData::CommaList {
                        opr: IncompleteCommaListOpr::BoxColonList {
                            colon_regional_token_idx,
                        },
                        bra,
                        bra_regional_token_idx,
                        items,
                    }
                    .into(),
                )
            }
            _ => unreachable!(),
        }
    }

    fn accept_block_lcurl(&mut self, lcurl_regional_token_idx: RegionalTokenIdx) {
        let TokraRegionDataRef::ItemDefn(tokra_region) = self.context().tokra_region_data() else {
            unreachable!()
        };
        let (asts, nested_block_end) =
            tokra_region.nested_block_ast_idx_range_and_end(lcurl_regional_token_idx);
        let stmts = self.context_mut().parse_stmts(asts);
        self.token_stream.set_state(nested_block_end);
        let syn_expr_data = match self.try_parse_expected::<NestedRcurlRegionalToken, _>(
            OriginalSynExprError::ExpectedBlockRcurl,
        ) {
            Ok(rcurl_regional_token) => SynExprData::NestedBlock {
                lcurl_regional_token_idx,
                stmts,
                rcurl_regional_token,
            },
            Err(e) => SynExprData::Err(e),
        };
        self.push_top_expr(syn_expr_data.into())
    }

    fn accept_list_start(&mut self, bra: Delimiter, bra_regional_token_idx: RegionalTokenIdx) {
        self.reduce(Precedence::Application);
        if bra == Delimiter::Vert {
            let lvert = bra_regional_token_idx;
            let closure = self.parse_closure(bra_regional_token_idx);
            self.push_top_expr(closure.into())
        } else {
            self.take_complete_and_push_to_top(|parser, complete_expr| -> TopSynExpr {
                let complete_expr = complete_expr.map(|expr| parser.context_mut().alloc_expr(expr));
                match bra {
                    Delimiter::Par => match complete_expr {
                        Some(function) => IncompleteSynExprData::CommaList {
                            opr: IncompleteCommaListOpr::FunctionApplicationOrCall { function },
                            bra,
                            bra_regional_token_idx,
                            items: smallvec![],
                        }
                        .into(),
                        None => IncompleteSynExprData::CommaList {
                            opr: IncompleteCommaListOpr::UnitOrDelimiteredOrNewTuple,
                            bra,
                            bra_regional_token_idx,
                            items: smallvec![],
                        }
                        .into(),
                    },
                    Delimiter::Box => IncompleteSynExprData::CommaList {
                        opr: match complete_expr {
                            Some(complete_expr) => IncompleteCommaListOpr::Index {
                                owner: complete_expr,
                            },
                            None => IncompleteCommaListOpr::BoxList,
                        },
                        bra,
                        bra_regional_token_idx,
                        items: smallvec![],
                    }
                    .into(),
                    Delimiter::TurboFish => match complete_expr {
                        Some(template) => IncompleteSynExprData::CommaList {
                            opr: IncompleteCommaListOpr::TemplateInstantiation { template },
                            bra,
                            bra_regional_token_idx,
                            items: smallvec![],
                        }
                        .into(),
                        None => todo!(),
                    },
                    Delimiter::NestedCurl => todo!(),
                    Delimiter::InlineCurl => SynExprData::Err(
                        OriginalSynExprError::UnexpectedInlineLcurl(bra_regional_token_idx).into(),
                    )
                    .into(),
                    Delimiter::Vert => {
                        unreachable!("Handled already")
                    }
                    Delimiter::HtmlAngle => {
                        let function_ident = match parser.try_parse_expected(
                            OriginalSynExprError::ExpectedFunctionIdentAfterOpeningHtmlBra,
                        ) {
                            Ok(function_ident) => function_ident,
                            Err(e) => return SynExprData::Err(e).into(),
                        };
                        let arguments = match parse_consecutive_vec_map(parser) {
                            Ok(arguments) => arguments,
                            Err(e) => return SynExprData::Err(e).into(),
                        };
                        match parser.try_parse_option::<EmptyHtmxKetRegionalToken>() {
                            Ok(Some(empty_html_ket)) => SynExprData::EmptyHtmlTag {
                                empty_html_bra_idx: bra_regional_token_idx,
                                function_ident,
                                arguments,
                                empty_html_ket,
                            }
                            .into(),
                            Ok(None) => todo!(),
                            Err(_) => todo!(),
                        }
                    }
                }
            })
        }
    }

    fn accept_ritchie(
        &mut self,
        ritchie_kind_regional_token_idx: RegionalTokenIdx,
        ritchie_kind: RitchieKind,
    ) {
        match self.try_parse_option::<LparRegionalToken>() {
            Ok(Some(lpar_token)) => self.push_top_expr(
                IncompleteSynExprData::CommaList {
                    opr: IncompleteCommaListOpr::RitchieArguments {
                        ritchie_kind_regional_token_idx,
                        ritchie_kind,
                        lpar_token,
                    },
                    bra: Delimiter::Par,
                    bra_regional_token_idx: lpar_token.regional_token_idx(),
                    items: smallvec![],
                }
                .into(),
            ),
            Ok(None) => todo!(),
            Err(_) => todo!(),
        }
    }

    fn accept_incomplete_keyword_argument(
        &mut self,
        key_regional_token_idx: RegionalTokenIdx,
        key: Ident,
        eq_token: EqRegionalToken,
    ) {
        self.push_top_expr(
            IncompleteSynExprData::KeyedArgument {
                key_regional_token_idx,
                key,
                eq_token,
            }
            .into(),
        )
    }

    fn accept_at(&mut self, at_regional_token_idx: RegionalTokenIdx) {
        let place_label_regional_token = self.try_parse_err_as_none();
        self.push_top_expr(
            SynExprData::At {
                at_regional_token_idx,
                place_label_regional_token,
            }
            .into(),
        )
    }

    fn accept_assoc_item(&mut self, ident: Ident, ident_regional_token_idx: RegionalTokenIdx) {
        let Some(IncompleteSynExprData::Binary {
            lopd,
            punctuation: SynBinaryOpr::ScopeResolution,
            punctuation_regional_token_idx: colon_colon_regional_token_idx,
        }) = self.take_last_incomplete_expr()
        else {
            unreachable!("this is called only when there is an incomplete binary expression")
        };
        match lopd {
            SynExprData::Delimitered {
                lpar_regional_token_idx,
                item,
                rpar_regional_token_idx,
            } => match self.syn_expr_arena()[item] {
                SynExprData::Binary {
                    lopd: ty,
                    opr: SynBinaryOpr::As,
                    opr_regional_token_idx: as_region_token_idx,
                    ropd: trai,
                } => {
                    self.push_top_expr(
                        SynExprData::TypeAsTargetItem {
                            lpar_regional_token_idx,
                            ty,
                            as_region_token_idx,
                            target: trai,
                            rpar_regional_token_idx,
                            colon_colon_regional_token_idx,
                            ident,
                            ident_regional_token_idx,
                        }
                        .into(),
                    );
                    return;
                }
                _ => (),
            },
            _ => (),
        }
        let parent_expr_idx = self.context_mut().alloc_expr(lopd);
        self.push_top_expr(
            SynExprData::AssocItem {
                parent_expr_idx,
                colon_colon_regional_token_idx,
                ident,
                ident_regional_token_idx,
            }
            .into(),
        )
    }
}

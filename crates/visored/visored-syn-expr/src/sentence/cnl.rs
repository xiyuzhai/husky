use latex_ast::ast::math::LxMathAstIdxRange;

use super::*;

impl<'db> VdSynExprBuilder<'db> {
    pub(super) fn parse_cnl_sentence(
        &mut self,
        // TODO: there's no need to peek?
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
        vibe: VdSynExprVibe,
    ) -> VdSynSentenceEntry {
        self.parse_cnl_sentence_ad_hoc(asts, vibe)
        //     let clauses = vec![self.parse_clause(token_idx, word, asts, vibe)];
        //     let end = loop {
        //         if self.peek_new_division(asts).is_some() {
        //             break VdSynSentenceEnd::Void;
        //         }
        //         if let Some(ast_idx) = asts.next() {
        //             match self.ast_arena()[ast_idx] {
        //                 LxRoseAstData::TextEdit { .. } => todo!(),
        //                 LxRoseAstData::Word(token_idx, coword) => {
        //                     self.emit_message_over_token_to_stdout(
        //                         *token_idx,
        //                         format!("coword: {}", coword),
        //                     );
        //                     todo!("coword: {}", coword)
        //                 }
        //                 LxRoseAstData::Punctuation(pucntuation_token_idx, punctuation) => {
        //                     match punctuation {
        //                         LxRosePunctuation::Comma => todo!(),
        //                         LxRosePunctuation::Period => {
        //                             break VdSynSentenceEnd::Period(pucntuation_token_idx)
        //                         }
        //                         LxRosePunctuation::Colon => todo!(),
        //                         LxRosePunctuation::Semicolon => todo!(),
        //                         LxRosePunctuation::Exclamation => todo!(),
        //                         LxRosePunctuation::Question => todo!(),
        //                         LxRosePunctuation::LeftCurl => todo!(),
        //                         LxRosePunctuation::RightCurl => todo!(),
        //                         LxRosePunctuation::LeftBox => todo!(),
        //                         LxRosePunctuation::RightBox => todo!(),
        //                         LxRosePunctuation::EscapedBackslash => todo!(),
        //                         LxRosePunctuation::EscapedLcurl => todo!(),
        //                         LxRosePunctuation::EscapedRcurl => todo!(),
        //                     }
        //                 }
        //                 LxRoseAstData::Math { .. } => todo!(),
        //                 LxRoseAstData::Delimited {
        //                     left_delimiter_token_idx,
        //                     left_delimiter,
        //                     asts,
        //                     right_delimiter_token_idx,
        //                     right_delimiter,
        //                 } => todo!(),
        //                 LxRoseAstData::CompleteCommand {
        //                     command_token_idx,
        //                     command_path,
        //                     options,
        //                     ref arguments,
        //                 } => todo!(),
        //                 LxRoseAstData::Environment { .. } => todo!(),
        //                 LxRoseAstData::NewParagraph(_) => todo!(),
        //             }
        //         } else {
        //             break VdSynSentenceEnd::Void;
        //         }
        //     };
        //     let clauses = self.alloc_clauses(clauses);
        //     let data = VdSynSentenceData::Clauses { clauses, end };
        //     // TODO: match snl mode
        //     VdSynSentenceEntry::Cnl { data }
    }

    fn parse_cnl_sentence_ad_hoc(
        &mut self,
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
        vibe: VdSynExprVibe,
    ) -> VdSynSentenceEntry {
        let tokens = self.collect_cnl_tokens(asts);
        let mut prefix = String::new();
        for (i, &token) in tokens.iter().enumerate() {
            match prefix.as_str() {
                "Let" => match token.data {
                    CnlTokenData::Word(lx_rose_token_idx, base_coword) => todo!(),
                    CnlTokenData::Math {
                        left_delimiter_token_idx,
                        math_asts,
                        right_delimiter_token_idx,
                    } => {
                        if i < tokens.len() - 2 {
                            todo!()
                        }
                        let formula = (
                            ((*left_delimiter_token_idx + 1)..*right_delimiter_token_idx).into(),
                            math_asts,
                        )
                            .to_vd_syn(self, vibe);
                        return VdSynSentenceEntry::Cnl {
                            tokens,
                            data: VdSynSentenceData::Let {
                                left_math_delimiter_token_idx: left_delimiter_token_idx,
                                formula,
                                right_math_delimiter_token_idx: right_delimiter_token_idx,
                            },
                        };
                    }
                    CnlTokenData::Punctuation(
                        lx_rose_token_idx,
                        lx_rose_punctuation,
                        cnl_punctuation,
                    ) => todo!(),
                },
                "Assume" => todo!(),
                "Then" | "We have" => todo!(),
                "It's enough to show" | "It's enough to prove" => todo!(),
                "" => match token.data {
                    CnlTokenData::Math {
                        left_delimiter_token_idx,
                        math_asts,
                        right_delimiter_token_idx,
                    } => todo!(),
                    _ => (),
                },
                _ => (),
            }
            match token.data {
                CnlTokenData::Word(_, base_coword) => prefix.push_str(&base_coword.to_string()),
                CnlTokenData::Math { .. } => todo!(),
                CnlTokenData::Punctuation(_, _, punctuation) => todo!(),
            }
        }
        todo!()
    }

    fn collect_cnl_tokens(
        &mut self,
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
    ) -> Vec<CnlToken> {
        let mut tokens = vec![];
        while let Some(token) = self.next_cnl_token(asts) {
            tokens.push(token);
            match token.data {
                CnlTokenData::Word(_, _) => (),
                CnlTokenData::Math { .. } => (),
                CnlTokenData::Punctuation(_, _, punctuation) => match punctuation {
                    CnlPunctuation::Comma => todo!(),
                    CnlPunctuation::Period => break,
                    CnlPunctuation::Colon => todo!(),
                    CnlPunctuation::Semicolon => todo!(),
                },
            }
        }
        tokens
    }

    fn next_cnl_token(
        &mut self,
        asts: &mut Peekable<impl Iterator<Item = LxRoseAstIdx>>,
    ) -> Option<CnlToken> {
        let ast = asts.next()?;
        let data = match self.ast_arena()[ast] {
            LxRoseAstData::TextEdit { ref buffer } => todo!(),
            LxRoseAstData::Word(lx_rose_token_idx, base_coword) => {
                CnlTokenData::Word(lx_rose_token_idx, base_coword)
            }
            LxRoseAstData::Punctuation(lx_rose_token_idx, lx_rose_punctuation) => {
                let punctuation = match lx_rose_punctuation {
                    LxRosePunctuation::Comma => CnlPunctuation::Comma,
                    LxRosePunctuation::Period => CnlPunctuation::Period,
                    LxRosePunctuation::Colon => CnlPunctuation::Colon,
                    LxRosePunctuation::Semicolon => CnlPunctuation::Semicolon,
                    LxRosePunctuation::Exclamation => todo!(),
                    LxRosePunctuation::Question => todo!(),
                    LxRosePunctuation::LeftCurl => todo!(),
                    LxRosePunctuation::RightCurl => todo!(),
                    LxRosePunctuation::LeftBox => todo!(),
                    LxRosePunctuation::RightBox => todo!(),
                    LxRosePunctuation::EscapedBackslash => todo!(),
                    LxRosePunctuation::EscapedLcurl => todo!(),
                    LxRosePunctuation::EscapedRcurl => todo!(),
                };
                CnlTokenData::Punctuation(lx_rose_token_idx, lx_rose_punctuation, punctuation)
            }
            LxRoseAstData::Math {
                left_delimiter_token_idx,
                math_asts,
                right_delimiter_token_idx,
            } => CnlTokenData::Math {
                left_delimiter_token_idx,
                math_asts,
                right_delimiter_token_idx,
            },
            LxRoseAstData::Delimited {
                left_delimiter_token_idx,
                left_delimiter,
                asts,
                right_delimiter_token_idx,
                right_delimiter,
            } => todo!(),
            LxRoseAstData::CompleteCommand {
                command_token_idx,
                command_path,
                options,
                ref arguments,
            } => todo!(),
            LxRoseAstData::Environment {
                begin_command_token_idx,
                begin_lcurl_token_idx,
                begin_environment_name_token_idx,
                begin_rcurl_token_idx,
                environment_signature,
                asts,
                end_command_token_idx,
                end_lcurl_token_idx,
                end_environment_name_token_idx,
                end_rcurl_token_idx,
            } => todo!(),
            LxRoseAstData::NewParagraph(lx_rose_token_idx) => todo!(),
        };
        Some(CnlToken { lx_ast: ast, data })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CnlToken {
    pub lx_ast: LxRoseAstIdx,
    pub data: CnlTokenData,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CnlTokenData {
    Word(LxRoseTokenIdx, BaseCoword),
    Math {
        left_delimiter_token_idx: LxRoseTokenIdx,
        math_asts: LxMathAstIdxRange,
        right_delimiter_token_idx: LxRoseTokenIdx,
    },
    Punctuation(LxRoseTokenIdx, LxRosePunctuation, CnlPunctuation),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CnlPunctuation {
    Comma,
    Period,
    Colon,
    Semicolon,
}

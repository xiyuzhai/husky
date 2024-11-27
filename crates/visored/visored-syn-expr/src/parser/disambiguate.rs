use super::{
    expr::{VdSynExprClass, VdSynExprData, VdSynExprIdx},
    VdSynExprParser,
};
use latex_ast::ast::math::{
    LxMathAstData, LxMathAstIdx, LxMathCommandArgumentData, LxMathCompleteCommandArgument,
};
use latex_command::path::LxCommandPath;
use latex_math_letter::letter::LxMathLetter;
use latex_math_punctuation::LxMathPunctuation;
use latex_token::{
    idx::{LxMathTokenIdx, LxTokenIdxRange},
    token::math::digit::LxMathDigit,
};
use visored_annotation::annotation::{space::VdSpaceAnnotation, token::VdTokenAnnotation};
use visored_global_resolution::resolution::{
    command::VdCompleteCommandGlobalResolution, punctuation::VdPunctuationGlobalResolution,
};
use visored_opr::{
    delimiter::{VdBaseLeftDelimiter, VdBaseRightDelimiter},
    opr::VdBaseOpr,
    precedence::VdPrecedence,
    separator::VdBaseSeparator,
};
use visored_term::term::literal::{VdLiteral, VdLiteralData};

#[derive(Debug)]
pub enum DisambiguatedAst {
    Expr(VdSynExprData, VdSynExprClass),
    Opr(VdBaseOpr),
    Separator(VdBaseSeparator),
    LeftDelimiter(VdBaseLeftDelimiter),
    RightDelimiter(VdBaseRightDelimiter),
}

impl<'a, 'db> VdSynExprParser<'a, 'db> {
    pub fn resolve_token(
        &mut self,
        next: &mut LxMathAstIdx,
        end: LxMathAstIdx,
    ) -> DisambiguatedAst {
        use crate::builder::ToVdSyn;

        let ast_data = &self.builder.ast_arena()[*next];
        *next += 1;
        match *ast_data {
            LxMathAstData::PlainLetter(token_idx, letter) => {
                if let Some(token_annotation) =
                    self.builder.annotations().token_annotation(*token_idx)
                {
                    match token_annotation {
                        VdTokenAnnotation::Integral(lx_integral_annotation) => todo!(),
                        VdTokenAnnotation::Variable(lx_variable_annotation) => todo!(),
                        VdTokenAnnotation::Differential => {
                            return DisambiguatedAst::Opr(VdBaseOpr::DIFFERENTIAL)
                        }
                    }
                }
                DisambiguatedAst::Expr(
                    VdSynExprData::Letter {
                        token_idx_range: LxTokenIdxRange::new_single(*token_idx),
                        letter,
                    },
                    VdSynExprClass::ATOM,
                )
            }
            LxMathAstData::StyledLetter {
                style_command_token_idx,
                style_lcurl_token_idx,
                plain_letter_token_idx,
                style_rcurl_token_idx,
                style,
                styled_letter,
            } => {
                if let Some(token_annotation) = self
                    .builder
                    .annotations()
                    .token_annotation(*style_command_token_idx)
                {
                    return todo!();
                }
                if let Some(token_annotation) = self
                    .builder
                    .annotations()
                    .token_annotation(*plain_letter_token_idx)
                {
                    return todo!();
                }
                DisambiguatedAst::Expr(
                    VdSynExprData::Letter {
                        token_idx_range: LxTokenIdxRange::new_closed(
                            *style_command_token_idx,
                            *style_rcurl_token_idx,
                        ),
                        letter: styled_letter,
                    },
                    VdSynExprClass::ATOM,
                )
            }
            LxMathAstData::Punctuation(token_idx, punctuation) => {
                if let Some(token_annotation) =
                    self.builder.annotations().token_annotation(*token_idx)
                {
                    return todo!();
                }
                match self
                    .builder
                    .default_resolution_table()
                    .resolve_punctuation(punctuation)
                {
                    Some(resolution) => match resolution {
                        VdPunctuationGlobalResolution::Opr(opr) => DisambiguatedAst::Opr(opr),
                        VdPunctuationGlobalResolution::Separator(separator) => {
                            DisambiguatedAst::Separator(separator)
                        }
                        VdPunctuationGlobalResolution::LeftDelimiter(left_delimiter) => {
                            DisambiguatedAst::LeftDelimiter(left_delimiter)
                        }
                        VdPunctuationGlobalResolution::RightDelimiter(right_delimiter) => {
                            DisambiguatedAst::RightDelimiter(right_delimiter)
                        }
                        VdPunctuationGlobalResolution::Todo => {
                            todo!("punctuation = {:?}", punctuation)
                        }
                        VdPunctuationGlobalResolution::PrefixOrBinaryOpr(
                            base_prefix_opr,
                            base_binary_opr,
                        ) => {
                            if self.might_accept_new_binary_opr_or_non_space_separator() {
                                DisambiguatedAst::Opr(base_binary_opr.into())
                            } else {
                                DisambiguatedAst::Opr(base_prefix_opr.into())
                            }
                        }
                        VdPunctuationGlobalResolution::PrefixOprOrSeparator(
                            base_prefix_opr,
                            base_separator,
                        ) => {
                            if self.might_accept_new_binary_opr_or_non_space_separator() {
                                DisambiguatedAst::Separator(base_separator)
                            } else {
                                DisambiguatedAst::Opr(base_prefix_opr.into())
                            }
                        }
                    },
                    None => todo!(),
                }
            }
            LxMathAstData::Digit(first_token_idx, digit) => {
                let mut last_token_idx = first_token_idx;
                let mut last_offset_end = self.builder.token_storage()[*first_token_idx]
                    .text_offset_range()
                    .end();
                let mut s = String::from(digit.char());
                enum LiteralNumberKind {
                    NaturalNumber,
                    Float,
                }
                let mut literal_number_kind = LiteralNumberKind::NaturalNumber;
                // TODO: handle real number by using a kind variable, literal number kind
                while *next < end {
                    match self.builder.ast_arena()[*next] {
                        LxMathAstData::Digit(token_idx, digit) => {
                            let offset_range =
                                self.builder.token_storage()[*token_idx].text_offset_range();
                            if offset_range.start() != last_offset_end {
                                break;
                            }
                            if let Some(space_annotation) = self
                                .builder
                                .annotations()
                                .preceding_space_annotation(*token_idx)
                            {
                                match space_annotation {
                                    VdSpaceAnnotation::Apply(apply_annotation) => todo!(),
                                    VdSpaceAnnotation::Sever(sever_annotation) => todo!(),
                                }
                            }
                            last_token_idx = token_idx;
                            last_offset_end = offset_range.end();
                            s.push(digit.char())
                        }
                        LxMathAstData::Punctuation(token_idx, LxMathPunctuation::Ldot) => {
                            match literal_number_kind {
                                LiteralNumberKind::NaturalNumber => {
                                    literal_number_kind = LiteralNumberKind::Float;
                                }
                                LiteralNumberKind::Float => todo!(),
                            }
                            last_token_idx = token_idx;
                            let offset_range =
                                self.builder.token_storage()[*token_idx].text_offset_range();
                            last_offset_end = offset_range.end();
                            s.push('.');
                        }
                        // TODO: handle scientific notation 2e3
                        _ => break,
                    }
                    *next += 1;
                }
                let data = match literal_number_kind {
                    LiteralNumberKind::NaturalNumber => VdLiteralData::NaturalNumber(s),
                    LiteralNumberKind::Float => VdLiteralData::Float(s),
                };
                let expr_data = VdSynExprData::Literal {
                    token_idx_range: LxTokenIdxRange::new_closed(*first_token_idx, *last_token_idx),
                    literal: VdLiteral::new(data),
                };
                DisambiguatedAst::Expr(expr_data, VdSynExprClass::ATOM)
            }
            LxMathAstData::TextEdit { ref buffer } => todo!(),
            LxMathAstData::Attach { base, ref scripts } => {
                let base = base.to_vd_syn(self.builder);
                let scripts = scripts
                    .iter()
                    .copied()
                    .map(|(script_kind, script)| (script_kind, script.to_vd_syn(self.builder)))
                    .collect();
                DisambiguatedAst::Expr(
                    VdSynExprData::Attach { base, scripts },
                    VdSynExprClass::ATOM,
                )
            }
            LxMathAstData::Delimited {
                left_delimiter_token_idx,
                left_delimiter,
                asts,
                right_delimiter_token_idx,
                right_delimiter,
            } => DisambiguatedAst::Expr(
                VdSynExprData::LxDelimited {
                    left_delimiter_token_idx,
                    left_delimiter,
                    item: (
                        ((*left_delimiter_token_idx + 1)..(*right_delimiter_token_idx)).into(),
                        asts,
                    )
                        .to_vd_syn(self.builder),
                    right_delimiter_token_idx,
                    right_delimiter,
                },
                VdSynExprClass::ATOM,
            ),
            LxMathAstData::CompleteCommand {
                command_token_idx,
                command_path,
                ref arguments,
            } => self.resolve_complete_command(command_token_idx, command_path, arguments),
            LxMathAstData::Environment { .. } => todo!(),
        }
    }

    fn resolve_complete_command(
        &mut self,
        command_token_idx: LxMathTokenIdx,
        command_path: LxCommandPath,
        arguments: &[LxMathCompleteCommandArgument],
    ) -> DisambiguatedAst {
        use crate::builder::ToVdSyn;

        let Some(resolve_complete_command) = self
            .builder
            .default_resolution_table()
            .resolve_complete_command(command_path)
        else {
            todo!("command_path = {:?}", command_path)
        };
        match resolve_complete_command {
            VdCompleteCommandGlobalResolution::Letter(letter) => {
                let token_idx_range = match arguments.last() {
                    Some(argument) => {
                        LxTokenIdxRange::new_closed(*command_token_idx, *argument.rcurl_token_idx())
                    }
                    None => LxTokenIdxRange::new_single(*command_token_idx),
                };
                DisambiguatedAst::Expr(
                    VdSynExprData::Letter {
                        token_idx_range,
                        letter,
                    },
                    VdSynExprClass::ATOM,
                )
            }
            VdCompleteCommandGlobalResolution::Todo => {
                todo!("command_path = {:?}", command_path)
            }
            VdCompleteCommandGlobalResolution::Item(_) => todo!(),
            VdCompleteCommandGlobalResolution::Frac => {
                debug_assert!(arguments.len() == 2);
                let [numerator_arg, denominator_arg] = arguments else {
                    unreachable!()
                };
                let LxMathCommandArgumentData::Math(numerator_asts) = *numerator_arg.data() else {
                    unreachable!()
                };
                let numerator =
                    (numerator_arg.asts_token_idx_range(), numerator_asts).to_vd_syn(self.builder);
                let LxMathCommandArgumentData::Math(denominator_asts) = *denominator_arg.data()
                else {
                    unreachable!()
                };
                let denominator = (denominator_arg.asts_token_idx_range(), denominator_asts)
                    .to_vd_syn(self.builder);
                DisambiguatedAst::Expr(
                    VdSynExprData::Fraction {
                        command_token_idx,
                        numerator,
                        denominator,
                        denominator_rcurl_token_idx: denominator_arg.rcurl_token_idx(),
                    },
                    VdSynExprClass::ATOM,
                )
            }
            VdCompleteCommandGlobalResolution::Sqrt => {
                debug_assert!(arguments.len() == 1);
                let [radicand_arg] = arguments else {
                    unreachable!()
                };
                let LxMathCommandArgumentData::Math(radicand_asts) = *radicand_arg.data() else {
                    unreachable!()
                };
                let radicand =
                    (radicand_arg.asts_token_idx_range(), radicand_asts).to_vd_syn(self.builder);
                DisambiguatedAst::Expr(
                    VdSynExprData::Sqrt {
                        command_token_idx,
                        radicand_lcurl_token_idx: radicand_arg.lcurl_token_idx(),
                        radicand,
                        radicand_rcurl_token_idx: radicand_arg.rcurl_token_idx(),
                    },
                    VdSynExprClass::ATOM,
                )
            }
            VdCompleteCommandGlobalResolution::Text => todo!(),
            VdCompleteCommandGlobalResolution::Opr(vd_base_opr) => {
                DisambiguatedAst::Opr(vd_base_opr)
            }
            VdCompleteCommandGlobalResolution::Separator(vd_separator) => {
                DisambiguatedAst::Separator(vd_separator)
            }
            VdCompleteCommandGlobalResolution::UsePackage => todo!(),
            VdCompleteCommandGlobalResolution::NewDivision(_) => todo!(),
            VdCompleteCommandGlobalResolution::DocumentClass => todo!(),
        }
    }
}

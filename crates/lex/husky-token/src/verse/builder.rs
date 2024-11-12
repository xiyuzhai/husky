use super::*;

pub(super) struct TokenVersesBuilder<'a> {
    tokens: &'a [TokenData],
    token_ranges: &'a [TextRange],
    line_starts: &'a [usize],
    main_sequence: MainTokenVerseSequence,
    nested_sequences: VecMap<NestedTokenVerseSequence>,
}

impl<'a> TokenVersesBuilder<'a> {
    pub(super) fn new(
        tokens_data: &'a [TokenData],
        token_ranges: &'a [TextRange],
        line_starts: &'a [usize],
    ) -> Self {
        Self {
            tokens: tokens_data,
            token_ranges,
            line_starts,
            main_sequence: Default::default(),
            nested_sequences: Default::default(),
        }
    }

    pub(crate) fn build_all(mut self) -> TokenVerses {
        self.build_main_sequence();
        self.finish()
    }

    fn build_main_sequence(&mut self) {
        let token_verses_data = self.build_token_verse_datas(&mut 0, 0);
        self.main_sequence = MainTokenVerseSequence::new(token_verses_data)
    }

    pub(crate) fn build_token_verse_datas(
        &mut self,
        i: &mut usize,
        indent0: u32,
    ) -> Vec<TokenVerseData> {
        use ControlFlow::*;

        enum ControlFlow {
            Break,
            Continue,
        }

        let Self {
            tokens: tokens_data,
            token_ranges,
            line_starts,
            ..
        } = *self;
        let mut token_verse_starts = vec![];
        let mut state = TokenVerseProductionState::None;
        while *i < line_starts.len() {
            let line0_start = line_starts[*i];
            let line0_indent = token_ranges[line0_start].start.col.index32();
            if line0_indent < indent0 {
                return token_verse_starts;
            }
            token_verse_starts.push(TokenVerseData::new(
                TokenVerseStart::from_index(line0_start),
                line0_indent,
            ));
            state = match tokens_data[line0_start] {
                TokenData::Keyword(Keyword::Stmt(StmtKeyword::Match)) => {
                    TokenVerseProductionState::Match
                }
                TokenData::Punctuation(Punctuation::VERT) => match state {
                    TokenVerseProductionState::None => TokenVerseProductionState::None,
                    TokenVerseProductionState::Match | TokenVerseProductionState::MatchVertical => {
                        TokenVerseProductionState::MatchVertical
                    }
                },
                _ => TokenVerseProductionState::None,
            };
            *i = {
                let mut j = *i + 1;
                while j < line_starts.len() {
                    let line1_start = line_starts[j];
                    let line1_start_token_data = &tokens_data[line1_start];
                    let line1_indent = token_ranges[line1_start].start.col.index32();
                    let control_flow = if line1_indent > line0_indent {
                        // detected an indentation
                        match tokens_data[line1_start - 1] {
                            TokenData::Keyword(Keyword::End(_))
                            | TokenData::Punctuation(Punctuation::EQ)
                            | TokenData::Punctuation(Punctuation::HEAVY_ARROW)
                            | TokenData::Punctuation(Punctuation::COLON) => Break,
                            TokenData::NESTED_LCURL => {
                                let prev_line_len = line1_start - line_starts[j - 1];
                                let nested = match prev_line_len {
                                    0 => unreachable!(),
                                    1 => true,
                                    _ => match tokens_data[line1_start - 2] {
                                        // `| {` or `= {`
                                        TokenData::VERTICAL | TokenData::EQ => true,
                                        _ => false,
                                    },
                                };
                                if nested {
                                    let verse_datas =
                                        self.build_token_verse_datas(&mut j, line1_indent);
                                    let end =
                                        line_starts.get(j).copied().unwrap_or(self.tokens.len());
                                    self.nested_sequences
                                        .insert_new(NestedTokenVerseSequence::new(
                                            TokenIdx::from_index(line1_start - 1),
                                            verse_datas,
                                            TokenIdx::from_index(end),
                                        ))
                                        .unwrap();
                                    Continue
                                } else {
                                    Continue
                                }
                            }
                            TokenData::INLINE_LCURL => {
                                let prev_line_len = line1_start - line_starts[j - 1];
                                let nested = match prev_line_len {
                                    0 => unreachable!(),
                                    1 => true,
                                    _ => match tokens_data[line1_start - 2] {
                                        // `| {` or `= {`
                                        TokenData::VERTICAL | TokenData::EQ => true,
                                        _ => false,
                                    },
                                };
                                if nested {
                                    self.build_token_verse_datas(&mut j, line1_indent);
                                    Continue
                                } else {
                                    Continue
                                }
                            }
                            TokenData::Punctuation(
                                Punctuation::LPAR | Punctuation::LBOX | Punctuation::LA_OR_LT,
                            ) => Continue,
                            _ => match line1_start_token_data {
                                TokenData::Keyword(kw) => match kw {
                                    Keyword::Stmt(_) | Keyword::Impl => Break,
                                    _ => Continue,
                                },
                                _ => Continue,
                            },
                        }
                    } else if line1_indent == line0_indent {
                        match line1_start_token_data {
                            TokenData::Punctuation(
                                Punctuation::RPAR
                                | Punctuation::RBOX
                                | Punctuation::NESTED_LCURL
                                | Punctuation::INLINE_RCURL
                                | Punctuation::RA_OR_GT,
                            ) => Continue,
                            TokenData::Punctuation(Punctuation::VERT) => match state {
                                TokenVerseProductionState::None
                                | TokenVerseProductionState::Match => Break,
                                TokenVerseProductionState::MatchVertical => {
                                    if tokens_data[line_starts[j - 1]..line1_start]
                                        .contains(&TokenData::Punctuation(Punctuation::HEAVY_ARROW))
                                    {
                                        Break
                                    } else {
                                        Continue
                                    }
                                }
                            },
                            _ => Break,
                        }
                    } else {
                        Break
                    };
                    match control_flow {
                        Break => break,
                        Continue => j += 1,
                    }
                }
                j
            }
        }
        token_verse_starts
    }

    fn finish(self) -> TokenVerses {
        TokenVerses {
            main_sequence: self.main_sequence,
            nested_sequences: self.nested_sequences,
        }
    }
}

pub enum TokenVerseProductionState {
    None,
    Match,
    MatchVertical,
}

pub(super) fn produce_line_starts(token_ranges: &[TextRange]) -> Vec<usize> {
    (0..token_ranges.len())
        .filter_map(|line_start| {
            if line_start == 0 {
                Some(0)
            } else if token_ranges[line_start - 1].end.line < token_ranges[line_start].start.line {
                Some(line_start)
            } else {
                None
            }
        })
        .collect()
}

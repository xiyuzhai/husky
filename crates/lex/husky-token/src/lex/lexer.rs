use crate::indent::INDENT_INCR;

use super::*;
use husky_text_protocol::position::TextLine;

pub(crate) struct Tokenizer<'lex> {
    db: &'lex ::salsa::Db,
    token_datas: Vec<TokenData>,
    token_ranges: Vec<TextRange>,
    line: TextLine,
    comments: Vec<Comment>,
}

enum TokenizerAction {
    Push((TokenData, TextRange)),
    Comment(TextRange),
    ReplaceLast((TokenData, TextRange)),
    NewLine,
}

impl<'token> Tokenizer<'token> {
    pub fn new(db: &'token ::salsa::Db) -> Self {
        Self {
            db,
            token_datas: vec![],
            token_ranges: vec![],
            line: Default::default(),
            comments: vec![],
        }
    }

    pub fn finish(self) -> RangedTokenSheet {
        RangedTokenSheet::new(self.db, self.token_datas, self.token_ranges, self.comments)
    }

    pub(crate) fn push_tokens(&mut self, pretoken_iter: impl Iterator<Item = RangedPretoken>) {
        for pretoken in pretoken_iter {
            match self.resolve_token(pretoken) {
                TokenizerAction::Push((token, token_range)) => {
                    self.token_datas.push(token);
                    self.token_ranges.push(token_range)
                }
                TokenizerAction::ReplaceLast((token, token_range)) => {
                    *self.token_datas.last_mut().unwrap() = token;
                    *self.token_ranges.last_mut().unwrap() = token_range
                }
                TokenizerAction::NewLine => self.line = self.line.to_next_line(),
                TokenizerAction::Comment(range) => self.comments.push(Comment::new(
                    CommentKind::Todo,
                    self.token_datas.len(),
                    range,
                )),
            }
        }
    }

    fn resolve_token(&self, ranged_pretoken: RangedPretoken) -> TokenizerAction {
        match ranged_pretoken.pretoken {
            Pretoken::Certain(kind) => TokenizerAction::Push((kind, ranged_pretoken.range)),
            Pretoken::Literal(lit) => match self.token_datas.last() {
                Some(TokenData::Punctuation(Punctuation::MINUS)) => {
                    let token_data = match lit.negative(self.db) {
                        Some(lit) => TokenData::Literal(lit),
                        None => TokenDataError::NoNegativeForLiteral(lit).into(),
                    };
                    TokenizerAction::ReplaceLast((token_data, ranged_pretoken.range))
                }
                _ => TokenizerAction::Push((TokenData::Literal(lit), ranged_pretoken.range)),
            },
            Pretoken::NewLine => TokenizerAction::NewLine,
            Pretoken::Ambiguous(punc) => match punc {
                AmbiguousPretoken::SubOrMinus => {
                    let token = match self.right_convexity() {
                        Convexity::Convex => TokenData::Punctuation(Punctuation::SUB),
                        Convexity::Concave | Convexity::Any => {
                            TokenData::Punctuation(Punctuation::MINUS)
                        }
                    };
                    TokenizerAction::Push((token, ranged_pretoken.range))
                }
                AmbiguousPretoken::For => match self.last_token_in_unfinished_line() {
                    Some(_) => TokenizerAction::Push((
                        TokenData::Keyword(ConnectionKeyword::For.into()),
                        ranged_pretoken.range,
                    )),
                    None => TokenizerAction::Push((
                        TokenData::Keyword(StmtKeyword::NonImplFor.into()),
                        ranged_pretoken.range,
                    )),
                },
                AmbiguousPretoken::Lcurl => {
                    let token = match self.last_token_in_unfinished_line() {
                        None
                        | Some(TokenData::EQ | TokenData::VERTICAL | TokenData::Keyword(_)) => {
                            TokenData::NESTED_LCURL
                        }
                        _ => TokenData::INLINE_LCURL,
                    };
                    TokenizerAction::Push((token, ranged_pretoken.range))
                }
                AmbiguousPretoken::Rcurl => {
                    let token_data = match self.last_token_in_unfinished_line() {
                        Some(_) => TokenData::INLINE_RCURL,
                        None => {
                            debug_assert_eq!(self.token_datas.len(), self.token_ranges.len());
                            let mut token_data = TokenData::INLINE_RCURL;
                            for i in (0..self.token_datas.len()).into_iter().rev() {
                                let token_range = self.token_ranges[i];
                                if token_range.start.col <= ranged_pretoken.range.start.col {
                                    break;
                                }
                                if token_range.start.col
                                    == ranged_pretoken.range.start.col + INDENT_INCR
                                {
                                    token_data = match i {
                                        0 => TokenData::Error(
                                            TokenDataError::RcurlMissingMatchingLcurl,
                                        ),
                                        _ => match self.token_datas[i - 1] {
                                            TokenData::NESTED_LCURL => TokenData::NESTED_RCURL,
                                            _ => TokenData::INLINE_RCURL,
                                        },
                                    };
                                    break;
                                }
                            }
                            token_data
                        }
                    };
                    TokenizerAction::Push((token_data, ranged_pretoken.range))
                }
            },
            Pretoken::Comment => TokenizerAction::Comment(ranged_pretoken.range),
            Pretoken::Err(e) => TokenizerAction::Push((TokenData::Error(e), ranged_pretoken.range)),
        }
    }

    fn right_convexity(&self) -> Convexity {
        match self.last_token_in_unfinished_line() {
            Some(token) => token.right_convexity(),
            None => Convexity::Concave,
        }
    }

    fn last_token_in_unfinished_line(&self) -> Option<TokenData> {
        if self.token_ranges.last()?.start.line >= self.line {
            self.token_datas.last().copied()
        } else {
            None
        }
    }
}

impl<'lex> std::fmt::Debug for Tokenizer<'lex> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TokenScanner").finish()
    }
}

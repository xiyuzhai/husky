use super::*;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
#[enum_class::from_variants]
pub enum PathNameRegionalToken {
    CrateRootMod(CrateRegionalToken),
    SelfMod(SelfModRegionalToken),
    SuperMod(SuperRegionalToken),
    Ident(IdentRegionalToken),
}

// crate

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct CrateRegionalToken {
    pub(crate) token_idx: RegionalTokenIdx,
}

impl CrateRegionalToken {
    pub fn new(token_idx: RegionalTokenIdx) -> Self {
        Self { token_idx }
    }

    pub fn regional_token_idx(&self) -> RegionalTokenIdx {
        self.token_idx
    }
}

// self mod

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct SelfModRegionalToken {
    token_idx: RegionalTokenIdx,
}

impl SelfModRegionalToken {
    pub fn regional_token_idx(&self) -> RegionalTokenIdx {
        self.token_idx
    }
}

/// `super` super token
#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct SuperRegionalToken {
    token_idx: RegionalTokenIdx,
}

impl SuperRegionalToken {
    pub fn regional_token_idx(&self) -> RegionalTokenIdx {
        self.token_idx
    }
}

impl<'a, Context> parsec::TryParseOptionFromStream<Context> for PathNameRegionalToken
where
    Context: RegionalTokenStreamParser<'a>,
{
    type Error = TokenDataError;

    fn try_parse_option_from_stream_without_guaranteed_rollback(
        ctx: &mut Context,
    ) -> Result<Option<Self>, Self::Error> {
        if let Some((regional_token_idx, token)) = ctx.token_stream_mut().next_indexed() {
            match token {
                TokenData::Ident(ident) => {
                    Ok(Some(PathNameRegionalToken::Ident(IdentRegionalToken {
                        ident,
                        regional_token_idx,
                    })))
                }
                TokenData::Keyword(Keyword::Pronoun(pronoun)) => match pronoun {
                    PronounKeyword::Crate => Ok(Some(PathNameRegionalToken::CrateRootMod(
                        CrateRegionalToken {
                            token_idx: regional_token_idx,
                        },
                    ))),
                    PronounKeyword::SelfType => Ok(None),
                    PronounKeyword::SelfValue => {
                        Ok(Some(PathNameRegionalToken::SelfMod(SelfModRegionalToken {
                            token_idx: regional_token_idx,
                        })))
                    }
                    PronounKeyword::Super => {
                        Ok(Some(PathNameRegionalToken::SuperMod(SuperRegionalToken {
                            token_idx: regional_token_idx,
                        })))
                    }
                },
                TokenData::Error(error) => Err(error),
                TokenData::Label(_)
                | TokenData::Punctuation(_)
                | TokenData::WordOpr(_)
                | TokenData::Literal(_)
                | TokenData::Keyword(_) => Ok(None),
            }
        } else {
            Ok(None)
        }
    }
}

impl PathNameRegionalToken {
    pub fn regional_token_idx(self) -> RegionalTokenIdx {
        match self {
            PathNameRegionalToken::Ident(token) => token.regional_token_idx(),
            PathNameRegionalToken::CrateRootMod(token) => token.regional_token_idx(),
            PathNameRegionalToken::SelfMod(token) => token.regional_token_idx(),
            PathNameRegionalToken::SuperMod(token) => token.regional_token_idx(),
        }
    }

    pub fn ident_regional_token(self) -> Option<IdentRegionalToken> {
        match self {
            PathNameRegionalToken::Ident(ident_token) => Some(ident_token),
            PathNameRegionalToken::CrateRootMod(_)
            | PathNameRegionalToken::SelfMod(_)
            | PathNameRegionalToken::SuperMod(_) => None,
        }
    }
    pub fn ident(self) -> Option<Ident> {
        match self {
            PathNameRegionalToken::Ident(ident_token) => Some(ident_token.ident()),
            PathNameRegionalToken::CrateRootMod(_)
            | PathNameRegionalToken::SelfMod(_)
            | PathNameRegionalToken::SuperMod(_) => None,
        }
    }
}

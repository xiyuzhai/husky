use super::*;
use husky_token::*;
use original_error::OriginalError;
use parsec::{IsStreamParser, StreamWrapper, TryParseOptionFromStream};
use thiserror::Error;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub struct ParentUseExprData {
    pub parent_name_token: PathNameToken,
    pub colon_colon_token: UseExprResult<ColonColonToken>,
    pub children: UseExprResult<UseExprChildren>,
}

/// use tree expr is top-down
/// because path is resolved top-down
#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum UseExpr {
    All { star_token: StarToken },
    IdentLeaf { ident_token: IdentToken },
    SelfLeaf { self_mod_token: SelfModToken },
    Parent(ParentUseExprData),
    Err(UseExprError),
}

impl From<UseExprResult<UseExpr>> for UseExpr {
    fn from(value: UseExprResult<UseExpr>) -> Self {
        match value {
            Ok(value) => value,
            Err(e) => UseExpr::Err(e),
        }
    }
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq)]
pub enum UseExprChildren {
    Single {
        child: UseExprIdx,
    },
    Multiple {
        lcurl_token: InlineLcurlToken,
        children: UseExprIdxRange,
        comma_tokens: Vec<CommaToken>,
        rcurl_token: UseExprResult<InlineRcurlToken>,
    },
}
impl UseExprChildren {
    pub(crate) fn idx_range(&self) -> UseExprIdxRange {
        match self {
            UseExprChildren::Single { child } => UseExprIdxRange::new_single(*child),
            UseExprChildren::Multiple {
                lcurl_token: _,
                children,
                comma_tokens: _,
                rcurl_token: _,
            } => *children,
        }
    }
}

pub type UseExprArena = Arena<UseExpr>;
pub type UseExprIdx = ArenaIdx<UseExpr>;
pub type UseExprIdxRange = ArenaIdxRange<UseExpr>;

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct UseExprRoot {
    use_token: UseToken,
    parent_use_expr_idx: ParentUseExprIdx,
}

#[salsa::derive_debug_with_db]
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct ParentUseExprIdx(UseExprIdx);

impl ParentUseExprIdx {
    pub fn use_expr_idx(self) -> UseExprIdx {
        self.0
    }

    pub(crate) fn data(self, arena: &UseExprArena) -> &ParentUseExprData {
        match arena[self.0] {
            UseExpr::Parent(ref expr) => expr,
            _ => unreachable!(),
        }
    }
}

impl From<ParentUseExprIdx> for UseExprIdx {
    fn from(value: ParentUseExprIdx) -> Self {
        value.0
    }
}

impl UseExprRoot {
    pub fn use_token(&self) -> UseToken {
        self.use_token
    }

    pub fn parent_use_expr_idx(&self) -> ParentUseExprIdx {
        self.parent_use_expr_idx
    }
}

pub(crate) fn parse_use_expr_root(
    token_stream: &mut TokenStream,
    use_expr_arena: &mut UseExprArena,
) -> Result<UseExprRoot, ()> {
    UseExprParser::new(token_stream, use_expr_arena)
        .parse_use_expr_root()
        .map_err(|e| {
            // alloc into an use expression, so that the error can be access later for diagnostics
            use_expr_arena.alloc_one(UseExpr::Err(e));
        })
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Error, PartialEq, Eq)]
pub enum UseExprError {
    #[error("{0}")]
    Original(#[from] OriginalUseExprError),
    #[error("{0}")]
    Derived(#[from] DerivedUseExprError),
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Error, PartialEq, Eq)]
pub enum OriginalUseExprError {
    #[error("expect identifier")]
    ExpectIdent(TokenStreamState),
    #[error("expect use expr")]
    ExpectUseExpr(TokenStreamState),
    #[error("expect `::`")]
    ExpectScopeResolution(TokenStreamState),
    #[error("expect `}}`")]
    ExpectRightCurlyBrace(TokenStreamState),
    #[error("expect `use` token")]
    ExpectUseToken(TokenStreamState),
    #[error("invalid `*` as use root")]
    InvalidAllAsRoot {
        use_token: UseToken,
        star_token: StarToken,
    },
    #[error("invalid ident as use root")]
    InvalidLeafAsRoot {
        use_token: UseToken,
        ident_token: IdentToken,
    },
    #[error("invalid `self` as use root")]
    InvalidSelfAsRoot {
        use_token: UseToken,
        self_mod_token: SelfModToken,
    },
    #[error("CannotUseCrateForChild")]
    CannotUseCrateForChild { crate_token: CrateToken },
}

impl OriginalError for OriginalUseExprError {
    type Error = UseExprError;
}

#[salsa::derive_debug_with_db]
#[derive(Debug, Error, PartialEq, Eq)]
pub enum DerivedUseExprError {
    #[error("token error")]
    TokenData(#[from] TokenDataError),
}

impl From<TokenDataError> for UseExprError {
    fn from(value: TokenDataError) -> Self {
        UseExprError::Derived(value.into())
    }
}

pub type UseExprResult<T> = Result<T, UseExprError>;

pub(crate) struct UseExprParser<'a, 'b> {
    token_stream: &'b mut TokenStream<'a>,
    use_expr_arena: &'b mut UseExprArena,
}

impl<'a, 'b> UseExprParser<'a, 'b> {
    pub(crate) fn new(
        token_stream: &'b mut TokenStream<'a>,
        use_expr_arena: &'b mut UseExprArena,
    ) -> Self {
        Self {
            token_stream,
            use_expr_arena,
        }
    }
}

impl<'a, 'b> std::ops::Deref for UseExprParser<'a, 'b> {
    type Target = TokenStream<'a>;

    fn deref(&self) -> &Self::Target {
        &self.token_stream
    }
}

impl<'a, 'b> std::ops::DerefMut for UseExprParser<'a, 'b> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.token_stream
    }
}

impl<'a, 'b> std::borrow::Borrow<TokenStream<'a>> for UseExprParser<'a, 'b> {
    fn borrow(&self) -> &TokenStream<'a> {
        &self.token_stream
    }
}

impl<'a, 'b> std::borrow::BorrowMut<TokenStream<'a>> for UseExprParser<'a, 'b> {
    fn borrow_mut(&mut self) -> &mut TokenStream<'a> {
        &mut self.token_stream
    }
}

impl<'a, 'b> StreamWrapper for UseExprParser<'a, 'b> {}

impl<'a, 'b> UseExprParser<'a, 'b> {
    pub(crate) fn parse_use_expr_root(&mut self) -> UseExprResult<UseExprRoot> {
        let use_token: UseToken = self.try_parse_expected(OriginalUseExprError::ExpectUseToken)?;
        let use_expr = self.try_parse_expected(OriginalUseExprError::ExpectUseExpr)?;
        match use_expr {
            UseExpr::All { star_token } => Err(OriginalUseExprError::InvalidAllAsRoot {
                use_token,
                star_token,
            }
            .into()),
            UseExpr::IdentLeaf { ident_token } => Err(OriginalUseExprError::InvalidLeafAsRoot {
                use_token,
                ident_token,
            }
            .into()),
            UseExpr::SelfLeaf { self_mod_token } => Err(OriginalUseExprError::InvalidSelfAsRoot {
                use_token,
                self_mod_token,
            }
            .into()),
            UseExpr::Parent(_) => Ok(UseExprRoot {
                use_token,
                parent_use_expr_idx: ParentUseExprIdx(self.use_expr_arena.alloc_one(use_expr)),
            }),
            UseExpr::Err(e) => Err(e),
        }
    }

    fn parse_use_expr_after_ident(&mut self, ident_token: IdentToken) -> UseExprResult<UseExpr> {
        let Some(colon_colon_token) = self.try_parse_option::<ColonColonToken>()? else {
            return Ok(UseExpr::IdentLeaf { ident_token });
        };
        Ok(UseExpr::Parent(ParentUseExprData {
            parent_name_token: PathNameToken::Ident(ident_token),
            colon_colon_token: Ok(colon_colon_token),
            children: self.parse_children(),
        }))
    }

    fn parse_children(&mut self) -> UseExprResult<UseExprChildren> {
        let Some(lcurl_token) = self.try_parse_option::<InlineLcurlToken>()? else {
            let child = self
                .try_parse_expected(OriginalUseExprError::ExpectUseExpr)
                .into();
            match child {
                UseExpr::Parent(ParentUseExprData {
                    parent_name_token: PathNameToken::CrateRoot(crate_token),
                    ..
                }) => Err(OriginalUseExprError::CannotUseCrateForChild { crate_token })?,
                _ => (),
            }
            let child = self.use_expr_arena.alloc_one(child);
            return Ok(UseExprChildren::Single { child });
        };
        let (children, comma_tokens) = parsec::parse_punctuated_list(self)?;
        let children = self.use_expr_arena.alloc_many(children);
        Ok(UseExprChildren::Multiple {
            lcurl_token,
            children,
            comma_tokens,
            rcurl_token: self.try_parse_expected(OriginalUseExprError::ExpectRightCurlyBrace),
        })
    }
}

impl<'a, 'b> TryParseOptionFromStream<UseExprParser<'a, 'b>> for UseExpr {
    type Error = UseExprError;
    fn try_parse_option_from_stream_without_guaranteed_rollback(
        ctx: &mut UseExprParser<'a, 'b>,
    ) -> UseExprResult<Option<Self>> {
        if let Some(star_token) = ctx.try_parse_option::<StarToken>()? {
            return Ok(Some(UseExpr::All { star_token }));
        }
        let Some(path_name_token) = ctx.try_parse_option::<PathNameToken>()? else {
            return Ok(None);
        };
        match path_name_token {
            PathNameToken::Ident(ident_token) => {
                Ok(Some(ctx.parse_use_expr_after_ident(ident_token)?))
            }
            PathNameToken::CrateRoot(crate_token) => Ok(Some(UseExpr::Parent(ParentUseExprData {
                parent_name_token: PathNameToken::CrateRoot(crate_token),
                colon_colon_token: ctx
                    .try_parse_expected(OriginalUseExprError::ExpectScopeResolution),
                children: ctx.parse_children(),
            }))),
            PathNameToken::SelfMod(self_mod_token) => {
                // differentiate betwee self one and self children
                if ctx.peek() == Some(&TokenData::Punctuation(Punctuation::COLON_COLON)) {
                    Ok(Some(UseExpr::Parent(ParentUseExprData {
                        parent_name_token: self_mod_token.into(),
                        colon_colon_token: Ok(ctx
                            .try_parse_option()
                            .expect("guaranteed by peek")
                            .expect("guaranteed by peek")),
                        children: ctx.parse_children(),
                    })))
                } else {
                    Ok(Some(UseExpr::SelfLeaf { self_mod_token }))
                }
            }
            PathNameToken::Super(super_token) => Ok(Some(UseExpr::Parent(ParentUseExprData {
                parent_name_token: PathNameToken::Super(super_token),
                colon_colon_token: ctx
                    .try_parse_expected(OriginalUseExprError::ExpectScopeResolution),
                children: ctx.parse_children(),
            }))),
        }
    }
}
